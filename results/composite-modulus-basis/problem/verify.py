#!/usr/bin/env python3
"""Rebuild and independently verify the complete problem package."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import random
import shlex
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parent
RESULT_ROOT = ROOT.parent
DATA = ROOT / "data"
BUILD = RESULT_ROOT / "build" / "problem"


def run(command: list[str], *, input_data: bytes | None = None,
        timeout: float = 120, capture: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(
        command,
        input=input_data,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.PIPE if capture else None,
        check=True,
        timeout=timeout,
    )


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(1 << 20):
            result.update(block)
    return result.hexdigest()


def compile_program(source: Path, output: Path, sanitize: bool = False) -> None:
    flags = ["-std=c++17", "-Wall", "-Wextra", "-Wpedantic"]
    if sanitize:
        flags += ["-O1", "-g", "-fsanitize=undefined", "-fno-sanitize-recover=all"]
    else:
        flags += ["-O2", "-DNDEBUG"]
    compiler = shlex.split(os.environ.get("CXX", "c++"))
    if not compiler:
        raise ValueError("CXX must name a compiler")
    run([*compiler, *flags, str(source), "-o", str(output)], capture=True)


def load_validator():
    spec = importlib.util.spec_from_file_location("range_module_validator", ROOT / "validator.py")
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def normalized_tokens(data: bytes) -> list[bytes]:
    return data.split()


def check_regeneration() -> None:
    with tempfile.TemporaryDirectory(prefix="range-module-data-") as directory:
        regenerated = Path(directory)
        run(["python3", str(ROOT / "gen.py"), "--output", str(regenerated)], timeout=300)
        expected_files = sorted(path.name for path in DATA.iterdir() if path.is_file())
        actual_files = sorted(path.name for path in regenerated.iterdir() if path.is_file())
        if expected_files != actual_files:
            raise AssertionError(
                f"regenerated file set differs: expected={expected_files}, actual={actual_files}")
        for name in expected_files:
            if (DATA / name).read_bytes() != (regenerated / name).read_bytes():
                raise AssertionError(f"committed data/{name} is not reproducible")


def check_official(std: Path, quick: bool) -> tuple[int, float]:
    manifest = json.loads((DATA / "manifest.json").read_text(encoding="utf-8"))
    validator = load_validator()
    cases = manifest["cases"][:5] if quick else manifest["cases"]
    slowest = 0.0
    total_queries = 0
    for item in cases:
        case_id = item["case_id"]
        input_path = DATA / f"{case_id}.in"
        answer_path = DATA / f"{case_id}.ans"
        if digest(input_path) != item["input_sha256"]:
            raise AssertionError(f"input hash mismatch for case {case_id}")
        if digest(answer_path) != item["answer_sha256"]:
            raise AssertionError(f"answer hash mismatch for case {case_id}")
        summary = validator.validate(input_path, item["subtask"])
        if summary["q"] != item["q"] or summary["m"] != item["modulus"]:
            raise AssertionError(f"manifest mismatch for case {case_id}")
        expected = answer_path.read_bytes()
        expected_tokens = normalized_tokens(expected)
        if len(expected_tokens) != item["q"]:
            raise AssertionError(f"wrong answer-token count for case {case_id}")
        if expected_tokens.count(b"YES") != item["yes"] or expected_tokens.count(b"NO") != item["no"]:
            raise AssertionError(f"answer statistics mismatch for case {case_id}")
        started = time.perf_counter()
        completed = run([str(std)], input_data=input_path.read_bytes(), timeout=120)
        elapsed = time.perf_counter() - started
        slowest = max(slowest, elapsed)
        if normalized_tokens(completed.stdout) != expected_tokens:
            raise AssertionError(f"std.cpp disagrees with the independent oracle on case {case_id}")
        total_queries += item["q"]
    return total_queries, slowest


def check_small_official(brute: Path, quick: bool) -> int:
    case_ids = ("01",) if quick else ("01", "02")
    checked = 0
    for case_id in case_ids:
        input_data = (DATA / f"{case_id}.in").read_bytes()
        expected = (DATA / f"{case_id}.ans").read_bytes()
        actual = run([str(brute)], input_data=input_data, timeout=30).stdout
        if normalized_tokens(actual) != normalized_tokens(expected):
            raise AssertionError(f"brute.cpp disagrees on official case {case_id}")
        checked += len(normalized_tokens(expected))
    return checked


def random_instance(rng: random.Random) -> bytes:
    modulus = rng.choice((2, 3, 4, 5, 6, 7, 8, 9, 10, 12))
    dimension = rng.randint(1, 3)
    while modulus**dimension > 20_000:
        dimension -= 1
    n = rng.randint(1, 7)
    query_count = rng.randint(4, 12)
    rows = [[rng.randrange(modulus) for _ in range(dimension)] for _ in range(n)]
    lines = [f"{n} {dimension} {modulus} {query_count}"]
    lines += [" ".join(map(str, row)) for row in rows]
    for _ in range(query_count):
        left = rng.randint(1, n)
        right = rng.randint(left, n)
        target = [rng.randrange(modulus) for _ in range(dimension)]
        lines.append(f"{left} {right} " + " ".join(map(str, target)))
    return ("\n".join(lines) + "\n").encode("ascii")


def differential_fuzz(std: Path, brute: Path, rounds: int) -> int:
    rng = random.Random(20260921)
    queries = 0
    for round_index in range(rounds):
        instance = random_instance(rng)
        expected = run([str(brute)], input_data=instance, timeout=10).stdout
        actual = run([str(std)], input_data=instance, timeout=10).stdout
        if normalized_tokens(actual) != normalized_tokens(expected):
            failure = BUILD / f"fuzz-failure-{round_index}.in"
            failure.write_bytes(instance)
            raise AssertionError(f"differential fuzz failed; saved {failure}")
        queries += len(normalized_tokens(expected))
    return queries


def check_packaged_solutions() -> int:
    variants = (
        ("timestamp-basic", "solutions/timestamp-basic.cpp", "02"),
        ("timestamp-fast", "solutions/timestamp-fast.cpp", "02"),
        ("closure-prototype", "solutions/closure-prototype.cpp", "02"),
        ("howell-rebuild", "solutions/howell-rebuild.cpp", "02"),
        ("howell-segment", "solutions/howell-segment.cpp", "02"),
        ("howell-sparse", "solutions/howell-sparse.cpp", "02"),
        ("dimension-one-gcd", "solutions/dimension-one-gcd.cpp", "04"),
        ("field-timestamp", "solutions/field-timestamp.cpp", "06"),
        ("prefix-howell", "solutions/prefix-howell.cpp", "11"),
    )
    checked = 0
    for name, source, case_id in variants:
        binary = BUILD / f"variant-{name}"
        compile_program(ROOT / source, binary)
        actual = run([str(binary)], input_data=(DATA / f"{case_id}.in").read_bytes(),
                     timeout=30).stdout
        expected = (DATA / f"{case_id}.ans").read_bytes()
        if normalized_tokens(actual) != normalized_tokens(expected):
            raise AssertionError(f"packaged solution {name} disagrees on case {case_id}")
        checked += 1

    xor_binary = BUILD / "variant-xor-packed"
    compile_program(ROOT / "solutions/xor-packed.cpp", xor_binary)
    xor_input = b"""3 3 2 3
1 0 0
0 1 0
1 1 0
1 2 1 1 0
2 2 1 0 0
1 3 0 0 1
"""
    xor_expected = [b"YES", b"NO", b"NO"]
    if normalized_tokens(run([str(xor_binary)], input_data=xor_input).stdout) != xor_expected:
        raise AssertionError("packaged solution xor-packed failed its smoke test")
    return checked + 1


def known_regressions(std: Path) -> None:
    instance = b"""3 2 4 5
2 1
1 0
2 0
1 1 0 2
1 1 1 0
2 3 1 0
3 3 1 0
1 3 3 1
"""
    expected = [b"YES", b"NO", b"YES", b"NO", b"YES"]
    actual = normalized_tokens(run([str(std)], input_data=instance).stdout)
    if actual != expected:
        raise AssertionError(f"known p-adic/timestamp regression failed: {actual}")

    deep_instance = b"""1 1 8 3
4
1 1 4
1 1 2
1 1 0
"""
    deep_expected = [b"YES", b"NO", b"YES"]
    deep_actual = normalized_tokens(run([str(std)], input_data=deep_instance).stdout)
    if deep_actual != deep_expected:
        raise AssertionError(f"known higher-valuation regression failed: {deep_actual}")

    crt_instance = b"""2 1 6 1
2
3
1 2 1
"""
    crt_actual = normalized_tokens(run([str(std)], input_data=crt_instance).stdout)
    if crt_actual != [b"YES"]:
        raise AssertionError(f"known CRT regression failed: {crt_actual}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true",
                        help="check only the first five official cases and 20 fuzz rounds")
    parser.add_argument("--sanitize", action="store_true",
                        help="compile the reference solution with UBSan")
    parser.add_argument("--skip-regeneration", action="store_true")
    args = parser.parse_args()

    BUILD.mkdir(parents=True, exist_ok=True)
    std = BUILD / ("std-ubsan" if args.sanitize else "std")
    brute = BUILD / "brute"
    compile_program(ROOT / "std.cpp", std, args.sanitize)
    compile_program(ROOT / "brute.cpp", brute)
    if not args.skip_regeneration:
        check_regeneration()
    known_regressions(std)
    official_queries, slowest = check_official(std, args.quick)
    brute_queries = check_small_official(brute, args.quick)
    fuzz_queries = differential_fuzz(std, brute, 20 if args.quick else 100)
    variants = 0 if args.sanitize else check_packaged_solutions()
    print(
        f"OK: {official_queries} official queries, {brute_queries} official brute checks, "
        f"{fuzz_queries} randomized brute checks, {variants} packaged solution checks; "
        f"slowest std case {slowest:.3f}s"
    )


if __name__ == "__main__":
    main()
