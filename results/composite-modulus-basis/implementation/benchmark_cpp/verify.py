"""Independent correctness gate for all C++ candidates (Python standard library)."""

import argparse
from itertools import product
import json
import math
from pathlib import Path
import random
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from solver import solve_offline
from tests.oracles import LatticeOracle

ALGORITHMS = (
    "timestamp-basic", "timestamp-fast", "closure-prototype", "howell-rebuild",
    "howell-segment", "howell-sparse", "field-timestamp", "xor-packed",
)


def applicable(name, factors, dimension):
    modulus = math.prod(p**k for p, k in factors)
    if name == "xor-packed":
        return modulus == 2 and dimension <= 64
    if name == "field-timestamp":
        return len(factors) == 1 and factors[0][1] == 1
    return True


def command(binary, name, factors):
    result = [str(binary), "--algorithm", name]
    # Exercise the independent baselines WITHOUT supplying a factorization.
    if not name.startswith("howell-") and name != "xor-packed":
        result.extend(["--factors", ",".join(f"{p}:{k}" for p, k in factors)])
    return result


def encode(rows, modulus, queries):
    lines = [f"{len(rows)} {len(rows[0])} {modulus} {len(queries)}"]
    lines.extend(" ".join(map(str, row)) for row in rows)
    lines.extend(f"{left} {right} " + " ".join(map(str, row)) for left, right, row in queries)
    return ("\n".join(lines) + "\n").encode()


def check(binary, label, factors, rows, queries, expected, algorithms=ALGORITHMS):
    modulus = math.prod(p**k for p, k in factors)
    data = encode(rows, modulus, queries)
    correct = b"".join(b"YES\n" if answer else b"NO\n" for answer in expected)
    tested, assertions = [], 0
    metadata = {}
    for name in algorithms:
        if not applicable(name, factors, len(rows[0])):
            continue
        result = subprocess.run(command(binary, name, factors), input=data, capture_output=True, timeout=120)
        if result.returncode or result.stdout != correct:
            failure = HERE.parent.parent / "build/cpp-benchmark/failure.in"
            failure.parent.mkdir(parents=True, exist_ok=True)
            failure.write_bytes(data)
            actual = result.stdout.splitlines()
            mismatch = next((i for i, (a, b) in enumerate(zip(actual, correct.splitlines())) if a != b), None)
            raise AssertionError(f"{label}: {name}; exit={result.returncode}; mismatch={mismatch}; "
                                 f"stderr={result.stderr.decode()[:2000]}; input={failure}")
        metrics = json.loads(result.stderr)
        if metrics["queries"] != len(expected) or metrics["yes"] != sum(expected):
            raise AssertionError(f"invalid metrics: {label}/{name}")
        metadata[name] = metrics
        tested.append(name)
        assertions += len(expected)
    if "timestamp-basic" in metadata and "timestamp-fast" in metadata:
        for counter in ("visits", "reductions", "writes", "pops", "max_pending"):
            if metadata["timestamp-basic"][counter] != metadata["timestamp-fast"][counter]:
                raise AssertionError(f"different task trace counts: {label}/{counter}")
        metrics = metadata["timestamp-fast"]
        n, d, total_k = len(rows), len(rows[0]), sum(k for _, k in factors)
        if metrics["visits"] > n * d * total_k or metrics["pops"] > n * total_k * (d + 1):
            raise AssertionError(f"operation bound exceeded: {label}")
        if metrics["max_pending"] > max(k for _, k in factors):
            raise AssertionError(f"queue bound exceeded: {label}")
    print(f"PASS {label}: {len(queries)} queries, {len(tested)} algorithms", flush=True)
    return {"label": label, "queries": len(queries), "algorithms": tested, "assertions": assertions}


def enumerate_span(rows, modulus, dimension):
    span = {(0,) * dimension}
    for row in rows:
        span = {tuple((a + coefficient * b) % modulus for a, b in zip(x, row))
                for x in span for coefficient in range(modulus)}
    return span


def exhaustive_case(binary, factors, dimension, length):
    modulus = math.prod(p**k for p, k in factors)
    universe = list(product(range(modulus), repeat=dimension))
    rows, queries, expected = [], [], []
    for sequence in product(universe, repeat=length):
        offset = len(rows)
        rows.extend(sequence)
        for right in range(1, length + 1):
            for left in range(1, right + 1):
                span = enumerate_span(sequence[left - 1:right], modulus, dimension)
                for target in universe:
                    queries.append((offset + left, offset + right, target))
                    expected.append(target in span)
    return check(binary, f"exhaustive-m{modulus}-d{dimension}-length{length}",
                 factors, rows, queries, expected)


def verify(binary, quick=False):
    rng = random.Random(20260917)
    results = []
    if not quick:
        for factors, d, length in [(((2, 2),), 2, 3), (((2, 1),), 3, 3), (((2, 3),), 1, 3), (((3, 1),), 2, 2)]:
            results.append(exhaustive_case(binary, factors, d, length))
    factor_sets = [((2, 1),), ((2, 2),), ((2, 8),), ((2, 31),), ((3, 10),),
                   ((2, 3), (3, 2)), ((998244353, 1),), ((4294967291, 1),),
                   ((3, 1), (5, 1), (17, 1), (257, 1), (65537, 1)),
                   ((65521, 2),)]
    for case_index in range(20 if quick else 60):
        factors = factor_sets[case_index % len(factor_sets)]
        modulus = math.prod(p**k for p, k in factors)
        d, n = rng.randint(1, 8), rng.randint(5, 20)
        rows = [[rng.randrange(modulus) for _ in range(d)] for _ in range(n)]
        for i in range(n):
            if case_index % 4 == 1:
                rows[i] = [x * factors[0][0] % modulus for x in rows[i]]
            elif case_index % 4 == 2 and d > 1:
                rows[i][-1] = sum(rows[i][:-1]) % modulus
            if i % 7 == 0:
                rows[i] = [0] * d
            elif i % 7 == 1 and i > 1:
                rows[i] = rows[i - 1][:]
        queries = []
        for q in range(60):
            left = rng.randint(1, n)
            right = rng.randint(left, n)
            target = [rng.randrange(modulus) for _ in range(d)]
            if q % 2:
                target = [0] * d
                for row in rows[left - 1:right]:
                    coefficient = rng.randrange(modulus)
                    target = [(a + coefficient * b) % modulus for a, b in zip(target, row)]
            queries.append((left, right, target))
        expected = [LatticeOracle(rows[l - 1:r], modulus, d).contains(x) for l, r, x in queries]
        python_answers = solve_offline(rows, modulus, queries, factors=factors)
        if python_answers != expected:
            raise AssertionError("Python reference disagrees with lattice oracle")
        # Signed, noncanonical representatives test the shared input contract.
        if case_index % 3 == 0:
            rows = [[x - 2 * modulus for x in row] for row in rows]
            queries = [(l, r, [x + 3 * modulus for x in target]) for l, r, target in queries]
        results.append(check(binary, f"lattice-{case_index}-m{modulus}-d{d}", factors, rows, queries, expected))
    # Word packing at the top bit and empty query batches need explicit checks.
    rows = [[int(j == i) for j in range(64)] for i in range(64)]
    queries = [(1, 64, [1] * 64), (1, 63, rows[63]), (64, 64, rows[63])]
    results.append(check(binary, "xor-top-bit", ((2, 1),), rows, queries, [True, False, True]))
    results.append(check(binary, "empty-query-batch", ((2, 2),), [[2, 1]], [], []))
    boundary_rows = [[-(2**63), 2**63 - 1], [2**63 - 1, -(2**63)]]
    boundary_queries = [(1, 1, boundary_rows[0]), (2, 2, boundary_rows[0]),
                        (1, 2, [-(2**63), -(2**63)]), (1, 2, [0, 0])]
    boundary_modulus = 4294967291
    boundary_expected = [LatticeOracle(boundary_rows[l - 1:r], boundary_modulus, 2).contains(x)
                         for l, r, x in boundary_queries]
    results.append(check(binary, "signed-input-boundaries", ((boundary_modulus, 1),),
                         boundary_rows, boundary_queries, boundary_expected))
    return {"seed": 20260917, "quick": quick, "cases": results,
            "membership_assertions": sum(x["assertions"] for x in results), "status": "passed"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify(args.binary.resolve(), args.quick)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS {result['membership_assertions']} independent C++ membership assertions", flush=True)


if __name__ == "__main__":
    main()
