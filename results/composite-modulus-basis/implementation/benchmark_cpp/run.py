"""Compile, independently validate, then serially benchmark C++ interval solvers."""

import argparse
from datetime import datetime, timezone
from dataclasses import replace
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import shlex
import statistics
import subprocess
import sys
import time

from datasets import cases, file_hash, generate
from verify import ALGORITHMS, applicable, command

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def capture(args):
    result = subprocess.run(args, capture_output=True, text=True, check=True, timeout=30)
    return result.stdout.strip()


def environment():
    info = {"system": platform.system(), "release": platform.release(), "machine": platform.machine(),
            "python": platform.python_version(), "logical_cpus": os.cpu_count(),
            "load_average_at_start": os.getloadavg() if hasattr(os, "getloadavg") else None}
    if platform.system() == "Darwin":
        try:
            info["cpu"] = capture(["sysctl", "-n", "machdep.cpu.brand_string"])
            info["memory_bytes"] = int(capture(["sysctl", "-n", "hw.memsize"]))
        except subprocess.CalledProcessError:
            info["hardware_metadata_status"] = "unavailable: host permission restriction"
    elif Path("/proc/cpuinfo").exists():
        info["cpu"] = next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
                            if line.startswith("model name")), platform.processor())
    return info


def validate_answers(path, manifest):
    probes = {p["query_index"]: p["expected"] for p in manifest["oracle_probes"]}
    yes, count = 0, 0
    for i, line in enumerate(path.open("rb")):
        if line not in (b"YES\n", b"NO\n"):
            raise AssertionError(f"invalid answer at {i}")
        answer = line == b"YES\n"
        if i % 2 == 1 and not answer:
            raise AssertionError(f"constructed positive rejected at {i}")
        if manifest["guaranteed_no_rule"] and i % 2 == 0 and answer:
            raise AssertionError(f"analytic negative accepted at {i}")
        if i in probes and answer != probes[i]:
            raise AssertionError(f"lattice oracle disagreement at {i}")
        yes += answer
        count += 1
    if count != manifest["q"]:
        raise AssertionError(f"expected {manifest['q']} answers, got {count}")
    return file_hash(path), yes


def sample_rss(pid):
    # Linux reads proc directly; macOS uses the process's current resident set.
    status = Path(f"/proc/{pid}/status")
    try:
        if status.exists():
            for line in status.read_text().splitlines():
                if line.startswith("VmRSS:"):
                    return int(line.split()[1]) * 1024
        output = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)],
                                capture_output=True, text=True, timeout=1)
        return int(output.stdout.strip() or 0) * 1024
    except (OSError, ValueError, subprocess.TimeoutExpired):
        return 0


def run_one(binary, algorithm, case, manifest, input_path, scratch, timeout, memory_mib):
    stdout_path, stderr_path = scratch / "answers.txt", scratch / "stderr.txt"
    args = command(binary, algorithm, case.factors)
    start, max_sampled = time.perf_counter(), 0
    reason = None
    with input_path.open("rb") as stdin, stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        proc = subprocess.Popen(args, stdin=stdin, stdout=stdout, stderr=stderr)
        try:
            while proc.poll() is None:
                elapsed = time.perf_counter() - start
                rss = sample_rss(proc.pid)
                max_sampled = max(max_sampled, rss)
                if elapsed > timeout:
                    reason = "timeout"
                elif rss > memory_mib * 1024 * 1024:
                    reason = "memory_limit"
                if reason:
                    break
                time.sleep(0.1)
        finally:
            # Own the Popen handle: cleanup also covers KeyboardInterrupt/errors,
            # without looking up or terminating unrelated process IDs.
            if proc.poll() is None:
                proc.kill()
            proc.wait()
    elapsed = time.perf_counter() - start
    result = {"status": reason or ("ok" if proc.returncode == 0 else "error"),
              "runner_wall_seconds": elapsed, "sampled_peak_rss_bytes": max_sampled,
              "returncode": proc.returncode}
    if result["status"] != "ok":
        result["stderr"] = stderr_path.read_text()[-4000:]
        return result
    metrics = json.loads(stderr_path.read_text())
    if metrics["peak_rss_bytes"] > memory_mib * 1024 * 1024:
        return {**result, **metrics, "status": "memory_limit"}
    digest, yes = validate_answers(stdout_path, manifest)
    if metrics["yes"] != yes or metrics["queries"] != case.q:
        raise AssertionError("C++ metrics disagree with actual output")
    result.update(metrics)
    result["stdout_sha256"] = digest
    return result


def median(values):
    return statistics.median(values) if values else None


def summarize(runs, repeats):
    measured = [r for r in runs if not r["warmup"]]
    ok = [r for r in measured if r["status"] == "ok"]
    failures = [r for r in runs if r["status"] != "ok"]
    if failures:
        return {"status": failures[-1]["status"], "completed_repeats": len(ok),
                "required_repeats": repeats}
    if len(ok) != repeats:
        return {"status": "incomplete", "completed_repeats": len(ok), "required_repeats": repeats}
    times = [r["solve_seconds"] for r in ok]
    return {"status": "ok", "completed_repeats": len(ok), "required_repeats": repeats,
            "median_solve_seconds": median(times), "min_solve_seconds": min(times),
            "max_solve_seconds": max(times),
            "coefficient_of_variation": statistics.stdev(times) / statistics.mean(times) if len(times) > 1 else 0,
            "median_program_seconds": median([r["program_seconds"] for r in ok]),
            "median_runner_wall_seconds": median([r["runner_wall_seconds"] for r in ok]),
            "peak_rss_bytes": max(r["peak_rss_bytes"] for r in ok), "yes": ok[0]["yes"],
            "stdout_sha256": ok[0]["stdout_sha256"],
            "counters": {key: ok[0][key] for key in ("visits", "reductions", "writes", "pops", "max_pending")}}


def report(data, path):
    lines = ["# C++ interval-membership benchmark", "", f"UTC: {data['created_utc']}", "",
             "All algorithms consume identical input files and emit identical ordered answers on completed runs.",
             "Primary time is the full solve (construction, offline bucketing, queries, allocation and destruction), excluding parsing/output.",
             "This is a static batch workload: offline reordering is allowed. It does not benchmark online historical snapshots.",
             "RSS is whole-process high-water memory, including input and output arrays. One compiler configuration is shared by every algorithm.", "",
             f"- Host: {data['environment'].get('cpu', data['environment']['machine'])}; {data['environment']['system']} {data['environment']['release']}",
             f"- Compiler: `{data['compiler_version'].splitlines()[0]}`",
             f"- Flags: `{' '.join(data['flags'])}`",
             f"- Profile: `{data['profile']}`; seed {data['seed']}; warmups={data['warmups']}; measured repeats={data['repeats']}",
             f"- Per-process wall timeout: {data['timeout_seconds']} s; RSS budget: {data['memory_mib']} MiB (sampled watchdog plus final high-water check)",
             f"- Correctness gate: {data['verification']['membership_assertions']:,} C++ membership assertions; exact arithmetic self-test passed.",
             "- Howell candidates are local saturated-echelon implementations, not a tuned canonical-form library or a fast-matrix-multiplication implementation.",
             "- closure-prototype is an internal historical ablation, not independent published prior art.",
             "- No CPU pinning, frequency locking, or exclusive-machine guarantee; rerun on a quiet machine for publication.",
             "", "[Raw measurements and dataset manifests](results.json)", "",
             "## Results", "",
             "Fast/basic is a matched speed ratio, not a comparison against the fastest competing method. A timeout is not an exact runtime.", "",
             "| Case | n / d / q | m / K / w | Algorithm | Solve median [min, max] s | Program median s | Peak RSS MiB | YES % |",
             "| --- | --- | --- | --- | --- | --- | --- | --- |"]
    if data.get("resume_sessions"):
        index = lines.index("## Results")
        lines[index:index] = [f"Resumed {len(data['resume_sessions'])} time(s): completed cases were preserved; interrupted cases were restarted. Partial runs and resume environments remain in results.json.", ""]
    for item in data["cases"]:
        spec = item["manifest"]
        for name, summary in item["summaries"].items():
            prefix = f"| {spec['name']} | {spec['n']} / {spec['d']} / {spec['q']} | {spec['modulus']} / {spec['K']} / {spec['w']} | {name} |"
            if summary["status"] != "ok":
                lines.append(f"{prefix} {summary['status']} | — | — | — |")
                continue
            lines.append(f"{prefix} {summary['median_solve_seconds']:.6f} [{summary['min_solve_seconds']:.6f}, {summary['max_solve_seconds']:.6f}] | "
                         f"{summary['median_program_seconds']:.6f} | {summary['peak_rss_bytes']/2**20:.1f} | {100*summary['yes']/spec['q']:.1f} |")
    lines += ["", "## Matched implementation comparison", "",
              "| Case | Basic / fast solve ratio | Fast / best completed non-timestamp baseline solve ratio | Notes |",
              "| --- | --- | --- | --- |"]
    for item in data["cases"]:
        summaries = item["summaries"]
        fast, basic = summaries.get("timestamp-fast", {}), summaries.get("timestamp-basic", {})
        if fast.get("status") != "ok":
            continue
        ft = fast["median_solve_seconds"]
        ratio = f"{basic['median_solve_seconds']/ft:.2f}x" if basic.get("status") == "ok" else "—"
        baselines = [(name, s) for name, s in summaries.items() if name not in ("timestamp-fast", "timestamp-basic", "closure-prototype") and s["status"] == "ok"]
        if baselines:
            best_name, best = min(baselines, key=lambda pair: pair[1]["median_solve_seconds"])
            against = f"{ft/best['median_solve_seconds']:.2f}x ({best_name}; <1 means timestamp-fast is faster)"
        else:
            against = "no completed baseline"
        notes = []
        if fast["coefficient_of_variation"] > 0.1:
            notes.append("fast timing CV > 10%")
        if ft < 0.01:
            notes.append("short sample; use a larger workload")
        lines.append(f"| {item['manifest']['name']} | {ratio} | {against} | {'; '.join(notes) or '—'} |")
    lines += ["", "## Reproduction", "", "Run from the result directory:", "", "```sh", data["reproduction_command"], "```", "",
              "Dataset SHA-256, distributions, interval-length histograms, oracle probes, compiler/source fingerprints, shuffled run order, every raw repetition and failures are in results.json.",
              "Every odd-indexed target is a known linear combination; coupled/nonunit distributions additionally force every even-indexed target outside the full generated module.",
              "Eight fixed short-interval probes per performance dataset use the independent integer-lattice oracle; complete outputs are cross-compared across algorithms.",
              "Warmups are excluded. Algorithms run serially, in a deterministic shuffled order each round; after a timeout/memory failure, further repeats of that candidate are not attempted.",
              "A failed or incomplete candidate receives no speedup number. Unsupported field-only methods are reported rather than used on composite moduli.", ""]
    path.write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=("smoke", "standard", "scaling", "stress"), default="standard")
    parser.add_argument("--tuning", choices=("portable", "native", "sanitize", "ubsan"), default="portable")
    parser.add_argument("--algorithms", default=",".join(ALGORITHMS))
    parser.add_argument("--cases", help="comma-separated case names; default all cases in profile")
    parser.add_argument("--seed", type=int, default=20260917)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=10)
    parser.add_argument("--memory-mib", type=int, default=512)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--resume", action="store_true", help="preserve completed cases; restart an interrupted case with matching sources/settings")
    parser.add_argument("--quick-verification", action="store_true", help="omit exhaustive enumeration, keep independent random/boundary oracle checks")
    args = parser.parse_args()
    if args.repeats < 1 or args.warmups < 0 or args.timeout <= 0 or args.memory_mib < 32:
        parser.error("invalid repetition or resource budget")
    algorithms = args.algorithms.split(",")
    if len(set(algorithms)) != len(algorithms) or any(name not in ALGORITHMS for name in algorithms):
        parser.error("unknown or duplicate algorithm")
    selected = [replace(case, seed=args.seed) for case in cases(args.profile)]
    if args.cases:
        names = args.cases.split(",")
        if not set(names).issubset({case.name for case in selected}):
            parser.error("unknown case name for this profile")
        selected = [case for case in selected if case.name in names]
    created = datetime.now(timezone.utc)
    output = (args.output or ROOT / "artifacts/cpp-benchmark" / f"{args.profile}-{args.tuning}-{created:%Y%m%dT%H%M%SZ}").resolve()
    previous = None
    if args.resume:
        if not (output / "results.json").exists():
            parser.error("--resume requires an existing results.json in --output")
        previous = json.loads((output / "results.json").read_text())
        required = {"profile": args.profile, "tuning": args.tuning, "seed": args.seed,
                    "repeats": args.repeats, "warmups": args.warmups,
                    "timeout_seconds": args.timeout, "memory_mib": args.memory_mib}
        if any(previous.get(key) != value for key, value in required.items()):
            parser.error("resume settings differ from the saved run")
        for filename in ("main.cpp", "algorithms.hpp", "arithmetic_test.cpp", "datasets.py", "verify.py"):
            if previous["source_sha256"].get(filename) != file_hash(HERE / filename):
                parser.error(f"cannot resume after changing {filename}")
        old_command = shlex.split(previous["reproduction_command"])
        old_names = old_command[old_command.index("--cases") + 1].split(",") if "--cases" in old_command else [case.name for case in cases(args.profile)]
        old_algorithms = old_command[old_command.index("--algorithms") + 1].split(",")
        if set(old_names) != {case.name for case in selected} or old_algorithms != algorithms:
            parser.error("resume case/algorithm selection differs from the saved run")
        if previous["status"] == "complete":
            print(f"Already complete: {output / 'report.md'}", flush=True)
            return
    elif (output / "results.json").exists():
        parser.error("output already contains results; select a new output directory")
    output.mkdir(parents=True, exist_ok=True)
    build = ROOT / "build/cpp-benchmark" / f"{args.tuning}-{os.getpid()}"
    build.mkdir(parents=True, exist_ok=True)
    compiler = shlex.split(os.environ.get("CXX", "c++"))
    flags = ["-std=c++17", "-Wall", "-Wextra"]
    if args.tuning == "portable":
        flags += ["-O2", "-DNDEBUG"]
    elif args.tuning == "native":
        flags += ["-O3", "-DNDEBUG", "-march=native"]
    elif args.tuning == "sanitize":
        flags += ["-O1", "-g", "-fsanitize=address,undefined", "-fno-omit-frame-pointer"]
    else:
        flags += ["-O1", "-g", "-fsanitize=undefined", "-fno-sanitize-recover=all", "-fno-omit-frame-pointer"]
    for source, name in (("main.cpp", "bench"), ("arithmetic_test.cpp", "arithmetic_test")):
        result = subprocess.run(compiler + flags + [str(HERE / source), "-o", str(build / name)], capture_output=True, text=True)
        (output / f"compile-{name}.txt").write_text(result.stdout + result.stderr)
        result.check_returncode()
    try:
        arithmetic = capture([str(build / "arithmetic_test")])
    except (subprocess.TimeoutExpired, subprocess.CalledProcessError) as error:
        (output / "validation-failure.txt").write_text(f"Arithmetic self-test failed before benchmarking: {error}\n")
        raise
    (output / "arithmetic.txt").write_text(arithmetic + "\n")
    verify_cmd = [sys.executable, str(HERE / "verify.py"), "--binary", str(build / "bench"), "--output", str(output / "verification.json")]
    if args.quick_verification:
        verify_cmd.append("--quick")
    print("Running independent correctness gate...", flush=True)
    with (output / "verification.txt").open("w") as log:
        subprocess.run(verify_cmd, stdout=log, stderr=subprocess.STDOUT, check=True)
    sources = {path.name: file_hash(path) for path in HERE.iterdir() if path.suffix in (".cpp", ".hpp", ".py")}
    reproduction = ["python3", "implementation/benchmark_cpp/run.py", "--profile", args.profile,
                    "--tuning", args.tuning, "--repeats", str(args.repeats), "--warmups", str(args.warmups),
                    "--seed", str(args.seed),
                    "--timeout", str(args.timeout), "--memory-mib", str(args.memory_mib), "--algorithms", args.algorithms]
    if args.cases:
        reproduction += ["--cases", args.cases]
    if args.quick_verification:
        reproduction.append("--quick-verification")
    data = {"schema_version": 1, "created_utc": created.isoformat(), "profile": args.profile,
            "seed": args.seed,
            "tuning": args.tuning, "flags": flags, "compiler_command": compiler,
            "compiler_version": capture(compiler + ["--version"]), "source_sha256": sources,
            "git_revision": capture(["git", "-C", str(ROOT), "rev-parse", "HEAD"]),
            "git_status_at_start": capture(["git", "-C", str(ROOT), "status", "--short"]),
            "environment": environment(), "repeats": args.repeats, "warmups": args.warmups,
            "timeout_seconds": args.timeout, "memory_mib": args.memory_mib,
            "verification": json.loads((output / "verification.json").read_text()),
            "arithmetic_self_test": arithmetic, "reproduction_command": shlex.join(reproduction),
            "cases": [], "status": "running"}

    prior_hashes = {}
    if previous is not None:
        if previous["compiler_version"] != data["compiler_version"] or previous["flags"] != flags:
            parser.error("compiler configuration changed; start a new output directory")
        for key in ("system", "machine", "cpu"):
            if previous["environment"].get(key) != data["environment"].get(key):
                parser.error("hardware environment changed; start a new output directory")
        fresh = data
        data = previous
        completed, interrupted = [], []
        for case in data["cases"]:
            if case.get("all_completed_outputs_agree") and all(
                s["status"] in ("ok", "unsupported", "timeout", "memory_limit") for s in case["summaries"].values()
            ):
                completed.append(case)
            else:
                interrupted.append(case)
        prior_hashes = {case["manifest"]["name"]: case["manifest"]["sha256"] for case in interrupted}
        data.setdefault("interrupted_cases", []).extend(interrupted)
        data["cases"] = completed
        data.setdefault("resume_sessions", []).append({"created_utc": fresh["created_utc"],
            "environment": fresh["environment"], "source_sha256": sources,
            "restarted_cases": list(prior_hashes), "completed_cases_preserved": len(completed)})
        data["status"] = "running"
        completed_names = {case["manifest"]["name"] for case in completed}
        selected = [case for case in selected if case.name not in completed_names]
        print(f"Resuming: {len(completed)} completed cases preserved; {len(selected)} cases remain", flush=True)

    def save():
        temporary = output / "results.json.tmp"
        temporary.write_text(json.dumps(data, indent=2) + "\n")
        temporary.replace(output / "results.json")
        report(data, output / "report.md")

    save()
    for case in selected:
        print(f"Generating {case.name}: n={case.n}, d={case.d}, q={case.q}...", flush=True)
        input_path = build / f"{case.name}.in"
        manifest = generate(case, input_path)
        if case.name in prior_hashes and manifest["sha256"] != prior_hashes[case.name]:
            raise AssertionError("regenerated input differs from the interrupted case")
        item = {"manifest": manifest, "runs": {name: [] for name in algorithms}, "summaries": {}, "run_order": []}
        data["cases"].append(item)
        active = [name for name in algorithms if applicable(name, case.factors, case.d)]
        for name in algorithms:
            if name not in active:
                item["summaries"][name] = {"status": "unsupported"}
        expected_hash = None
        order_rng = random.Random(case.seed + 2)
        for iteration in range(args.warmups + args.repeats):
            order = active[:]
            order_rng.shuffle(order)
            item["run_order"].append(order)
            for name in order:
                run = run_one(build / "bench", name, case, manifest, input_path, build, args.timeout, args.memory_mib)
                run["warmup"] = iteration < args.warmups
                run["iteration"] = iteration
                if run["status"] == "ok":
                    if expected_hash is None:
                        expected_hash = run["stdout_sha256"]
                    elif run["stdout_sha256"] != expected_hash:
                        run["status"] = "answer_mismatch"
                item["runs"][name].append(run)
                item["summaries"][name] = summarize(item["runs"][name], args.repeats)
                print(f"  {name} {'warmup' if run['warmup'] else iteration - args.warmups + 1}: "
                      f"{run['status']}" + (f" {run['solve_seconds']:.4f}s" if "solve_seconds" in run else ""), flush=True)
                save()
                if run["status"] in ("error", "answer_mismatch"):
                    raise RuntimeError(f"benchmark correctness/execution failure: {case.name}/{name}; see {output}")
                if run["status"] != "ok":
                    active.remove(name)
        # Check the optimized implementation preserves the ordinary task counts.
        a, b = item["summaries"].get("timestamp-basic", {}), item["summaries"].get("timestamp-fast", {})
        if a.get("status") == b.get("status") == "ok" and a["counters"] != b["counters"]:
            raise AssertionError(f"task-count mismatch in {case.name}")
        item["all_completed_outputs_agree"] = True
        input_path.unlink()
        save()
    data["status"] = "complete"
    data["environment"]["load_average_at_end"] = os.getloadavg() if hasattr(os, "getloadavg") else None
    save()
    print(f"Report: {output / 'report.md'}", flush=True)


if __name__ == "__main__":
    main()
