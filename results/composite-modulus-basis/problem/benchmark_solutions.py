#!/usr/bin/env python3
"""Judge and compare every packaged solution on the official data."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
RESULT_ROOT = ROOT.parent
DATA = ROOT / "data"
BUILD = RESULT_ROOT / "build" / "problem-comparison"
ARTIFACTS = ROOT / "artifacts"


@dataclass(frozen=True)
class Solution:
    name: str
    source: str
    scope: tuple[str, ...]
    note: str


ALL_GROUPS = ("small", "dimension-one", "prime", "squarefree", "prefix", "full")
SOLUTIONS = (
    Solution("std-readable", "std.cpp", ALL_GROUPS, "正式可读标程"),
    Solution("timestamp-basic", "solutions/timestamp-basic.cpp", ALL_GROUPS,
             "研究工件普通 STL 版"),
    Solution("timestamp-fast", "solutions/timestamp-fast.cpp", ALL_GROUPS,
             "同算法常数优化版"),
    Solution("closure-prototype", "solutions/closure-prototype.cpp", ALL_GROUPS,
             "显式传播 p 倍的历史原型"),
    Solution("howell-rebuild", "solutions/howell-rebuild.cpp", ALL_GROUPS,
             "每次询问重建 Howell 基"),
    Solution("howell-segment", "solutions/howell-segment.cpp", ALL_GROUPS,
             "线段树合并 Howell 基"),
    Solution("howell-sparse", "solutions/howell-sparse.cpp", ALL_GROUPS,
             "稀疏表合并 Howell 基"),
    Solution("dimension-one-gcd", "solutions/dimension-one-gcd.cpp", ("dimension-one",),
             "d=1 子任务做法"),
    Solution("field-timestamp", "solutions/field-timestamp.cpp", ("prime",),
             "质数模数子任务做法"),
    Solution("prefix-howell", "solutions/prefix-howell.cpp", ("prefix",),
             "l=1 子任务做法"),
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(1 << 20):
            digest.update(block)
    return digest.hexdigest()


def compile_solution(solution: Solution, compiler: list[str], flags: list[str]) -> tuple[Path, float]:
    source = ROOT / solution.source
    output = BUILD / solution.name
    started = time.perf_counter()
    result = subprocess.run(
        [*compiler, *flags, str(source), "-o", str(output)],
        capture_output=True, text=True,
    )
    elapsed = time.perf_counter() - started
    (BUILD / f"compile-{solution.name}.txt").write_text(
        result.stdout + result.stderr, encoding="utf-8")
    result.check_returncode()
    return output, elapsed


def judge_case(binary: Path, solution: Solution, case: dict,
               timeout: float, memory_mib: int) -> dict:
    case_id = case["case_id"]
    output_path = BUILD / f"{solution.name}-{case_id}.out"
    error_path = BUILD / f"{solution.name}-{case_id}.err"
    metrics_path = BUILD / f"{solution.name}-{case_id}.metrics.json"
    limit_bytes = memory_mib * 1024 * 1024
    worker = ROOT / "solutions" / "run_with_metrics.py"
    subprocess.run([
        sys.executable, str(worker),
        "--binary", str(binary),
        "--input", str(DATA / f"{case_id}.in"),
        "--output", str(output_path),
        "--stderr", str(error_path),
        "--metrics", str(metrics_path),
        "--timeout", str(timeout),
    ], check=True, timeout=timeout + 10)
    result = json.loads(metrics_path.read_text(encoding="utf-8"))
    if result["peak_rss_bytes"] > limit_bytes:
        result["status"] = "MLE"
    if result["status"] == "finished":
        expected = (DATA / f"{case_id}.ans").read_bytes().split()
        actual = output_path.read_bytes().split()
        result["status"] = "AC" if actual == expected else "WA"
        result["output_tokens"] = len(actual)
    if result["status"] not in ("AC", "WA"):
        result["stderr_tail"] = error_path.read_text(encoding="utf-8", errors="replace")[-2000:]
    return result


def score_solution(solution: Solution, results: dict[str, dict],
                   cases: list[dict], groups: list[dict]) -> dict:
    eligible = [group for group in groups if group["name"] in solution.scope]
    earned = 0
    group_results = {}
    for group in eligible:
        ids = group["cases"]
        passed = all(results.get(case_id, {}).get("status") == "AC" for case_id in ids)
        group_results[group["name"]] = {
            "score": group["score"],
            "passed": passed,
            "cases": ids,
        }
        if passed:
            earned += group["score"]
    possible = sum(group["score"] for group in eligible)
    measured = [item for item in results.values() if "wall_seconds" in item]
    return {
        "earned_score": earned,
        "possible_score": possible,
        "group_results": group_results,
        "measured_wall_seconds": sum(item["wall_seconds"] for item in measured),
        "max_case_seconds": max((item["wall_seconds"] for item in measured), default=0),
        "peak_rss_bytes": max(
            (item.get("peak_rss_bytes", 0) for item in measured), default=0),
    }


def render_cell(result: dict | None) -> str:
    if result is None:
        return "—"
    status = result["status"]
    if status == "AC":
        rss = result.get("peak_rss_bytes", 0) / 2**20
        return f"{result['wall_seconds']:.3f}s / {rss:.0f}MiB"
    if status == "SKIP":
        return "skip"
    return status


def render_report(payload: dict, path: Path) -> None:
    lines = [
        "# 正式题目多做法测评",
        "",
        f"测评时间（UTC）：{payload['created_utc']}",
        "",
        "所有完整做法使用相同正式输入、token 答案和编译参数。每个程序每个数据运行一次；耗时包含输入、求解和输出。",
        "短用例会受到进程启动开销影响，本报告用于题目验收而不是发表级微基准。",
        "",
        f"- 主机：{payload['environment']['machine']}，{payload['environment']['system']} {payload['environment']['release']}",
        f"- 编译器：`{payload['compiler_version'].splitlines()[0]}`",
        f"- 编译参数：`{' '.join(payload['flags'])}`",
        f"- 单点时限：{payload['timeout_seconds']} 秒；RSS 上限：{payload['memory_mib']} MiB（按子进程高水位判定）",
        "- 某子任务首个失败点出现后，该做法在同一子任务的后续文件记为 `skip`。",
        "",
        "## 汇总",
        "",
        "| 做法 | 范围 | 结果 | 得分 | 已测总耗时 | 峰值 RSS | 说明 |",
        "|---|---|---:|---:|---:|---:|---|",
    ]
    by_name = {item["name"]: item for item in payload["solutions"]}
    for solution in payload["solutions"]:
        summary = solution["summary"]
        complete = summary["earned_score"] == summary["possible_score"]
        verdict = "AC" if complete else "未通过"
        scope = "完整" if tuple(solution["scope"]) == ALL_GROUPS else ", ".join(solution["scope"])
        lines.append(
            f"| `{solution['name']}` | {scope} | {verdict} | "
            f"{summary['earned_score']}/{summary['possible_score']} | "
            f"{summary['measured_wall_seconds']:.3f}s | "
            f"{summary['peak_rss_bytes']/2**20:.1f} MiB | {solution['note']} |"
        )

    full_names = [item["name"] for item in payload["solutions"]
                  if tuple(item["scope"]) == ALL_GROUPS]
    lines += [
        "",
        "## 完整做法逐点结果",
        "",
        "单元格为 `墙钟时间 / 峰值 RSS`。失败状态为 TLE、MLE、RE 或 WA。",
        "",
        "| 数据 | n/d/q | " + " | ".join(f"`{name}`" for name in full_names) + " |",
        "|---|---:|" + "---:|" * len(full_names),
    ]
    for case in payload["cases"]:
        cells = [render_cell(by_name[name]["results"].get(case["case_id"])) for name in full_names]
        lines.append(
            f"| {case['case_id']} {case['name']} | {case['n']}/{case['d']}/{case['q']} | "
            + " | ".join(cells) + " |"
        )

    lines += ["", "## 子任务专用做法", "",
              "| 做法 | 子任务 | 各数据 | 得分 |", "|---|---|---|---:|"]
    for solution in payload["solutions"]:
        if tuple(solution["scope"]) == ALL_GROUPS:
            continue
        cells = []
        for case_id, result in solution["results"].items():
            cells.append(f"{case_id}: {render_cell(result)}")
        summary = solution["summary"]
        lines.append(
            f"| `{solution['name']}` | {', '.join(solution['scope'])} | "
            f"{'; '.join(cells)} | {summary['earned_score']}/{summary['possible_score']} |"
        )

    accepted_full = [item for item in payload["solutions"]
                     if tuple(item["scope"]) == ALL_GROUPS
                     and item["summary"]["earned_score"] == 100]
    lines += ["", "## 结论", ""]
    if accepted_full:
        ordered = sorted(accepted_full, key=lambda item: item["summary"]["measured_wall_seconds"])
        fastest = ordered[0]
        lines.append(
            f"- 完整通过的做法有 {len(ordered)} 个；按本轮正式数据总墙钟，最快为 "
            f"`{fastest['name']}`（{fastest['summary']['measured_wall_seconds']:.3f}s）。"
        )
        std = next((item for item in ordered if item["name"] == "std-readable"), None)
        fast = next((item for item in ordered if item["name"] == "timestamp-fast"), None)
        if std and fast:
            ratio = std["summary"]["measured_wall_seconds"] / fast["summary"]["measured_wall_seconds"]
            lines.append(f"- 优化时间戳版相对可读标程的整批墙钟加速为 {ratio:.2f} 倍。")
    for item in payload["solutions"]:
        if tuple(item["scope"]) == ALL_GROUPS and item["summary"]["earned_score"] < 100:
            failures = [f"{case_id}:{result['status']}" for case_id, result in item["results"].items()
                        if result["status"] not in ("AC", "SKIP")]
            lines.append(f"- `{item['name']}` 未完整通过：{', '.join(failures) or '存在未通过分组'}。")
    lines += [
        "- 域专用、一维 gcd 和前缀 Howell 均只证明对应子任务，不是完整题解。",
        "- `xor-packed` 已通过模 2 冒烟测试；正式数据没有独立的 $m=2$ 组，因此不计分也不列耗时。",
        "- Howell 三种候选是本项目的本地饱和阶梯实现，不代表该路线的最优工程实现。",
        "",
        "原始逐点状态、耗时、RSS、编译时间、源码哈希和错误尾部见 [solution-comparison.json](solution-comparison.json)。",
        "",
    ]
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=float, default=8.0)
    parser.add_argument("--memory-mib", type=int, default=512)
    parser.add_argument("--only", help="comma-separated solution names")
    args = parser.parse_args()
    if args.timeout <= 0 or args.memory_mib < 32:
        parser.error("invalid resource limits")

    selected = list(SOLUTIONS)
    if args.only:
        names = args.only.split(",")
        known = {solution.name for solution in SOLUTIONS}
        if not set(names) <= known:
            parser.error(f"unknown solutions: {sorted(set(names) - known)}")
        selected = [solution for solution in SOLUTIONS if solution.name in names]

    manifest = json.loads((DATA / "manifest.json").read_text(encoding="utf-8"))
    config = json.loads((ROOT / "problem.json").read_text(encoding="utf-8"))
    cases = manifest["cases"]
    groups = config["subtasks"]
    BUILD.mkdir(parents=True, exist_ok=True)
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    compiler = shlex.split(os.environ.get("CXX", "c++"))
    flags = ["-std=c++17", "-O2", "-DNDEBUG", "-Wall", "-Wextra", "-Wpedantic"]

    compiled = {}
    compile_seconds = {}
    for solution in selected:
        print(f"compile {solution.name}", flush=True)
        compiled[solution.name], compile_seconds[solution.name] = compile_solution(
            solution, compiler, flags)

    # Warm each executable's filesystem pages; warmups do not consume official
    # input and are excluded from measurements.
    for binary in compiled.values():
        subprocess.run([str(binary)], input=b"", stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL, check=True, timeout=5)

    solution_results = []
    for solution in selected:
        print(f"judge {solution.name}", flush=True)
        results = {}
        failed_groups = set()
        for case in cases:
            group = case["subtask"]
            if group not in solution.scope:
                continue
            if group in failed_groups:
                results[case["case_id"]] = {"status": "SKIP"}
                continue
            result = judge_case(
                compiled[solution.name], solution, case, args.timeout, args.memory_mib)
            results[case["case_id"]] = result
            print(f"  {case['case_id']}: {result['status']} {result['wall_seconds']:.3f}s", flush=True)
            if result["status"] != "AC":
                failed_groups.add(group)
        summary = score_solution(solution, results, cases, groups)
        solution_results.append({
            "name": solution.name,
            "source": solution.source,
            "source_sha256": sha256(ROOT / solution.source),
            "scope": list(solution.scope),
            "note": solution.note,
            "compile_seconds": compile_seconds[solution.name],
            "results": results,
            "summary": summary,
        })

    compiler_version = subprocess.run(
        [*compiler, "--version"], capture_output=True, text=True, check=True, timeout=30,
    ).stdout.strip()
    payload = {
        "schema": "astra4oi.range-module.solution-comparison.v1",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "environment": {
            "system": platform.system(),
            "release": platform.release(),
            "machine": platform.machine(),
            "python": platform.python_version(),
            "logical_cpus": os.cpu_count(),
        },
        "compiler": compiler,
        "compiler_version": compiler_version,
        "flags": flags,
        "timeout_seconds": args.timeout,
        "memory_mib": args.memory_mib,
        "data_manifest_sha256": sha256(DATA / "manifest.json"),
        "shared_algorithms_sha256": sha256(
            RESULT_ROOT / "implementation" / "benchmark_cpp" / "algorithms.hpp"),
        "cases": cases,
        "solutions": solution_results,
    }
    json_path = ARTIFACTS / "solution-comparison.json"
    report_path = ARTIFACTS / "solution-comparison.md"
    json_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    render_report(payload, report_path)
    print(f"wrote {report_path}")


if __name__ == "__main__":
    main()
