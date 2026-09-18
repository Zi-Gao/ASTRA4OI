"""Build bilingual CP-facing summaries from completed benchmark JSON only."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
ARTIFACTS = ROOT / "artifacts/cpp-benchmark"
EXTERNAL = ("howell-rebuild", "howell-segment", "howell-sparse", "field-timestamp", "xor-packed")


def load(name):
    data = json.loads((ARTIFACTS / name / "results.json").read_text())
    if data["status"] != "complete":
        raise ValueError(f"incomplete benchmark: {name}")
    return data


def best(case):
    candidates = [(name, case["summaries"][name]) for name in EXTERNAL
                  if name in case["summaries"] and case["summaries"][name]["status"] == "ok"]
    return min(candidates, key=lambda pair: pair[1]["median_solve_seconds"]) if candidates else (None, None)


def cell(summary, milliseconds=True):
    if summary.get("status") != "ok":
        return summary.get("status", "—")
    scale = 1000 if milliseconds else 1
    return f"{summary['median_solve_seconds']*scale:.2f}" if milliseconds else f"{summary['median_solve_seconds']:.4f}"


def render(native, portable, scaling, stress, lang):
    zh = lang == "zh"
    heading = "OI/CP C++ 性能实测" if zh else "OI/CP C++ performance results"
    other = "en" if zh else "zh"
    lines = [f"# {heading}", "", f"[{'English' if zh else '中文'}](../{other}/cpp-benchmark-results.md)", ""]
    if zh:
        lines += ["**结论应按模数和数据分布区分：小幂指数下表现突出，深幂层下并不总胜出，模 2 应优先考虑打包专用实现。** 以下列出完整测试矩阵，不把超时当成具体耗时，也不把本地基线称为该路线的最快实现。", "",
                  f"机器：{native['environment'].get('cpu', 'unknown')}，{native['environment']['system']} {native['environment']['release']}；{native['compiler_version'].splitlines()[0]}。原生优化使用 `{' '.join(native['flags'])}`。标准组 {native['repeats']} 次测量，伸缩与压力组各 {scaling['repeats']} / {stress['repeats']} 次，均另有预热。", "",
                  "时间为**整批求解**中位数，包括建表、离线分桶、查询和内部内存管理，不是单次查询延迟。各候选使用同一快读/输出、编译选项及数据。RSS 为整个进程高水位。数据生成、oracle 和解析/输出不计入主时间，端到端程序时间另存原始报告。", "",
                  "n 为向量数，d 为维度，q 为询问数；K 为素因子指数之和，w 为不同素因子数量。", ""]
    else:
        lines += ["**Results depend on modulus and distribution: small exponents are favorable, deep powers do not always win, and packed XOR remains the specialized choice for modulus 2.** The full matrix is shown; timeouts are not exact times, and local baselines are not claimed to be best-in-class implementations.", "",
                  f"Host: {native['environment'].get('cpu', 'unknown')}, {native['environment']['system']} {native['environment']['release']}; {native['compiler_version'].splitlines()[0]}. Native flags: `{' '.join(native['flags'])}`. Standard: {native['repeats']} measured runs; scaling/stress: {scaling['repeats']}/{stress['repeats']}, plus warmups.", "",
                  "Times are medians for the **entire solve**, including construction, offline bucketing, queries and internal memory management, not individual query latency. All candidates share buffered I/O, compiler flags and inputs. RSS is whole-process high water. Generation, oracle work and parsing/output are excluded from solve time; end-to-end program time is recorded separately.", "",
                  "n is the vector count, d the dimension, q the query count, K the sum of prime-power exponents, and w the number of distinct prime factors.", ""]
    lines += ["## " + ("标准数据：完整结果" if zh else "Standard matrix"), "",
              "| Case | m; n / d / q | Basic ms | Fast ms | Best baseline | Baseline ms | Baseline / fast |",
              "| --- | --- | --- | --- | --- | --- | --- |"]
    for case in native["cases"]:
        spec, s = case["manifest"], case["summaries"]
        name, baseline = best(case)
        fast = s["timestamp-fast"]
        ratio = f"{baseline['median_solve_seconds']/fast['median_solve_seconds']:.2f}x" if baseline and fast["status"] == "ok" else "—"
        lines.append(f"| {spec['name']} | {spec['modulus']}; {spec['n']} / {spec['d']} / {spec['q']} | "
                     f"{cell(s['timestamp-basic'])} | {cell(fast)} | {name or '—'} | {cell(baseline or {})} | {ratio} |")
    lines += ["", ("比值大于 1 表示优化版更快。best baseline 只在完成全部测量的 Howell 风格及域专用候选中选择，不包含本项目闭包原型；全部候选（含原型）、波动范围、失败状态及 YES 比例见原始报告。"
                    if zh else "A ratio above 1 favors timestamp-fast. The best completed Howell-style/field baseline excludes the internal closure prototype. Full candidate results, variation, failures and YES fractions remain in the raw report."), ""]
    fast_wins = []
    fast_losses = []
    for case in native["cases"]:
        _, baseline = best(case)
        fast = case["summaries"]["timestamp-fast"]
        if baseline and fast["status"] == "ok":
            (fast_wins if fast["median_solve_seconds"] < baseline["median_solve_seconds"] else fast_losses).append(case["manifest"]["name"])
    if zh:
        lines += [f"按中位数，优化版在 {len(fast_wins)} / {len(fast_wins)+len(fast_losses)} 个标准场景中快于上述最佳已完成基线。这只是固定数据集的胜负计数，不是成功率估计。", "",
                  "未胜出的场景：" + "、".join(fast_losses) + "。接近 1 的比值尤其不应解释成稳定的跨机器优势。", ""]
    else:
        lines += [f"By median, timestamp-fast is faster in {len(fast_wins)} of {len(fast_wins)+len(fast_losses)} standard cases. This counts these fixed datasets, not a population win probability.", "",
                  "Non-winning cases: " + ", ".join(fast_losses) + ". Ratios near 1 should not be treated as stable cross-machine advantages.", ""]
    lines += ["## " + ("编译选项与结构优化分开比较" if zh else "Compiler tuning versus implementation tuning"), "",
              "| Case | O2 basic ms | O2 fast ms | Native basic ms | Native fast ms |",
              "| --- | --- | --- | --- | --- |"]
    port = {c["manifest"]["name"]: c for c in portable["cases"]}
    for case in native["cases"]:
        name = case["manifest"]["name"]
        if name not in port:
            continue
        p, n = port[name]["summaries"], case["summaries"]
        if port[name]["manifest"]["sha256"] != case["manifest"]["sha256"]:
            raise AssertionError("compiler comparison uses different inputs")
        lines.append(f"| {name} | {cell(p['timestamp-basic'])} | {cell(p['timestamp-fast'])} | {cell(n['timestamp-basic'])} | {cell(n['timestamp-fast'])} |")
    lines += ["", ("同一列组内才是普通/优化实现的直接比较；不要把普通版 O2 与优化版 native 的差距全部归因于算法。"
                    if zh else "Compare basic/fast within a compiler configuration; do not attribute an O2-basic versus native-fast gap entirely to the implementation."), "",
              "## " + ("参数伸缩" if zh else "Parameter scaling"), "",
              "| Case | m; n / d / q; K / w | Basic ms | Fast ms | Best baseline ms (name) |",
              "| --- | --- | --- | --- | --- |"]
    for case in scaling["cases"]:
        spec, s = case["manifest"], case["summaries"]
        name, baseline = best(case)
        lines.append(f"| {spec['name']} | {spec['modulus']}; {spec['n']} / {spec['d']} / {spec['q']}; {spec['K']} / {spec['w']} | "
                     f"{cell(s['timestamp-basic'])} | {cell(s['timestamp-fast'])} | {cell(baseline or {})} ({name or '—'}) |")
    lines += ["", ("这些是有限参数扫描，不能据此证明最坏复杂度或拟合出最优渐近界；理论界仍以论文证明为准。"
                    if zh else "These finite sweeps do not prove worst-case bounds or asymptotic optimality; those claims remain governed by the paper's analysis."), "",
              "## " + ("资源上限与峰值内存" if zh else "Stress and peak memory"), "",
              "| Case | Algorithm | Solve s / status | Peak RSS MiB |",
              "| --- | --- | --- | --- |"]
    for case in stress["cases"]:
        for name, s in case["summaries"].items():
            if s["status"] == "unsupported":
                continue
            memory = f"{s['peak_rss_bytes']/2**20:.1f}" if s["status"] == "ok" else "—"
            lines.append(f"| {case['manifest']['name']} | {name} | {cell(s, False)} | {memory} |")
    lines += ["", (f"压力组预算：每个进程 {stress['timeout_seconds']} 秒墙钟、{stress['memory_mib']} MiB RSS。超时还包含读入等开销，所以不能用该阈值推导 solve 的精确下界。" if zh else
                    f"Stress budget: {stress['timeout_seconds']} seconds wall time and {stress['memory_mib']} MiB RSS per process. Wall time includes parsing, so the timeout threshold is not an exact lower bound on solve time."), "",
              "## " + ("验证、适用范围与复现" if zh else "Validation, scope and reproduction"), ""]
    if zh:
        lines += [f"每种发布构建先通过 {native['verification']['membership_assertions']:,} 次独立 C++ 成员判断检查，以及精确模算术检查。另有 UBSan 小规模全流程。ASan 在本机运行时初始化阶段死锁，未宣称通过。", "",
                  "所有完成的性能运行逐个检查构造正例、结构性反例、独立格 oracle 探针和完整答案 SHA-256；没有把程序之间一致当作独立数学证明。", "",
                  "范围：32 位模数、静态批量区间查询、已给时间戳方案所需分解。Howell 候选无需分解，但只是本地饱和阶梯实现，不是最优化的正规形库；未测快速矩阵乘法、历史在线快照、因数分解、64 位模数及 x86/Linux 硬件。未锁频或独占机器，原始重复数据与 CV 可用于判断抖动。", "",
                  "原始工件："]
    else:
        lines += [f"Each build passes {native['verification']['membership_assertions']:,} independent C++ membership assertions and the exact-arithmetic self-test. UBSan smoke validation is also available. ASan stalled during host runtime initialization and is not claimed to have passed.", "",
                  "Every completed performance run checks constructed positives, analytic negatives where available, independent lattice probes and full-output SHA-256 agreement. Agreement between implementations is not a mathematical proof.", "",
                  "Scope: 32-bit moduli, static batch intervals, factorization supplied to timestamp methods. Howell candidates are factorization-free local saturated-echelon implementations, not tuned normal-form libraries. Fast matrix multiplication, online historical snapshots, factorization, 64-bit moduli and x86/Linux measurements are outside this run. Frequency and other host workloads were not controlled; raw repetitions and CV expose variability.", "",
                  "Raw artifacts:"]
    lines += ["",
              "- [Standard native](../../artifacts/cpp-benchmark/standard-native/report.md)",
              "- [Standard portable O2](../../artifacts/cpp-benchmark/standard-portable/report.md)",
              "- [Scaling](../../artifacts/cpp-benchmark/scaling-native/report.md)",
              "- [Stress](../../artifacts/cpp-benchmark/stress-native/report.md)",
              "- [UBSan validation](../../artifacts/cpp-benchmark/ubsan-final/report.md)",
              f"- [Code and reproduction](../../implementation/benchmark_cpp/{'README.md' if zh else 'README-EN.md'})", ""]
    return "\n".join(lines)


def main():
    groups = [load(name) for name in ("standard-native", "standard-portable", "scaling-native", "stress-native")]
    for filename in ("main.cpp", "algorithms.hpp", "arithmetic_test.cpp"):
        if len({data["source_sha256"][filename] for data in groups}) != 1:
            raise AssertionError(f"C++ source changed between groups: {filename}")
    for lang in ("zh", "en"):
        path = ROOT / "docs" / lang / "cpp-benchmark-results.md"
        path.write_text(render(*groups, lang))
        print(path)


if __name__ == "__main__":
    main()
