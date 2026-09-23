# 正式题目多做法测评

测评时间（UTC）：2026-09-23T15:04:10.818655+00:00

所有完整做法使用相同正式输入、token 答案和编译参数。每个程序每个数据运行一次；耗时包含输入、求解和输出。
短用例会受到进程启动开销影响，本报告用于题目验收而不是发表级微基准。

- 主机：arm64，Darwin 25.6.0
- 编译器：`Apple clang version 17.0.0 (clang-1700.6.3.2)`
- 编译参数：`-std=c++17 -O2 -DNDEBUG -Wall -Wextra -Wpedantic`
- 单点时限：8.0 秒；RSS 上限：512 MiB（按子进程高水位判定）
- 某子任务首个失败点出现后，该做法在同一子任务的后续文件记为 `skip`。

## 汇总

| 做法 | 范围 | 结果 | 得分 | 已测总耗时 | 峰值 RSS | 说明 |
|---|---|---:|---:|---:|---:|---|
| `std-readable` | 完整 | AC | 100/100 | 4.847s | 12.6 MiB | 正式可读标程 |
| `timestamp-basic` | 完整 | AC | 100/100 | 5.135s | 13.3 MiB | 研究工件普通 STL 版 |
| `timestamp-fast` | 完整 | AC | 100/100 | 4.750s | 13.3 MiB | 同算法常数优化版 |
| `closure-prototype` | 完整 | AC | 100/100 | 4.943s | 13.3 MiB | 显式传播 p 倍的历史原型 |
| `howell-rebuild` | 完整 | 未通过 | 55/100 | 34.175s | 10.0 MiB | 每次询问重建 Howell 基 |
| `howell-segment` | 完整 | AC | 100/100 | 6.156s | 58.5 MiB | 线段树合并 Howell 基 |
| `howell-sparse` | 完整 | 未通过 | 70/100 | 8.442s | 715.5 MiB | 稀疏表合并 Howell 基 |
| `dimension-one-gcd` | dimension-one | AC | 15/15 | 0.495s | 3.3 MiB | d=1 子任务做法 |
| `field-timestamp` | prime | AC | 15/15 | 0.644s | 3.0 MiB | 质数模数子任务做法 |
| `prefix-howell` | prefix | AC | 15/15 | 0.371s | 3.3 MiB | l=1 子任务做法 |

## 完整做法逐点结果

单元格为 `墙钟时间 / 峰值 RSS`。失败状态为 TLE、MLE、RE 或 WA。

| 数据 | n/d/q | `std-readable` | `timestamp-basic` | `timestamp-fast` | `closure-prototype` | `howell-rebuild` | `howell-segment` | `howell-sparse` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 01 small-p4 | 12/2/32 | 0.007s / 1MiB | 0.006s / 1MiB | 0.007s / 1MiB | 0.005s / 1MiB | 0.006s / 1MiB | 0.006s / 1MiB | 0.006s / 1MiB |
| 02 small-crt | 14/3/40 | 0.006s / 1MiB | 0.006s / 1MiB | 0.006s / 1MiB | 0.005s / 1MiB | 0.005s / 1MiB | 0.006s / 1MiB | 0.005s / 1MiB |
| 03 small-zeros | 30/4/60 | 0.006s / 1MiB | 0.005s / 1MiB | 0.006s / 1MiB | 0.005s / 1MiB | 0.006s / 1MiB | 0.006s / 1MiB | 0.011s / 1MiB |
| 04 dimension-one-72 | 10000/1/12000 | 0.042s / 3MiB | 0.040s / 3MiB | 0.038s / 3MiB | 0.037s / 3MiB | 0.407s / 2MiB | 0.041s / 6MiB | 0.075s / 16MiB |
| 05 dimension-one-boundary | 100000/1/100000 | 0.440s / 13MiB | 0.460s / 13MiB | 0.461s / 13MiB | 0.405s / 13MiB | TLE | 0.509s / 37MiB | 0.619s / 178MiB |
| 06 prime-local | 6000/16/8000 | 0.337s / 3MiB | 0.298s / 3MiB | 0.345s / 3MiB | 0.293s / 3MiB | 0.350s / 3MiB | 0.351s / 12MiB | 0.349s / 84MiB |
| 07 prime-coupled | 5000/20/7000 | 0.333s / 3MiB | 0.349s / 3MiB | 0.396s / 3MiB | 0.348s / 3MiB | 0.890s / 3MiB | 0.447s / 14MiB | 0.455s / 93MiB |
| 08 squarefree-local | 8000/14/10000 | 0.178s / 3MiB | 0.178s / 3MiB | 0.186s / 3MiB | 0.188s / 3MiB | 0.184s / 3MiB | 0.184s / 14MiB | 0.242s / 109MiB |
| 09 squarefree-axis | 7000/16/9000 | 0.184s / 3MiB | 0.188s / 3MiB | 0.183s / 3MiB | 0.188s / 3MiB | 0.734s / 3MiB | 0.241s / 13MiB | 0.401s / 99MiB |
| 10 squarefree-zeros | 5000/20/7000 | 0.188s / 3MiB | 0.234s / 3MiB | 0.186s / 3MiB | 0.187s / 3MiB | 0.574s / 3MiB | 0.235s / 14MiB | 0.345s / 90MiB |
| 11 prefix-power | 8000/16/10000 | 0.286s / 3MiB | 0.286s / 3MiB | 0.288s / 3MiB | 0.298s / 3MiB | 5.620s / 3MiB | 0.400s / 15MiB | 0.458s / 118MiB |
| 12 prefix-crt | 6500/20/8500 | 0.188s / 3MiB | 0.238s / 3MiB | 0.181s / 3MiB | 0.183s / 3MiB | 5.117s / 3MiB | 0.392s / 16MiB | 0.448s / 128MiB |
| 13 full-padic-local | 7000/20/9000 | 0.292s / 3MiB | 0.347s / 3MiB | 0.287s / 3MiB | 0.354s / 4MiB | 0.237s / 3MiB | 0.296s / 16MiB | 0.336s / 142MiB |
| 14 full-crt-coupled | 8000/20/10000 | 0.293s / 4MiB | 0.291s / 4MiB | 0.228s / 4MiB | 0.292s / 4MiB | 1.433s / 3MiB | 0.335s / 17MiB | 0.506s / 161MiB |
| 15 full-many-primes | 8000/18/10000 | 0.237s / 4MiB | 0.234s / 4MiB | 0.240s / 4MiB | 0.239s / 4MiB | 0.997s / 3MiB | 0.297s / 16MiB | 0.510s / 147MiB |
| 16 full-zeros-duplicates | 5000/24/7000 | 0.185s / 3MiB | 0.228s / 3MiB | 0.184s / 3MiB | 0.242s / 3MiB | 0.720s / 3MiB | 0.293s / 17MiB | 0.449s / 121MiB |
| 17 full-large-modulus | 5000/20/7000 | 0.351s / 3MiB | 0.343s / 3MiB | 0.340s / 3MiB | 0.344s / 3MiB | 0.885s / 3MiB | 0.395s / 15MiB | 0.509s / 98MiB |
| 18 full-max-nq | 100000/2/100000 | 0.399s / 13MiB | 0.405s / 13MiB | 0.345s / 13MiB | 0.398s / 13MiB | TLE | 0.452s / 40MiB | 0.573s / 201MiB |
| 19 full-deep-power | 30000/20/30000 | 0.896s / 9MiB | 0.997s / 9MiB | 0.844s / 9MiB | 0.931s / 9MiB | skip | 1.270s / 58MiB | MLE |

## 子任务专用做法

| 做法 | 子任务 | 各数据 | 得分 |
|---|---|---|---:|
| `dimension-one-gcd` | dimension-one | 04: 0.039s / 2MiB; 05: 0.456s / 3MiB | 15/15 |
| `field-timestamp` | prime | 06: 0.346s / 3MiB; 07: 0.297s / 3MiB | 15/15 |
| `prefix-howell` | prefix | 11: 0.188s / 3MiB; 12: 0.183s / 3MiB | 15/15 |

## 结论

- 完整通过的做法有 5 个；按本轮正式数据总墙钟，最快为 `timestamp-fast`（4.750s）。
- 优化时间戳版相对可读标程的整批墙钟加速为 1.02 倍。
- `howell-rebuild` 未完整通过：05:TLE, 18:TLE。
- `howell-sparse` 未完整通过：19:MLE。
- 域专用、一维 gcd 和前缀 Howell 均只证明对应子任务，不是完整题解。
- `xor-packed` 已通过模 2 冒烟测试；正式数据没有独立的 $m=2$ 组，因此不计分也不列耗时。
- Howell 三种候选是本项目的本地饱和阶梯实现，不代表该路线的最优工程实现。

原始逐点状态、耗时、RSS、编译时间、源码哈希和错误尾部见 [solution-comparison.json](solution-comparison.json)。
