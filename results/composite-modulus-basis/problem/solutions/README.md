# 对比做法

本目录把研究工件中已经实现的候选算法接到正式题目输入上。除两个子任务程序外，公用适配器为 `runner.hpp`，核心实现复用 `implementation/benchmark_cpp/algorithms.hpp`，避免复制后产生两份不一致代码。

| 程序 | 适用范围 | 说明 |
|---|---|---|
| `../std.cpp` | 完整数据 | 可读的带时间戳 $p$ 进阶梯基，正式标程 |
| `timestamp-basic.cpp` | 完整数据 | 研究工件中的普通 STL 实现 |
| `timestamp-fast.cpp` | 完整数据 | 同算法的平坦内存、复用缓冲区和模运算优化版 |
| `closure-prototype.cpp` | 完整数据 | 每次写槽后显式传播 $p$ 倍的历史原型 |
| `howell-rebuild.cpp` | 完整数据，可能超时 | 每个询问从头建立饱和三角基 |
| `howell-segment.cpp` | 完整数据，空间较大 | 线段树存子模基，查询时合并 |
| `howell-sparse.cpp` | 完整数据，空间很大 | 稀疏表存区间子模基 |
| `field-timestamp.cpp` | 仅质数模数 | 域上的经典时间戳线性基 |
| `xor-packed.cpp` | 仅 $m=2,d\le64$ | 64 位打包异或基；正式数据没有专属组 |
| `dimension-one-gcd.cpp` | 仅 $d=1$ | 线段树区间 gcd |
| `prefix-howell.cpp` | 仅 $l=1$ | 单个增量 Howell 基 |

`benchmark_solutions.py` 会用相同的 `-O2 -DNDEBUG` 编译选项、正式输入和 token 答案测量这些程序。结果写入 `artifacts/solution-comparison.json` 和 `artifacts/solution-comparison.md`。
