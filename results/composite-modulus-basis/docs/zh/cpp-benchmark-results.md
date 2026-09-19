# OI/CP C++ 性能实测

[English](../en/cpp-benchmark-results.md)

本页是提交 `9a0fb9e` 的横向基准快照；当前快版的进一步优化见 [常数优化报告](constant-tuning.md)。

**结论应按模数和数据分布区分：小幂指数下表现突出，深幂层下并不总胜出，模 2 应优先考虑打包专用实现。** 以下列出完整测试矩阵，不把超时当成具体耗时，也不把本地基线称为该路线的最快实现。

机器：Apple M3 Pro，Darwin 25.6.0；Apple clang version 17.0.0 (clang-1700.6.3.2)。原生优化使用 `-std=c++17 -Wall -Wextra -O3 -DNDEBUG -march=native`。标准组 5 次测量，伸缩与压力组各 3 / 3 次，均另有预热。

时间为**整批求解**中位数，包括建表、离线分桶、查询和内部内存管理，不是单次查询延迟。各候选使用同一快读/输出、编译选项及数据。RSS 为整个进程高水位。数据生成、oracle 和解析/输出不计入主时间，端到端程序时间另存原始报告。

n 为向量数，d 为维度，q 为询问数；K 为素因子指数之和，w 为不同素因子数量。

## 标准数据：完整结果

| Case | m; n / d / q | Basic ms | Fast ms | Best baseline | Baseline ms | Baseline / fast |
| --- | --- | --- | --- | --- | --- | --- |
| binary-d64 | 2; 20000 / 64 / 20000 | 89.14 | 32.79 | xor-packed | 5.33 | 0.16x |
| prime-d32 | 998244353; 10000 / 32 / 20000 | 53.50 | 31.78 | field-timestamp | 31.56 | 0.99x |
| square-d32 | 4; 20000 / 32 / 20000 | 82.13 | 32.96 | howell-rebuild | 104.57 | 3.17x |
| deep-power-d24 | 65536; 12000 / 24 / 24000 | 610.85 | 163.33 | howell-rebuild | 115.05 | 0.70x |
| odd-power-d24 | 59049; 12000 / 24 / 24000 | 351.74 | 232.07 | howell-rebuild | 154.42 | 0.67x |
| crt-d32 | 72; 12000 / 32 / 24000 | 167.64 | 62.30 | howell-rebuild | 372.84 | 5.98x |
| many-primes-d24 | 9699690; 12000 / 24 / 24000 | 197.90 | 81.79 | howell-rebuild | 243.84 | 2.98x |
| word-boundary-d32 | 4294967291; 10000 / 32 / 20000 | 54.30 | 34.35 | field-timestamp | 33.10 | 0.96x |
| composite-boundary-d24 | 4294967295; 12000 / 24 / 24000 | 135.81 | 65.48 | howell-rebuild | 179.90 | 2.75x |
| coupled-crt-d32 | 72; 12000 / 32 / 24000 | 151.83 | 58.56 | howell-segment | 628.27 | 10.73x |
| nonunit-power-d24 | 65536; 12000 / 24 / 24000 | 476.39 | 152.21 | howell-segment | 310.07 | 2.04x |
| valuation-ladder-d24 | 1073741824; 12000 / 24 / 24000 | 37.98 | 11.09 | howell-segment | 128.17 | 11.56x |
| zeros-duplicates-d32 | 72; 12000 / 32 / 24000 | 54.22 | 22.18 | howell-segment | 238.28 | 10.74x |

比值大于 1 表示优化版更快。best baseline 只在完成全部测量的 Howell 风格及域专用候选中选择，不包含本项目闭包原型；全部候选（含原型）、波动范围、失败状态及 YES 比例见原始报告。

按中位数，优化版在 8 / 13 个标准场景中快于上述最佳已完成基线。这只是固定数据集的胜负计数，不是成功率估计。

未胜出的场景：binary-d64、prime-d32、deep-power-d24、odd-power-d24、word-boundary-d32。接近 1 的比值尤其不应解释成稳定的跨机器优势。

## 编译选项与结构优化分开比较

| Case | O2 basic ms | O2 fast ms | Native basic ms | Native fast ms |
| --- | --- | --- | --- | --- |
| binary-d64 | 90.87 | 36.51 | 89.14 | 32.79 |
| prime-d32 | 53.45 | 32.87 | 53.50 | 31.78 |
| square-d32 | 81.76 | 35.11 | 82.13 | 32.96 |
| deep-power-d24 | 543.52 | 176.31 | 610.85 | 163.33 |
| odd-power-d24 | 335.64 | 238.23 | 351.74 | 232.07 |
| crt-d32 | 167.37 | 66.58 | 167.64 | 62.30 |
| many-primes-d24 | 190.96 | 88.31 | 197.90 | 81.79 |
| word-boundary-d32 | 53.89 | 33.52 | 54.30 | 34.35 |
| composite-boundary-d24 | 140.98 | 69.25 | 135.81 | 65.48 |
| coupled-crt-d32 | 164.20 | 65.27 | 151.83 | 58.56 |
| nonunit-power-d24 | 554.63 | 163.50 | 476.39 | 152.21 |
| valuation-ladder-d24 | 38.40 | 12.58 | 37.98 | 11.09 |
| zeros-duplicates-d32 | 54.72 | 24.44 | 54.22 | 22.18 |

同一列组内才是普通/优化实现的直接比较；不要把普通版 O2 与优化版 native 的差距全部归因于算法。

## 参数伸缩

| Case | m; n / d / q; K / w | Basic ms | Fast ms | Best baseline ms (name) |
| --- | --- | --- | --- | --- |
| dimension-8 | 4; 8000 / 8 / 16000; 2 / 1 | 13.00 | 4.16 | 18.46 (howell-rebuild) |
| dimension-16 | 4; 8000 / 16 / 16000; 2 / 1 | 19.87 | 5.74 | 34.60 (howell-rebuild) |
| dimension-32 | 4; 8000 / 32 / 16000; 2 / 1 | 37.57 | 13.02 | 86.38 (howell-rebuild) |
| dimension-64 | 4; 8000 / 64 / 16000; 2 / 1 | 101.77 | 37.35 | 357.65 (howell-segment) |
| exponent-1 | 2; 8000 / 24 / 16000; 1 / 1 | 17.22 | 5.62 | 2.16 (xor-packed) |
| exponent-2 | 4; 8000 / 24 / 16000; 2 / 1 | 25.43 | 12.05 | 53.36 (howell-rebuild) |
| exponent-4 | 16; 8000 / 24 / 16000; 4 / 1 | 60.57 | 23.57 | 66.73 (howell-rebuild) |
| exponent-8 | 256; 8000 / 24 / 16000; 8 / 1 | 152.83 | 49.11 | 78.09 (howell-rebuild) |
| exponent-16 | 65536; 8000 / 24 / 16000; 16 / 1 | 345.20 | 111.52 | 77.02 (howell-rebuild) |
| exponent-30 | 1073741824; 8000 / 24 / 16000; 30 / 1 | 742.74 | 228.59 | 79.62 (howell-rebuild) |
| queries-1000 | 4; 8000 / 32 / 1000; 2 / 1 | 38.51 | 11.30 | 8.39 (howell-rebuild) |
| queries-8000 | 4; 8000 / 32 / 8000; 2 / 1 | 37.28 | 12.42 | 45.81 (howell-rebuild) |
| queries-64000 | 4; 8000 / 32 / 64000; 2 / 1 | 61.99 | 24.83 | 274.01 (howell-sparse) |
| length-1000 | 4; 1000 / 32 / 16000; 2 / 1 | 10.47 | 5.42 | 51.32 (howell-sparse) |
| length-64000 | 4; 64000 / 32 / 16000; 2 / 1 | 229.83 | 75.23 | 87.17 (howell-rebuild) |
| components-2 | 6; 8000 / 24 / 16000; 2 / 2 | 24.46 | 10.86 | 102.29 (howell-rebuild) |
| components-4 | 210; 8000 / 24 / 16000; 4 / 4 | 55.30 | 22.56 | 147.05 (howell-rebuild) |
| components-8 | 9699690; 8000 / 24 / 16000; 8 / 8 | 125.29 | 56.26 | 165.27 (howell-rebuild) |

这些是有限参数扫描，不能据此证明最坏复杂度或拟合出最优渐近界；理论界仍以论文证明为准。

## 资源上限与峰值内存

| Case | Algorithm | Solve s / status | Peak RSS MiB |
| --- | --- | --- | --- |
| n100k-d64-square | howell-rebuild | 2.7957 | 56.5 |
| n100k-d64-square | timestamp-fast | 0.4239 | 59.7 |
| n100k-d64-square | howell-segment | memory_limit | — |
| n100k-d64-square | closure-prototype | 1.3049 | 59.8 |
| n100k-d64-square | timestamp-basic | 1.2240 | 59.7 |
| n100k-d64-square | howell-sparse | memory_limit | — |
| n100k-deep-power | howell-rebuild | 0.8631 | 32.0 |
| n100k-deep-power | timestamp-fast | 4.4820 | 35.2 |
| n100k-deep-power | howell-segment | 1.1864 | 347.5 |
| n100k-deep-power | closure-prototype | timeout | — |
| n100k-deep-power | timestamp-basic | timeout | — |
| n100k-deep-power | howell-sparse | memory_limit | — |
| n100k-many-primes | howell-rebuild | 1.7719 | 32.0 |
| n100k-many-primes | timestamp-fast | 0.8776 | 35.2 |
| n100k-many-primes | howell-segment | 2.5332 | 358.3 |
| n100k-many-primes | closure-prototype | 2.1298 | 35.2 |
| n100k-many-primes | timestamp-basic | 2.1839 | 35.2 |
| n100k-many-primes | howell-sparse | memory_limit | — |
| q500k-square | howell-rebuild | 2.8132 | 83.2 |
| q500k-square | timestamp-fast | 0.2050 | 87.8 |
| q500k-square | howell-segment | 2.5819 | 155.6 |
| q500k-square | closure-prototype | 0.3310 | 87.8 |
| q500k-square | timestamp-basic | 0.3860 | 87.9 |
| q500k-square | howell-sparse | memory_limit | — |
| dimension-128 | howell-rebuild | 3.4810 | 22.4 |
| dimension-128 | timestamp-fast | 0.2379 | 23.1 |
| dimension-128 | howell-segment | 2.6748 | 329.6 |
| dimension-128 | closure-prototype | 0.9430 | 23.2 |
| dimension-128 | timestamp-basic | 0.8070 | 23.2 |
| dimension-128 | howell-sparse | memory_limit | — |

压力组预算：每个进程 8.0 秒墙钟、512 MiB RSS。超时还包含读入等开销，所以不能用该阈值推导 solve 的精确下界。

## 验证、适用范围与复现

每种发布构建先通过 2,741,761 次独立 C++ 成员判断检查，以及精确模算术检查。另有 UBSan 小规模全流程。ASan 在本机运行时初始化阶段死锁，未宣称通过。

所有完成的性能运行逐个检查构造正例、结构性反例、独立格 oracle 探针和完整答案 SHA-256；没有把程序之间一致当作独立数学证明。

范围：32 位模数、静态批量区间查询、已给时间戳方案所需分解。Howell 候选无需分解，但只是本地饱和阶梯实现，不是最优化的正规形库；未测快速矩阵乘法、历史在线快照、因数分解、64 位模数及 x86/Linux 硬件。未锁频或独占机器，原始重复数据与 CV 可用于判断抖动。

原始工件：

- [Standard native](../../artifacts/cpp-benchmark/standard-native/report.md)
- [Standard portable O2](../../artifacts/cpp-benchmark/standard-portable/report.md)
- [Scaling](../../artifacts/cpp-benchmark/scaling-native/report.md)
- [Stress](../../artifacts/cpp-benchmark/stress-native/report.md)
- [UBSan validation](../../artifacts/cpp-benchmark/ubsan-final/report.md)
- [Code and reproduction](../../implementation/benchmark_cpp/README.md)
