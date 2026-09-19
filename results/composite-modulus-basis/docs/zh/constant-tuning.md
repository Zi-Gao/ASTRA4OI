# C++ 常数优化：同编译条件下的前后对照

[English](../en/constant-tuning.md)

以提交 `9a0fb9e` 的 `timestamp-fast` 为基线，36 组 native 数据的整批求解中位数全部下降，提速 **1.08～2.16 倍**。这比较的是旧快版和新快版，不是与普通版或 Howell 基线比较。

Apple M3 Pro / Apple Clang 17，native 为 `-O3 -DNDEBUG -march=native`，portable 为 `-O2 -DNDEBUG`，均使用 C++17。每组先预热一次，标准组测 5 次，伸缩和压力组测 3 次；每轮随机化两个版本的先后顺序，串行运行。主时间包含分桶、建表、所有查询和内部内存管理，排除输入输出；初始化缓存的时间也计入。CPU 频率和后台负载未锁定，小幅差异不可视作跨机器保证。

## 保留的优化

1. 奇素数幂的整除检测用模 `2^32` 的逆元乘法与上界比较，已知整除的商用一次乘法；2 的幂使用移位，去掉热路径整数除法。
2. 32 位单位求逆使用 32 位余数、64 位有符号系数的扩展 Euclid；小奇模数按需缓存逆元，模数不超过 32 时使用微型乘法表。缓存每分量最多 256 KiB，乘法表最多 4 KiB，构造和清零计入求解时间。
3. 2 的幂的后缀运算使用 32 位回绕乘减与掩码；归一化的新槽/替换槽分开循环，已知主元坐标直接赋值，不再重复模运算。
4. 初始任务天然成堆。替换主元后，后继任务时间戳严格减小，只需堆根一次下滤；不再先弹出再压回。
5. 维护单位主元的满模证书：所有列均有单位主元时，其最小时间戳之前的区间可直接返回 YES。证书在单位主元写入后失效，下次查询才重算；缺秩数据不会误用此捷径。

插入任务的 `visits / reductions / writes / pops / max_pending` 与旧版逐项一致；查询捷径不计入这些插入计数。接口、支持范围和一般复杂度界不变。C++ 的机器整数优化仍未建立到 Lean 模型的源码精化关系。

## 标准组：native 与 O2

| 数据 | 旧 native ms | 新 native ms | 倍数 | 旧 O2 ms | 新 O2 ms | 倍数 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| binary-d64 | 36.39 | 25.68 | 1.42x | 37.36 | 25.32 | 1.48x |
| prime-d32 | 34.36 | 28.42 | 1.21x | 36.72 | 28.80 | 1.27x |
| square-d32 | 29.52 | 24.68 | 1.20x | 33.27 | 24.74 | 1.34x |
| deep-power-d24 | 173.24 | 149.03 | 1.16x | 184.17 | 147.06 | 1.25x |
| odd-power-d24 | 236.25 | 128.35 | 1.84x | 248.04 | 129.44 | 1.92x |
| crt-d32 | 66.18 | 46.85 | 1.41x | 71.81 | 46.24 | 1.55x |
| many-primes-d24 | 86.46 | 40.30 | 2.15x | 94.30 | 41.71 | 2.26x |
| word-boundary-d32 | 36.95 | 30.52 | 1.21x | 39.12 | 30.60 | 1.28x |
| composite-boundary-d24 | 69.30 | 37.55 | 1.85x | 76.89 | 39.04 | 1.97x |
| coupled-crt-d32 | 62.62 | 49.72 | 1.26x | 68.04 | 49.75 | 1.37x |
| nonunit-power-d24 | 157.08 | 131.07 | 1.20x | 172.21 | 131.98 | 1.30x |
| valuation-ladder-d24 | 11.71 | 9.94 | 1.18x | 13.82 | 11.70 | 1.18x |
| zeros-duplicates-d32 | 23.98 | 16.37 | 1.46x | 25.12 | 15.65 | 1.60x |

## 压力组

| Case | Before ms | After ms | Speedup | Peak RSS before / after MiB |
| --- | ---: | ---: | ---: | ---: |
| n100k-d64-square | 424.73 | 331.61 | 1.28x | 59.70 / 59.69 |
| n100k-deep-power | 4466.28 | 3670.41 | 1.22x | 35.31 / 35.31 |
| n100k-many-primes | 911.47 | 459.12 | 1.99x | 35.20 / 35.20 |
| q500k-square | 222.41 | 138.47 | 1.61x | 87.80 / 87.78 |
| dimension-128 | 252.73 | 187.83 | 1.35x | 23.12 / 23.12 |

## 参数伸缩

| Case | Before ms | After ms | Speedup | Peak RSS before / after MiB |
| --- | ---: | ---: | ---: | ---: |
| dimension-8 | 3.27 | 2.79 | 1.17x | 3.31 / 3.33 |
| dimension-16 | 6.51 | 5.12 | 1.27x | 4.03 / 4.05 |
| dimension-32 | 13.99 | 11.06 | 1.26x | 5.50 / 5.50 |
| dimension-64 | 39.82 | 28.09 | 1.42x | 8.47 / 8.47 |
| exponent-1 | 4.93 | 3.64 | 1.35x | 4.81 / 4.81 |
| exponent-2 | 9.78 | 7.99 | 1.23x | 4.81 / 4.81 |
| exponent-4 | 21.52 | 19.23 | 1.12x | 4.83 / 4.81 |
| exponent-8 | 50.58 | 45.59 | 1.11x | 4.84 / 4.83 |
| exponent-16 | 119.18 | 101.61 | 1.17x | 4.88 / 4.88 |
| exponent-30 | 239.31 | 205.18 | 1.17x | 4.92 / 4.91 |
| queries-1000 | 9.61 | 8.88 | 1.08x | 2.98 / 2.98 |
| queries-8000 | 11.56 | 9.90 | 1.17x | 4.19 / 4.19 |
| queries-64000 | 30.27 | 19.62 | 1.54x | 13.44 / 13.44 |
| length-1000 | 4.96 | 2.96 | 1.68x | 4.39 / 4.38 |
| length-64000 | 81.91 | 71.81 | 1.14x | 15.03 / 15.03 |
| components-2 | 11.16 | 7.36 | 1.52x | 4.83 / 4.81 |
| components-4 | 25.10 | 14.27 | 1.76x | 4.83 / 4.83 |
| components-8 | 57.93 | 26.77 | 2.16x | 4.84 / 4.83 |

## 验证与记录

native、O2、UBSan 三种构建各通过 **2,741,761 次**独立成员判定断言，涵盖穷举、整数格 oracle、Python 参考实现和输入边界。新增算术回归覆盖最大维度 256、`2^31`、`3^20`、`5^13`、`65521^2`、近 `2^32` 素数、小模数乘法表、满模证书失效及任务计数。UBSan 未报告未定义行为。

全部计时运行均核对完整输出的 SHA-256、五项插入计数和每组 8 个独立格 oracle 探针。原始 JSON 含每次耗时、整程序耗时、RSS、输入/二进制/源码指纹与数据参数。ASan 在此前环境中无法正常启动，本轮未声称有 ASan 覆盖。

原 36 组横向结果继续保留为历史快照；不能将本轮新计时直接除以前一轮 Howell 的计时来声称新的跨算法加速比。

## 复现

从成果目录执行，以下以 native 标准组为例：

```sh
mkdir -p build/constant-tuning/baseline
git show 9a0fb9e:results/composite-modulus-basis/implementation/benchmark_cpp/main.cpp > build/constant-tuning/baseline/main.cpp
git show 9a0fb9e:results/composite-modulus-basis/implementation/benchmark_cpp/algorithms.hpp > build/constant-tuning/baseline/algorithms.hpp
clang++ -std=c++17 -O3 -DNDEBUG -march=native -Wall -Wextra build/constant-tuning/baseline/main.cpp -o build/constant-tuning/before
clang++ -std=c++17 -O3 -DNDEBUG -march=native -Wall -Wextra implementation/benchmark_cpp/main.cpp -o build/constant-tuning/after
python3 implementation/benchmark_cpp/verify.py --binary build/constant-tuning/after
python3 implementation/benchmark_cpp/compare_versions.py --before build/constant-tuning/before --after build/constant-tuning/after --profile standard --repeats 5 --before-label 9a0fb9e --build-flags='-std=c++17 -O3 -DNDEBUG -march=native -Wall -Wextra' --output build/constant-tuning/reproduced-standard.json
```

将 `--profile` 改为 `scaling` / `stress`，相应设置 `--repeats 3` 和新的输出路径；O2 对照需将两个二进制都改用 `-O2 -DNDEBUG` 编译，并同步 `--build-flags`。完整 O2 正确性门可运行 `make cpp-test`。输出文件必须尚不存在。

- [Native standard](../../artifacts/cpp-benchmark/constant-tuning/standard.json)
- [O2 standard](../../artifacts/cpp-benchmark/constant-tuning/standard-o2.json)
- [Scaling](../../artifacts/cpp-benchmark/constant-tuning/scaling.json)
- [Stress](../../artifacts/cpp-benchmark/constant-tuning/stress.json)
- [Native verification](../../artifacts/cpp-benchmark/constant-tuning/verification.txt)
- [O2 verification](../../artifacts/cpp-benchmark/constant-tuning/verification-o2.txt)
- [UBSan verification](../../artifacts/cpp-benchmark/constant-tuning/verification-ubsan.txt)
- [UBSan arithmetic](../../artifacts/cpp-benchmark/constant-tuning/arithmetic-ubsan.txt)
- [Build provenance](../../artifacts/cpp-benchmark/constant-tuning/provenance.json)
