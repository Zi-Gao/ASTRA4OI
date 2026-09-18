# C++ 标准化性能对照

[English](README-EN.md) · [成果入口](../../README.md)

**[已完成的性能实测汇总](../../docs/zh/cpp-benchmark-results.md)**：36 组数据、O2/native 对照、原始重复计时与资源失败记录。

面向 OI/CP 的静态区间成员查询：各实现读取完全相同的输入，允许离线重排询问，按原顺序输出答案。范围为 `2 <= m < 2^32`、`1 <= d <= 256`。普通乘法使用 64 位中间值；优化版倒数约减和独立基线的 Bezout 组合使用编译器的 `__int128`。支持 Clang/GCC 的 macOS/Linux 环境，Python 3.10+，无需第三方包。

## 比较哪些实现

| 名称 | 实现 | 范围/定位 |
| --- | --- | --- |
| `timestamp-basic` | STL 优先队列、独立行对象、完整行更新、整数取模 | 本文算法的普通 C++ 版 |
| `timestamp-fast` | 平铺主元表、k 个可复用任务缓冲、原地后缀更新、精确倒数约减；2 的幂用掩码、ctz 和 Newton 单位求逆 | 本文算法的优化版；不是“已达到硬件极限”的保证 |
| `closure-prototype` | 每次写主元都显式加入 p 倍行的 FIFO 闭包 | 本项目历史原型的 C++ 移植，属于消融对照，不是外部文献基线 |
| `howell-rebuild` | 每个区间重建饱和阶梯生成集 | 无需因数分解 |
| `howell-segment` | 线段树保存并合并饱和阶梯摘要 | 无需因数分解 |
| `howell-sparse` | 倍增表保存摘要，查询合并两个可重叠块 | 无需因数分解 |
| `field-timestamp` | 独立实现的域上时间戳基，无幂层或任务队列，使用同一优化模算术 | 仅素数模数 |
| `xor-packed` | 64 位打包的异或时间戳基 | 仅模 2、d≤64；用于显示专用表示的实际优势 |

三种 Howell 风格方案共享一个本地编写的、含零化闭包的三角生成集内核，并非调用成熟正规形库，也没有实现快速矩阵乘法；不声称它们代表该路线的最快实现。内核不强制约化主元上方元素，因此称“饱和阶梯 / Howell 风格”，不把输出宣称为规范 Howell form。它们在确认生成整个自由模后允许提前结束，且在 2 的幂模数下的单位主元步骤也使用同一 Newton 求逆，避免刻意削弱基线。

来源与设计依据：[Howell 模线性代数算法](https://cs.uwaterloo.ca/~astorjoh/esa.pdf)、[Howellize 的零化闭包伪代码](https://research.cs.wisc.edu/wpis/papers/TR1792-R1.pdf)、[域上时间戳算法的一手说明](https://www.cnblogs.com/Xun-Xiaoyao/p/17275653.html)。这里是根据算法原理独立编写的实现；线段树/倍增表包装为本项目构造，未将其归为原论文已有的区间结论。

## 正确性先于计时

`verify.py` 对每个适用候选执行：小参数完整序列/区间/目标穷举；随机数据与独立整数格 oracle 对拍；Python 参考程序对照；负数及非规范代表元；模数接近 `2^32`、深幂层、耦合低秩、零行、重复行、空查询和打包最高位测试。普通与优化时间戳版还必须具有相同的任务计数，并满足主体操作上界。

`arithmetic_test.cpp` 把优化算术与原生 `%`、gcd/逆元性质对比，覆盖满 64 位被除数和 32 位边界。比较使用显式失败分支，不受 `-DNDEBUG` 影响。

性能数据另作八个固定短区间的整数格 oracle 检查；所有奇数编号目标均由区间内向量构造，所以必为 YES；coupled/nonunit 数据的偶数编号目标必为 NO。所有完整输出使用 SHA-256 交叉比对，不只比较 YES 数量。测试不能替代源码形式化；C++ 和 Howell 风格基线没有纳入现有 Lean 证明。

## 标准测量口径

- 同一进程一次处理一个候选与一份数据。全部候选使用同一编译器和编译选项。
- 主指标 `solve_seconds` 包括建结构、离线分桶、全部查询、内部内存分配与释放；排除数据生成、读入、答案输出和 oracle。
- `program_seconds` 包含解析、已给分解的校验、求解与输出。runner 墙钟另计，受每 100 ms 的资源监测粒度影响，不用于短程序的精确排名。
- 报告中位数、最小/最大值及原始每轮记录；默认一次预热、五次测量。每轮使用固定种子打乱算法顺序，串行执行，不并发跑性能候选。
- RSS 为整个进程的内存高水位，包括输入与答案，不冒充数据结构独占空间。资源预算按墙钟和 RSS 执行；RSS 采样可能短时超限，结束后再检查高水位。
- 超时/超内存/不适用都保留，不填造耗时，不用超时阈值算“准确加速倍数”。出现错误答案立即停止。
- 本测试允许离线处理。时间戳版没有保存每个历史前缀，因此结果不能用于声称历史在线版本也使用同样内存。
- 时间戳方案已知分解，Howell 方案不接收分解；不测分解算法。普通版与优化版都保留轻量操作计数。

`portable` 为 `-O2 -DNDEBUG`；`native` 为 `-O3 -DNDEBUG -march=native`，对所有候选同样生效。`sanitize` 用于地址/未定义行为检查，`ubsan` 仅检查未定义行为，均不能与发布版耗时混排。未绑定 CPU、锁频或关闭其他程序；发布前建议在安静机器复跑，保留硬件环境和原始数据。

本机 Apple Clang 17 的 AddressSanitizer 在 macOS 26.6.2 上启动前死锁，未获得 ASan 覆盖，见 [实际失败记录](../../artifacts/cpp-benchmark/sanitizer-smoke/validation-failure.txt)。UBSan 独立配置的小规模全流程见 [检查报告](../../artifacts/cpp-benchmark/ubsan-final/report.md)。检查构建的耗时只用于诊断，不进入正式性能结论。

## 数据矩阵与运行

`smoke`：小规模全流程；`standard`：模 2、素数、p²、深素数幂、奇素数幂、多素因子、32 位边界及四类结构化输入；`scaling`：分别改变 n、d、k、w、q；`stress`：n=100000、q=500000 或 d=128 的资源上限测试。

区间混合单点、短区间、约 d/2d 长度和任意长度；目标不全部取随机值，以免满秩长区间使答案退化为全 YES。分布、区间长度直方图和答案比例均随报告保存。`valuation-ladder` 是结构化压力输入，不宣称已证明为最坏情况。

从成果根目录运行：

```sh
make cpp-test
make benchmark-cpp
make benchmark-cpp-native
make benchmark-cpp-stress
python3 implementation/benchmark_cpp/run.py --profile scaling --tuning native
```

自定义预算与候选：

```sh
python3 implementation/benchmark_cpp/run.py --profile standard --tuning native --repeats 5 --timeout 10 --memory-mib 512
python3 implementation/benchmark_cpp/run.py --profile stress --tuning native --cases n100k-d64-square --repeats 3
python3 implementation/benchmark_cpp/run.py --profile smoke --tuning sanitize --repeats 1 --warmups 0 --quick-verification
```

`--algorithms timestamp-basic,timestamp-fast,howell-segment` 可限制候选，`--seed` 可换数据种子。`CXX=clang++` 或 `CXX=g++` 选择编译器。默认每次新建带 UTC 时间的结果目录；`--output` 指定目录，已有结果不会被静默覆盖。

中断后可用原命令和原 `--output`，追加 `--resume`。它保留完整场景、从头重跑未完成场景，核对实现/数据生成器指纹、设置、编译器和硬件，并保存中断记录。不要同时对同一目录启动多个运行进程。

报告位于 `artifacts/cpp-benchmark/`，包含 Markdown、JSON 原始测量、独立验证日志、源文件 SHA-256、编译环境、数据文件 SHA-256 及复现命令。大输入由固定种子重建，成功测试后删除；二进制及临时文件位于忽略提交的 `build/`。

单独运行 C++（输入格式与 Python 程序相同）：

```sh
build/cpp-benchmark/bench --algorithm timestamp-fast --factors 2:2 < implementation/examples/example.in
build/cpp-benchmark/bench --algorithm howell-segment < implementation/examples/example.in
```

实际 `--factors` 必须匹配输入头中的模数。答案写 stdout，单行 JSON 指标写 stderr。不要把 stdout 与 stderr 合并后再当作题目答案。
