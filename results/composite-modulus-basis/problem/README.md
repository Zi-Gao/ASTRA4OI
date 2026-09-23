# OI 题包：区间生成子模

这是“合数模数下的区间生成子模成员查询”的可复现 OI 模板题包。题包与论文、形式化证明及性能基准隔离，正式输入接口仍沿用 `n d m q`。

## 内容

- `statement.md`：中文题面与子任务；
- `solution.md`：OI 风格题解、正确性与复杂度；
- `problem.json`：本仓库的可移植题目配置；
- `std.cpp`：GNU C++17 可读标程；
- `brute.cpp`：小状态空间的独立闭包暴力；
- `gen.py`：固定种子的正式数据生成器；
- `validator.py`：总限制及各子任务校验；
- `verify.py`：重生成、哈希、标程、暴力和随机对拍门禁；
- `solutions/`：时间戳、显式闭包、Howell 与子任务专用做法；
- `benchmark_solutions.py`：统一编译、正式数据测评和对比报告生成器；
- `data/`：19 个输入/答案文件及 `manifest.json`；
- `examples/`：题面样例。

仓库此前没有绑定某个评测系统的配置格式，因此 `problem.json` 明确使用项目自有的 `astra4oi.problem.v1` schema。接入具体 OJ 时只需映射时空限制、token checker、子任务和数据文件，不需要修改题意或程序。

## 复现

从上一级成果目录执行：

```sh
make problem-data
make problem-check
make problem-compare
```

快速检查或 UBSan 检查：

```sh
python3 problem/verify.py --quick --skip-regeneration
python3 problem/verify.py --quick --sanitize --skip-regeneration
```

`make problem-data` 会确定性重建 `data/`。每个正式文件的输入与答案 SHA-256、种子、参数和 YES/NO 数量均记录在 manifest 中。
多做法测评结果见 [`artifacts/solution-comparison.md`](artifacts/solution-comparison.md)，原始逐点记录见同目录 JSON。

## 答案的独立性

正式答案不由 `std.cpp` 生成：

- 正例直接由区间内行的线性组合构造；
- 一维数据用区间 gcd 判定；
- 对角理想数据使用已知可逆坐标变换和逐轴 gcd；
- 局部任意行数据在某个素域投影中构造严格不属于区间张成的反例；
- 耦合与非单位数据使用显式线性不变量构造反例。

验证脚本再让 C++ 标程核对所有正式答案，并用状态闭包暴力对拍小数据和 100 组随机实例。形式化证明验证抽象算法，不等于对 `std.cpp` 的源码精化证明；两者的信任边界仍然分开。
