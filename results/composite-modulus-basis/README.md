# 合数模数下的区间生成子模成员查询

[English](README-EN.md)

本目录按研究论文与可复现工件组织。中文论文为主稿，英文稿保持相同定义、引理和定理编号。
核心结果是带时间标记的 p-进阶梯表；数学正确性与操作计数有一般性 Lean 4 证明。

## 论文与证明

- **[中文论文 PDF](paper/output/pdf/paper-zh.pdf)** / [英文论文 PDF](paper/output/pdf/paper-en.pdf)
- [中文 LaTeX 源码](paper/main-zh.tex) / [英文 LaTeX 源码](paper/main-en.tex)
- **[论文—Lean 逐条对照](docs/zh/proof-map.md)** / [直接按区间下标陈述的 Lean 主定理](formal/LeanVerification/Paper.lean)
- [形式化范围与信任边界](docs/zh/formalization.md)
- [新颖性核查与已有工作对照（2026-09-17）](docs/zh/novelty-audit.md)
- [C++ 实现与标准化性能对照](implementation/benchmark_cpp/README.md)
- **[OI/CP 性能实测汇总](docs/zh/cpp-benchmark-results.md)**（普通/优化 C++、8 种候选、36 组数据）

对已知分解 `m = ∏ p_s^k_s`，记 `K = ∑ k_s`、`w` 为分量数。
主体坐标更新量为预处理 `O(nKd²)`、每次成员查询 `O(wd²)`。
求逆、赋值、堆、因数分解与整数位成本另计；论文严格区分这些成本模型。

## 目录

```text
paper/           中英文论文、参考文献、定理映射及 PDF
formal/          Lean 工程、论文主定理、声明审计
implementation/  参考程序、测试、性能样例、输入输出样例
  experiments/   历史原型，只作补充对照
  tests/         独立整数格 oracle 和大模数测试
docs/zh/         中文使用、验证、测试、扩展及历史说明
docs/en/         对应英文说明
artifacts/       实际测试、构建与性能日志
```

## 复现

Python 3.10+，参考程序及测试只用标准库。从本目录执行：

```sh
python3 implementation/solver.py < implementation/examples/example.in
make test
make formal
make paper
make check
```

- Lean 首次安装与依赖缓存：[形式化说明](docs/zh/formalization.md)。
- PDF 需要含 `ctex`、Fandol 字体和 `latexmk` 的 TeX Live/XeLaTeX。
- [程序接口与输入契约](docs/zh/usage.md) · [测试覆盖](docs/zh/testing.md) · [补充数学说明](docs/zh/extensions.md)

Python 参考程序测试包含最大为 **2,147,483,647** 的质数、`2^64`、`(10^9+7)^3` 和 **120 位 CRT 模数**，
同时覆盖 YES、NO、历史版本与操作上界。实测日志位于 [artifacts/](artifacts/)。
形式化验证不等于 Python 源码精化，也不表示论文已通过外部同行评审。

C++ 性能工件另以 **32 位模数**为范围，包含普通/优化时间戳实现、Howell 风格区间基线和域专用对照；
见上方 C++ 文档。现有 Lean 数学证明没有验证 C++ 源码或实际运行时间。
