# 参考程序使用说明

[English](../en/usage.md) · [工件入口](../../README.md)

Python 3.10+，仅使用标准库。以下命令从成果根目录执行：

```sh
python3 implementation/solver.py < implementation/examples/example.in
python3 implementation/solver.py --online < implementation/examples/example.in
python3 implementation/solver.py --factors 2:2 < implementation/examples/example.in
```

## 输入与输出

```text
n d m q
a_1 的 d 个坐标
...
a_n 的 d 个坐标
l r x_1 ... x_d          # 共 q 条查询
```

要求 `n,d,m ≥ 1`、`q ≥ 0`、`1 ≤ l ≤ r ≤ n`。下标从 1 开始，区间两端包含。
坐标是整数，可以为负或超出模数范围；程序先规范化。每条查询输出 `YES` 或 `NO`。
样例见 [example.in](../../implementation/examples/example.in) 和 [example.out](../../implementation/examples/example.out)。

大模数应显式给出素因子分解，例如 `--factors 998244353:2,1000000007:2`，并使输入模数等于其乘积。
程序验证乘积、正性和不同底数，**调用者保证底数为素数**。
未给分解时使用试除，最坏 `O(sqrt(m))` 次试除，不适合大整数分解。

## Python API

在 `implementation/` 中启动 Python，或将该目录加入模块搜索路径：

```python
from solver import RangeBasis, solve_offline

basis = RangeBasis(4, 2, factors=[(2, 2)])
basis.append((2, 1))
assert basis.contains(1, 1, (0, 2))
assert basis.span_size(1, 1) == 4
basis.append((0, 2))
assert not basis.contains(2, 2, (2, 1))
assert basis.contains(1, 1, (0, 2))

assert solve_offline([(2, 1), (0, 2)], 4,
                     [(1, 1, (0, 2)), (2, 2, (2, 1))]) == [True, False]
```

`RangeBasis` 支持追加和已有历史区间查询，保存不可变行的前缀快照；不支持中间修改或删除。
它的空间为 `O(nKd²)`。`solve_offline` 按右端点分桶，只保存当前基，基结构空间为 `O(Kd²)`，
另计输入、查询和输出。`span_size` 需 `O(dK)` 次槽位检查以及幂运算和整数位成本，
不享有成员查询的复杂度界。

## 验证入口

```sh
make test                 # 全部程序测试
make test-large           # 大模数独立测试
make formal               # 一般证明、公理审计、有限回归
make paper                # 编译两种语言的论文
make check                # 定理对照与文档一致性
make benchmark            # 性能样例
```

正式程序是 [solver.py](../../implementation/solver.py)。历史原型保留在
[experiments/](../../implementation/experiments/)，不能作为正式 API 或复杂度保证的替代。
