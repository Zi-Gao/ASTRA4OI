# 历史实验原型

[English](README-EN.md) · [正式实现](../solver.py)

- `explicit_closure.py`：每次写入主元后显式加入 p 倍行，作为补充交叉验证。
- `fast_prototype.py`：快速算法的早期探索版本，供追溯使用。

从 `implementation/` 目录执行：

```sh
python3 -m experiments.explicit_closure
python3 -m experiments.fast_prototype
```

它们不是正式 API，也不承担 `O(nkd²)` 的保证。正式接口、错误检查及最新测试以
[README.md](../../docs/zh/usage.md) 和 [TESTING.md](../../docs/zh/testing.md) 为准。
