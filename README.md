# ASTRA4OI

ASTRA4OI 是一个面向 OI/算法研究成果的多成果仓库。每个成果都放在独立的子目录中，保留自己的说明、实现、测试和实验记录，避免不同研究内容互相污染。

## 目录约定

```text
ASTRA4OI/
├── README.md
├── docs/                         # 仓库级说明与发布材料
├── scripts/                      # 跨成果的辅助脚本
└── results/
    ├── composite-modulus-basis/
    └── <another-result>/
```

每个 `results/<name>/` 都应尽量做到自包含，并至少包含：

- `README.md`：问题、结论、运行方式和适用边界；
- 实现文件；
- 测试或验证脚本；
- 可复现实验的输入、输出和结果记录。

## 当前成果

- [composite-modulus-basis](results/composite-modulus-basis/)：合数模线性基的快速区间查询，包含 p-进阶梯表算法、证明、Python 实现、穷举验证和性能样例。

配套社区文章：[合数模下的区间线性基：带时间标记的 p-进阶梯表](docs/luogu-composite-modulus-basis.md)。本文明确标注该算法成果由 GPT-6-ASTRA 完成。

运行当前成果的基本验证：

```sh
cd results/composite-modulus-basis
python3 test_solver.py
python3 solver.py < example.in
python3 solver.py --online < example.in
```

## 新增成果

新增研究成果时，请在 `results/` 下建立新的、语义清晰的子目录，不要把成果文件直接放到仓库根目录。成果之间应避免通过相对路径依赖彼此的内部文件；如需共享工具，放入 `scripts/` 或单独的仓库级公共模块。
