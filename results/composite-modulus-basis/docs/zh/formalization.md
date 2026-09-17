# 论文与 Lean 4 形式化

[English](../en/formalization.md) · [工件入口](../../README.md) · [逐条对照表](proof-map.md)

## 机器检查覆盖什么

论文有 15 个带编号的定义、引理、定理、推论和成本命题，映射到 32 个 Lean 声明。
[theorem-map.json](../../paper/theorem-map.json) 是对照信息的唯一来源；
[同步程序](../../formal/sync_paper.py) 生成两种语言的 Markdown 表、论文 LaTeX 表和
[Audit.lean](../../formal/Audit.lean)。`--check` 检测编号、声明源位置和生成文件是否漂移。

[Paper.lean](../../formal/LeanVerification/Paper.lean) 不只重命名已有定理：

- `intervalSpan` 直接用原序列的一基、闭区间下标定义生成子模。
- `prefixSource_span` 和 `compositePrefix_span` 证明它等于前缀表所使用的时间阈值语义。
- `theorem_1_prime_power` 同时给出前缀构造、最多 `dk` 行、`3rkd²` 初始幂链与消元更新额度，
  以及每个区间的正确答案和至多 `d` 次查询消元。
- `theorem_2_composite_interval` 和 `theorem_2_composite_preprocessing` 给出字面区间的 CRT 结论及合并计数。

底层证明覆盖数字组合单射、由基数得到完备性、循环商群阶、缺槽首项、必要幂层保持、
同时间碰撞排除和插入终止性。构造从空表开始，没有把“算法已经成功执行”作为主定理前提。

## 成本模型边界

一次替换有归一化和旧余量两遍行操作，故消元阶段至多 `2kd²` 个坐标更新。
一次输入规范化和至多 `k-1` 次逐行乘 p 另预留 `kd`，正维度时合计至多 `3kd²`。
Lean 证明的是这些代数/组合计数。论文完整实现成本命题被明确标成“仅事件计数已机器验证”：
数组寻址、二叉堆、求逆和赋值子程序的具体成本依赖文字说明中的实现契约。

Lean 的数学构造使用列表、关系式执行和选择公理；不声称其编译产物具有参考数组/堆实现的运行时间。
Python 源码精化、字节级分配、完整整数位复杂度与一般有限环补充归约不在机器证明范围内。

## 构建与审计

安装 [elan](https://github.com/leanprover/elan)，首次从成果根目录执行：

```sh
cd formal
lake exe cache get
cd ..
make formal
```

工具链固定为 Lean 4.32.0，Mathlib 固定为 v4.32.0，依赖提交见
[lake-manifest.json](../../formal/lake-manifest.json)。首次下载需要网络和数 GB 磁盘。

```sh
make core                         # 一般证明和 32 声明公理审计
make formal                       # 另加可选有限模型回归
python3 formal/sync_paper.py --check
```

所有映射声明的传递公理只能属于 `propext`、`Classical.choice`、`Quot.sound`。
审计会拒绝 `sorryAx`、有限原生求值公理或其他未允许公理。没有公理依赖的声明也被显式识别。
默认 [LeanVerification.lean](../../formal/LeanVerification.lean) 导入全部一般证明，包括新的论文入口。

## 有限模型的角色

[LeanRegression.lean](../../formal/LeanRegression.lean) 用 `native_decide` 检查模 4、8、9 及
CRT 模 6、12 的 83,598 次成员比较，另有两个回归反例。
它是可选的独立有限模型，未被默认一般证明入口导入，不能替代任意参数上的证明。

实际输出保存在 [artifacts/lean.txt](../../artifacts/lean.txt)。
