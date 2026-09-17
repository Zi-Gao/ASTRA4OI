# 论文—Lean 4 证明对照

本文件由 `formal/sync_paper.py` 从 `paper/theorem-map.json` 生成，声明源链接和论文编号自动同步。

“机器证明”表示对应数学声明已被 Lean 检查；“仅事件计数”表示实现成本契约仍由文字分析给出。

| 论文 | 结论 | 范围 | Lean 声明 |
|---|---|---|---|
| 定义 1 (`def:interval`) | 区间子模与下标桥接 | 机器证明 | [`Paper.intervalSpan`](../../formal/LeanVerification/Paper.lean#L16)<br>[`Paper.prefixSource_span`](../../formal/LeanVerification/Paper.lean#L34)<br>[`Paper.compositePrefix_span`](../../formal/LeanVerification/Paper.lean#L93) |
| 定义 2 (`def:lead`) | 首项和规范行 | 机器证明 | [`PadicEchelon.HasLead`](../../formal/LeanVerification/PadicEchelon.lean#L131)<br>[`PadicEchelon.PivotRow`](../../formal/LeanVerification/PadicEchelon.lean#L60) |
| 定义 3 (`def:digit`) | 数字基的基数刻画 | 机器证明 | [`DigitCardinality.CardinalBasis`](../../formal/LeanVerification/DigitCardinality.lean#L131)<br>[`DigitCardinality.CardinalBasis.mem_iff_digitRep`](../../formal/LeanVerification/DigitCardinality.lean#L165) |
| 引理 1 (`lem:digits`) | 数字表示单射 | 机器证明 | [`DigitCardinality.encode_injective`](../../formal/LeanVerification/DigitCardinality.lean#L111)<br>[`DigitCardinality.card_range_encode`](../../formal/LeanVerification/DigitCardinality.lean#L119) |
| 引理 2 (`lem:query`) | 查询存在性与双向正确性 | 机器证明 | [`BasisQuery.exists_correct_answer`](../../formal/LeanVerification/BasisQuery.lean#L382)<br>[`BasisQuery.Derivation.correct`](../../formal/LeanVerification/BasisQuery.lean#L277) |
| 引理 3 (`lem:order`) | 商群阶与幂层 | 机器证明 | [`CyclicQuotient.exists_quotient_order_exponent`](../../formal/LeanVerification/CyclicQuotient.lean#L62)<br>[`CyclicQuotient.nsmul_pow_ne_zero_iff`](../../formal/LeanVerification/CyclicQuotient.lean#L68)<br>[`CyclicQuotient.quotient_exponent_anti`](../../formal/LeanVerification/CyclicQuotient.lean#L50) |
| 引理 4 (`lem:coset`) | 缺槽首项及乘 p 的推进 | 机器证明 | [`BasisQuery.Basis.missing_coset_lead_unique`](../../formal/LeanVerification/BasisQuery.lean#L54)<br>[`BasisQuery.Derivation.p_nsmul_final_strictly_later`](../../formal/LeanVerification/BasisQuery.lean#L249) |
| 引理 5 (`lem:extension`) | 循环扩张与层间不碰撞 | 机器证明 | [`ArbitraryExtension.basisFromSettledLayers`](../../formal/LeanVerification/ArbitraryExtension.lean#L212)<br>[`CyclicExtension.no_same_slot_of_missing_layers`](../../formal/LeanVerification/CyclicExtension.lean#L377) |
| 引理 6 (`lem:terminal`) | 终态提取后缀数字基 | 机器证明 | [`TerminalExtraction.drained_table_correct`](../../formal/LeanVerification/TerminalExtraction.lean#L314) |
| 引理 7 (`lem:operational`) | 必要键保持和同时间碰撞排除 | 机器证明 | [`FastAppend.initial_protected`](../../formal/LeanVerification/FastAppend.lean#L116)<br>[`FastInvariant.scan_preservesKeysAndProtected`](../../formal/LeanVerification/FastInvariant.lean#L78)<br>[`PrioritySafety.same_timestamp_collision_impossible`](../../formal/LeanVerification/PrioritySafety.lean#L181) |
| 引理 8 (`lem:budget`) | 合法终止、列预算与队列大小 | 机器证明 | [`Totality.appendResult_nonempty`](../../formal/LeanVerification/Totality.lean#L472)<br>[`WorklistComplexity.insertion_visits_le`](../../formal/LeanVerification/WorklistComplexity.lean#L118)<br>[`WorklistComplexity.insertion_pops_le`](../../formal/LeanVerification/WorklistComplexity.lean#L123)<br>[`WorklistComplexity.insertion_queue_lengths_le`](../../formal/LeanVerification/WorklistComplexity.lean#L130) |
| 定理 1 (`thm:prime`) | 素数幂区间主定理 | 机器证明 | [`Paper.theorem_1_prime_power`](../../formal/LeanVerification/Paper.lean#L57) |
| 推论 1 (`cor:card`) | 区间子模大小 | 机器证明 | [`TimestampedBasis.CorrectTable.card_at`](../../formal/LeanVerification/TimestampedBasis.lean#L426)<br>[`Paper.prefixSource_span`](../../formal/LeanVerification/Paper.lean#L34) |
| 定理 2 (`thm:crt`) | CRT 区间查询及预处理 | 机器证明 | [`Paper.theorem_2_composite_interval`](../../formal/LeanVerification/Paper.lean#L123)<br>[`Paper.theorem_2_composite_preprocessing`](../../formal/LeanVerification/Paper.lean#L140) |
| 命题 1 (`prop:cost`) | 完整实现成本模型 | 仅事件计数 | [`VerifiedScan.Drain.initial_operational_bounds`](../../formal/LeanVerification/VerifiedScan.lean#L425)<br>[`WorklistComplexity.insertion_heap_comparisons_le`](../../formal/LeanVerification/WorklistComplexity.lean#L142) |
