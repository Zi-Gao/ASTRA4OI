# Novelty audit (2026-09-17)

[中文](../zh/novelty-audit.md) · [Artifact entry](../../README-EN.md)

Scope: the manuscript, algorithm, and formalization boundaries at repository commit `c2e93474e8f678a4cbf511887cb616ae593be5a6`. This is a targeted literature audit, not a priority certificate or peer review. The manuscript theorems, executable, and generated PDFs were not changed.

## 1. Conclusion and strength of evidence

**A combined algorithmic contribution remains plausible, but composite-modulus membership, digit bases, and timestamped linear bases are not individually new.**

The sources searched and inspected did not reveal an external result combining append-only vectors over `Z/(p^k)`, one timestamped table for all suffix-generated submodules, and at most `k` nonbranching task chains yielding `O(kd²)` dominant updates and `O(d²)` queries. This is a bounded negative search result, not evidence of nonexistence.

The defensible candidate is the complete maintenance algorithm: quotient identities, protected levels, maximum-timestamp scheduling, collision exclusion, and the nonbranching bound in the presence of zero divisors. Individual elementary lemmas should not each be presented as discoveries.

## 2. Closest prior work

| Source and inspected location | Established overlap | Implication |
| --- | --- | --- |
| [S1: Storjohann–Mulders, ESA 1998](https://cs.uwaterloo.ca/~astorjoh/esa.pdf), §§2–5, especially Task 5 | Howell forms support static membership in `O(d²)` basic operations after preprocessing, without supplied prime factorization. Basic operations include gcd-related primitives. | Neither modular elimination nor quadratic membership alone is novel. Compare interval maintenance and cost models. |
| [S2: Kuijper–Schindelar](https://arxiv.org/pdf/0906.4602), Definition 4.9, Theorems 4.10/4.12; 2009 preprint, 2011 journal publication | Order differences determine expansions into p-power multiples, producing p-bases with a predictable leading monomial property over `Z/(p^k)[x]`. | Very close algebraic precedent; it does not supply the present append-only suffix structure. |
| [S3: Kuijper–Pinto](https://arxiv.org/pdf/0801.3703), §II | p-linear combinations, p-generator sequences, and p-bases, with earlier references. | Relate the manuscript's leading-slot definition to established terminology. |
| [S4: Xun_Xiaoyao, 2023-03-31](https://www.cnblogs.com/Xun-Xiaoyao/p/17275653.html), insertion code and online extension | Public `F₂` implementation of newer-timestamp replacement, threshold filtering, and prefix copies. | Timestamping and historical versions are precedents. This first-hand technical implementation is not a scholarly priority claim; packed-XOR costs differ from dense-vector costs. |
| [S5: Elder et al., Abstract Domains of Affine Relations](https://research.cs.wisc.edu/wpis/papers/TR1792-R1.pdf), Algorithm 1, Lemma 2.3, Corollary 2.4 | Howellize handles annihilator consequences over `Z/(2^w)` and bounds strict append-generated chains by `wd`. | Closure and finite-height arguments have precedents. Coordinate-suffix projection there differs from suffixes of source generators here. |
| [S6: Feng–Nóbrega–Kschischang–Silva, 2013](https://arxiv.org/html/1304.2523), §IV | Finite-chain-ring row canonical forms, linked to Howell forms, p-bases, and earlier work. | A broad claim of extending field elimination to chain rings is inappropriate. |

Three adjacent directions require careful separation:

- [S7: Francis–Verron, 2018/2019](https://arxiv.org/abs/1802.01388) concerns signature-based Gröbner computations over integral domains/PIDs. Source labels invite comparison with `(t,e)`, but the inspected abstract does not cover the zero-divisor case here.
- [S8: Near Optimal Linear Algebra in the Online and Sliding Window Models](https://arxiv.org/abs/1805.03765) studies numerical approximation, sampling, and embeddings, according to its abstract; it is not evidence of the same exact modular problem.
- [S9: Divasón's Isabelle/HOL Smith-normal-form development, 2020](https://isa-afp.org/entries/Smith_Normal_Form.html) establishes prior formal verification of matrix normal forms. Claim the specific interval algorithm and counts verified here, not broad priority for verified modular algebra.

Howell's original publication is [Spans in the module (Z_m)^s, 1986](https://www.tandfonline.com/doi/abs/10.1080/03081088608817705). Its metadata/abstract were checked; algorithmic conclusions rely on accessible S1. S3 also cites Vazirani–Saran–Rajan (1996) on minimal trellises for finite abelian group codes. The author-hosted full text could not be opened in this audit, so this remains a backward-reference lead rather than evidence of coverage.

## 3. Assessment of individual contributions

| Component | Assessment | Action |
| --- | --- | --- |
| CRT, static membership, annihilator closure | Established tools | Background, with S1/S5 citations |
| Digit bases, power expansion, predictable leads | Close to p-basis / p-PLM theory | Add S2 and distinguish definitions |
| Field timestamps and prefix copies | Public precedent | Cite S4; explain the `k=1` specialization |
| Cyclic quotient order `p^h` and cardinality multiplication | Standard algebra | Proof ingredients, not standalone novelty |
| `(t,e)` identities and protected levels for every suffix | Candidate contribution | State the simultaneous invariant explicitly |
| Priority scheduling, collision exclusion, one successor per displacement | Strongest candidate | Explain what is required beyond composing known static tools |
| Combined preprocessing/query bounds | Candidate data-structure result | Compare actual interval baselines; no optimality claim |
| Lean interval semantics, termination, and event counts | Specific artifact contribution | Preserve the Python refinement boundary |

p-adic expansion is not automatically `F_p` linearization: `1+1=2` modulo 4 produces a carry. A proposed reduction to an ordinary `kd`-dimensional field basis needs a proof that the intended operations are preserved, not merely a dimension count.

## 4. Interval baselines derived in this audit

These are **our deductions** from mergeable normal-form summaries, not interval theorems attributed to S1. Let `C(d)` normalize at most `2d` generators of dimension d. A classical bound is `O(d³)` basic operations; a suitable fast implementation permits discussion of `O(d^ω)`. Each summary has at most d rows and `O(d²)` ring elements.

The construction uses `span(A ∪ B) = span(H(A) ∪ H(B))`: stack two summaries and normalize.

| Method | Preprocessing upper bound | Interval-query upper bound | Summary space | Supplied factorization |
| --- | --- | --- | --- | --- |
| Rebuild a length-L interval | None | Classical `O(d² max(L,d))` | Temporary `O(Ld+d²)` | No |
| Segment tree of normal forms | `O(nC(d))` | `O(C(d) log(n+1)+d²)` | `O(nd²)` | No |
| Sparse table of normal forms | `O(nC(d) log(n+1))` | `O(C(d)+d²)` | `O(nd² log(n+1))` | No |
| Present historical-prefix tables | `O(nKd²)` dominant coordinate updates | `O(wd²)` dominant coordinate updates | `O(nKd²)` | Yes |

For a sparse-table query, choose the two length-`2^floor(log₂ L)` blocks covering the interval. Their overlap is harmless because repeated generators do not change a span. Their summaries must be merged; OR/AND of separate membership answers is incorrect. The segment-tree bound recompresses the accumulating summary after each merge.

These are conservative upper bounds, not claims about the best possible Howell interval algorithm; they have not been implemented or benchmarked here. Cost units differ from the manuscript's coordinate counts, which omit valuations, inversions, and heap overhead. Space excludes inputs, offline queries, and integer bit lengths. The present current-prefix/offline table needs `O(Kd²)` space, unlike the historical-version interface in the table.

Thus an n-independent query bound alone is insufficient novelty, and no universal advantage is established for large K or unavailable factorization. The preprocessing/query/space tradeoff under a common model is the relevant comparison.

## 5. Suggested contribution wording and revision actions

Suggested wording:

> We present timestamped p-adic echelon tables for range-generated submodule membership in append-only sequences. Combining power-level digit representations with timestamp filtering, we maintain quotient identities and protected levels for all suffixes simultaneously. Maximum-timestamp residual scheduling excludes same-time collisions and limits each append to at most k nonbranching chains, yielding the stated dominant update and query bounds. Lean 4 verifies these mathematical properties and event counts. Digit bases, static modular membership, and field timestamped bases have precedents; our contribution is scoped to this maintenance algorithm and its proof.

Recommended next steps, in order:

1. Add S1/S2/S4/S5 to both Related Work sections and the bibliography, distinguishing scholarly and implementation evidence, then regenerate PDFs.
2. Establish the exact correspondence with S2: ordering conventions, p-generator closure, uniqueness, and the extra conditions required for dynamic maintenance. This audit identifies proximity, not a completed equivalence proof.
3. Add a compact version of the baseline table, reconcile operation units, and benchmark at least one factorization-free baseline.
4. If claiming that the scheduling policy is necessary, supply a failing input or weaker bound for immediate displacement processing. A proof of the chosen algorithm does not prove every design choice necessary.
5. Seek expert scrutiny of whether an existing filtered/labelled module algorithm directly yields the same parameter bounds. No external messages were sent in this audit.

## 6. Search record and limitations

Date: 2026-09-17. Public web search, author-hosted papers, arXiv, publisher pages, and original formalization project pages; no exhaustive subscription-database search.

Queries actually used included:

```text
"Fast Algorithms for Linear Algebra Modulo N"
"Howell form" "incremental"
"Howell form" "update"
"Howell form" "suffix"
"dynamic" "submodule membership"
"range" "span membership" vectors
"submodule" "range queries"
"range queries" "modular" "linear basis"
"timestamp" "linear basis" range
"区间" "线性基" "时间戳" 2019
"minimal Gröbner" "p-basis" Kuijper
signature based Groebner bases rings zero divisors arxiv
Lean verified Howell normal form Smith normal form modular linear algebra
```

Additional interval/submodule and timestamped/p-adic queries excluded this project's site and Codeforces copies. Project posts and mirrors were not treated as independent prior art. Crawl/upload dates were not used as publication dates: S1 is ESA 1998; S2's arXiv record confirms its 2011 journal reference.

Remaining gaps include original competitive-programming priority, comprehensive forward citations, non-English theses, earlier group-code algorithms, and the full scope of labelled/filtered Gröbner methods. The audit supports narrower claims and identifies essential comparisons, not a worldwide-first claim or publication guarantee.
