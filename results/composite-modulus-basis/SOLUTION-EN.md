# Linear Basis over Composite Moduli: Timestamped $p$-adic Echelon Table

## Overview

We can achieve a time complexity close to that of a standard range linear basis over a field. Given the prime factorization:

$$m = \prod_{s=1}^{w} p_s^{k_s}, \qquad K = \sum_s k_s$$

This directory provides the constructive algorithm, theoretical proofs, and a Python standard library implementation in `solver.py`:

| Mode | Dominant Modular Operations (Preprocessing) | Dominant Modular Operations (Per Query) | Basis Space Complexity |
| --- | --- | --- | --- |
| Single prime power, offline by right endpoint | $O(nd^2k)$ | $O(d^2)$ | $O(d^2k)$ |
| Arbitrary integer modulus, offline by right endpoint | $O(nd^2K)$ | $O(wd^2)$ | $O(d^2K)$ |
| Persist all prefixes, online queries on arbitrary historical intervals | Same as above | Same as above | $O(nd^2K)$ |

In particular, for $m = p^2$, each column requires only two slots, achieving the same asymptotic complexity as a standard linear basis over a field. When $k = 1$, the algorithm degenerates to the standard timestamped linear basis.

The table above accounts for the dominant modular additions and multiplications; heap comparisons, $p$-adic valuations, unit inversions, integer bit complexities, and integer factorization costs are detailed later. Large integer factorization is not treated as a free operation.

---

## 1. Where Naively Adapting Standard Linear Bases Fails

### Multiples of Non-Unit Pivots Generate New Subsequent Pivots

Modulo 4, consider a single vector:

$$a = (2, 1), \qquad 2a = (0, 2)$$

If we only retain $a$ in the first column, a query for $(0, 2)$ will fail to find a pivot in the second column and will incorrectly report that it cannot be represented. The same issue occurs for $(p, 1)$ modulo $p^2$ in general.

### A Single Position Cannot Merely Retain the Latest Raw Vector

Consider the 1D sequence $a_1 = 1, a_2 = 2 \pmod 4$: the entire interval can span $1$, while the suffix $[2, 2]$ can only span $0$ and $2$. Completely replacing $1$ with the newer vector $2$ loses information about the older interval, whereas keeping only $1$ fails to represent the new suffix.

The 1D sequence modulo $p^k$:

$$1, p, p^2, \ldots, p^{k-1}$$

yields $k$ distinct non-zero suffix ideals. This demonstrates that the standard field approach of "one timestamped raw vector per column" is insufficient; our algorithm allocates $k$ slots per column. (We do not claim, however, that an arbitrary data structure must strictly consume $k$ full vectors).

### Timestamps After Elimination Must Remain Conservative

When a newer row eliminates an older row, the remaining row must retain the older timestamp. A row cannot inherit a newer timestamp simply because it participated in Gaussian elimination against a newer vector.

For example, modulo 4, the difference between $(1, 0)$ and $(1, 1)$ is $(0, 1)$, but the second vector alone cannot span this difference.

---

## 2. Table and Queries over Prime Powers

Let $R = \mathbb{Z}/p^k\mathbb{Z}$, with all coordinates canonicalized to $[0, p^k)$.

The leading position of a non-zero row $b$ is defined as:

$$\operatorname{lead}(b) = (j, v_p(b_j))$$

where $j$ is the first non-zero coordinate, ordered lexicographically by index $j$ first, then valuation $v_p(b_j)$. Multiplying by $p$ either strictly advances the leading position of a non-zero row or annihilates the row to zero.

We maintain a table $B[j][v]$ consisting of $dk$ slots. Each occupied slot contains:

* **Vector $b$**: The first $j$ coordinates are zero, with the pivot normalized to $b_j = p^v$;
* **Timestamp $t$**: This row can be represented by raw vectors with indices $\ge t$ in the current prefix;
* **Power level $e$**: This row originates from $p^e a_t$ of raw vector $a_t$.

**Note that $e$ and the pivot valuation $v$ are distinct quantities.** When a row is eliminated into subsequent columns, its pivot valuation may change, but its power level $e$ is preserved.

**Normalization validity:** If $b_j = p^v u$ with $\gcd(u, p) = 1$, we invert $u$ modulo $p^k$ and multiply the entire row by $u^{-1}$. We never invert the non-unit $p^v$.

After processing prefix $r$, a query on the interval $[l, r]$ only uses slots with timestamp $t \ge l$:

```text
for j = 0 .. d-1:
    if x[j] == 0: continue
    v = valuation_p(x[j])
    b = B[j][v]
    if b does not exist or b.time < l: return NO
    c = x[j] / p^v                 # Integer division, not modular inverse
    x = x - c * b                  # Modulo p^k, clearing coordinate j entirely
return YES

```

Each successful elimination zeroes out coordinate $j$ entirely, resulting in at most $d$ vector operations, each taking $O(d)$ time. Queries do not modify the table.

---

## 3. $p$-Digit Basis and Its Fundamental Properties

Here, a **$p$-digit basis** refers to a set of rows with pairwise distinct leading positions such that every element in the submodule can be uniquely expressed as:

$$\sum_b c_b b, \qquad c_b \in \{0, 1, \ldots, p-1\}$$

This is distinct from a free module basis and does not require the rows to be linearly independent over $R$.

**Property 1: Distinct digit combinations yield distinct vectors.**
Subtracting two combinations, let the minimal leading position among non-zero coefficients be $(j, v)$. The coefficient lies in $\{-(p-1), \ldots, p-1\} \setminus \{0\}$, which is not divisible by $p$. Thus, it cannot be canceled out by terms with larger valuations at index $j$.

**Property 2: Membership query correctness.**
If $x$ belongs to the submodule, the first non-zero term in its digit expansion shares the exact same leading position as $x$, guaranteeing the existence of a corresponding slot. Subtracting any ring multiple of the pivot keeps the vector within the submodule, allowing elimination to proceed. Conversely, successful elimination serves as an explicit certificate of linear representability.

**Property 3: Partial elimination yields the canonical leading position in the quotient group.**
Eliminating a vector against the digit basis of submodule $H$ until encountering a missing slot yields a non-zero residual row $b$. Its leading position depends solely on the coset $x + H$: if two residual rows from the same coset had different leading positions, their difference would belong to $H$ while having a leading position missing from $H$, contradicting Property 2.

If the coset is non-zero, this position is called its leading position. Multiplying the coset by $p$ either strictly advances the leading position or annihilates the coset: this is done by multiplying the residual row by $p$ and continuing elimination against $H$. Multiplying by a unit does not alter the coset's leading position.

### Inserting a Vector into an Existing Submodule

Suppose $a + H$ has order $p^h$ in the additive quotient group ($0 \le h \le k$). Then $p^e a + H$ is non-zero with strictly increasing leading positions for $e < h$, and is zero for $e \ge h$.

Therefore, sequentially eliminating $a, pa, \ldots, p^{k-1}a$ yields exactly $h$ new rows with pairwise distinct leading positions. They can be normalized as:

$$b_e \equiv u_e p^e a \pmod H, \qquad p \nmid u_e, \quad 0 \le e < h$$

The digit combinations of these rows iterate over all $p^h$ elements of the cyclic quotient group $(H + Ra)/H$. One can determine the $p$-adic digits iteratively: the unit coefficient $u_e$ at level $e$ can always match the current digit, passing carries to subsequent levels. Combined with the digit basis of $H$, they form a valid digit basis for $H + Ra$.

This also implies that different power levels of the same raw vector will never compete for the same slot after elimination against newer submodules.

---

## 4. Fast Timestamped Insertion

A straightforward but slower construction is to rebuild each prefix in the order $a_r, a_{r-1}, \ldots, a_1$, inserting all $p$-power multiples of each raw vector. As shown in Section 3, this produces a valid digit basis for every suffix.

The fast algorithm preserves these invariant states and only handles pivot evictions triggered by the incoming vector.

When inserting at index $r$, initialize a priority queue with all non-zero multiples:

$$(a_r, r, 0), (pa_r, r, 1), \ldots, (p^{k-1}a_r, r, k-1)$$

The queue orders entries by timestamp descending, breaking ties by power level ascending. There are at most $k$ active rows at any time.

```text
while priority_queue is not empty:
    pop (a, t, e, start) with the latest timestamp
    find the first non-zero coordinate j of a starting from 'start'
    v = valuation_p(a[j])

    if B[j][v] is empty:
        normalize a, store as (a, t, e), and terminate this chain

    else if slot row b.time > t:
        a -= (a[j] / p^v) * b
        continue elimination on the next column

    else (a is newer):
        normalize a, swap with the older row b in B[j][v]
        b -= (b[j] / p^v) * a
        push the non-zero residual b back to the queue with its original (t, e) and start = j + 1
        terminate current chain

```

Collisions at the same timestamp never occur (proven in Section 5 and asserted in code). **Evicted older rows must re-enter the priority queue to guarantee that all newer timestamps finish processing first.** We do not consider the experimental variant that "eagerly eliminates the evicted row all the way through" as a proven algorithm.

Eviction preserves timestamp semantics: an older row minus a newer row still depends only on raw vectors with indices $\ge$ the older timestamp. Normalization only multiplies by units, keeping the power level $e$ invariant.

---

## 5. Correctness Proof of the Timestamping Algorithm

Let:

$$H_{t+1}^{(r)} = \langle a_{t+1}, \ldots, a_r \rangle_R$$

After processing prefix $r$, we maintain the following invariants:

1. For every left endpoint $l$, the rows with timestamp $\ge l$ form a $p$-digit basis for the submodule generated by $[l, r]$.
2. If $a_t$ has order $p^{h_t}$ in the quotient group $R^d / H_{t+1}^{(r)}$, the rows with timestamp exactly $t$ have power levels $e \in \{0, \ldots, h_t - 1\}$, satisfying:

$$b_{t,e} \equiv u_{t,e} p^e a_t \pmod{H_{t+1}^{(r)}}, \qquad p \nmid u_{t,e}$$



An empty table trivially satisfies these invariants. Below is the inductive step for an insertion.

**Step 1: Each old row preserves its quotient group identity.**
New vectors only enlarge newer submodules. When an older row subtracts a newer row and is scaled by a unit, the congruence condition above still holds. The initial power chain of a new vector clearly satisfies it. Each replacement merely transfers or eliminates an existing row without duplicating any `(timestamp, power_level)` pair.

**Step 2: Induction descending by timestamp.**
The priority queue processes rows by timestamp descending; an eviction only pushes an older row back into the queue. When processing timestamp $t$, all strictly greater timestamps have stabilized and, by the inductive hypothesis, form the digit basis of the updated submodule $H = \langle a_{t+1}, \ldots, a_r \rangle$.

In the previous prefix, timestamp $t$ had $h_{\text{old}}$ power levels; the new quotient group exponent satisfies $h_{\text{new}} \le h_{\text{old}}$ because $H$ only grows. All levels $e < h_{\text{new}}$ that must be retained remain present in the table or the queue: rows can only be discarded if they reduce to zero against newer rows, which happens if and only if $e \ge h_{\text{new}}$.

Rows with timestamp $t$ already in the table occupy slots missing from $H$, representing partial eliminations against $H$. Rows with timestamp $t$ popped from the queue are also eliminated against $H$ first:

* If $e \ge h_{\text{new}}$, its coset is zero, so it is eliminated to zero by the newer basis.
* If $e < h_{\text{new}}$, it terminates at a slot missing from $H$ and is retained. If an older row already occupies that slot, the older row is evicted and requeued.
* Two distinct power levels cannot occupy the same slot: by the quotient leading position property, their leading positions are strictly increasing. Identical power levels are never duplicated. Hence, collisions at the same timestamp never occur.

Thus, timestamp $t$ retains exactly the required $h_{\text{new}}$ levels. By the cyclic quotient lemma, combining them with the newer basis yields the digit basis for $\langle a_t, \ldots, a_r \rangle$.

Induction over all timestamps establishes both invariants. Filtering by timestamp $\ge l$ yields the correct digit basis for the interval $[l, r]$.

---

## 6. Complexity and Online Variant

### Why a Single Insertion Has Only $k$ Elimination Chains

An insertion starts with at most $k$ tasks. A task terminates upon encountering an empty slot; upon an eviction, the active task is replaced by a single evicted residual without branching. Each elimination step at a non-zero coordinate zeroes out that entire column, and re-enqueuing resumes from the next column ($j+1$). Thus, the work decomposes into at most $k$ linear chains, each visiting at most $d$ columns.

Each visit performs $O(1)$ vector operations of length $d$, yielding an overall dominant complexity of $O(kd^2)$ per insertion. This differs fundamentally from closure algorithms that generate an extra $p$-multiple row upon every eviction, which branch and cannot guarantee this bound.

Each insertion also entails:

* $O(kd \log(k+1))$ priority queue comparisons (queue size $\le k$).
* At most $kd$ unit inversions. Letting $I(p^k)$ denote inversion cost, this adds $O(kd I(p^k))$.
* $O(kd)$ $p$-adic valuations. For $p = 2$, this uses trailing zero counts; for other $p$, binary search on precomputed powers $p^v$ takes $O(\log(k+1))$ divisibility tests.

A query requires at most $d$ valuation computations and zero modular inversions. The detailed operation count is:

$$O\!\left(nkd(d + \log(k+1) + I(p^k)) + qd(d + \log(k+1))\right)$$

When dealing with arbitrary-precision integers, this must be scaled by the arithmetic complexity of the integer width. This represents modular operation counts, not a bit complexity independent of $\log m$.

### Offline Mode

Bucket queries by their right endpoint $r$, iterate $r = 1 \dots n$, insert $a_r$, and answer queries in bucket $r$. Bucketing takes $O(n + q)$; the basis structure requires $O(d^2k)$ space (excluding input, query, bucket, and output arrays).

### Online Queries and Online Appends

After processing each prefix, store a pointer snapshot of the $dk$ slots. Since row vectors and slot metadata are immutable, snapshots only copy references. A single insertion creates $O(kd)$ new slot records, each containing a row of length $d$.

* Total space across all prefixes: $O(nd^2k)$.
* Total snapshot copying time: $O(ndk)$, subsumed by preprocessing.
* Querying $[l, r]$ directly accesses snapshot $r$, taking $O(d^2)$ dominant modular operations.

This supports querying arbitrary intervals offline or streaming new vectors online while querying any existing historical interval. `RangeBasis` implements the latter. (Modifying or deleting vectors in the middle of the sequence is not supported).

If copying slot pointers is undesirable, one can track per-slot modification histories and binary-search on right endpoints or use persistent arrays, though this slightly increases query overhead without improving the space bound.

---

## 7. Arbitrary Integer Moduli: CRT

Run the algorithm independently over each $\mathbb{Z}/p_s^{k_s}\mathbb{Z}$. A query succeeds if and only if it succeeds in all prime-power components.

**Sufficiency of independent components:** While each component may find a different set of coefficients $\lambda_i^{(s)}$, the Chinese Remainder Theorem can combine them coordinate-wise for each index $i$ into a single global coefficient $\lambda_i \pmod m$. The components do not need to agree on integer coefficients beforehand.

Membership testing only checks solvability and does not require explicit CRT reconstruction. For $m = 1$ (the zero ring), any target vector is equivalent to zero; all valid interval queries return `YES`.

**Factorization Cost:** Theoretical bounds assume prime factorization is known. The reference implementation uses trial division ($O(\sqrt{m})$ worst-case) by default, intended for small moduli or verification. For known factorizations, pass `--factors 2:2,3:1`; the code verifies product correctness, positivity, and distinct bases, but the caller must ensure prime factors are prime. This algorithm does not solve large-integer factorization.

---

## 8. Connection to Smith / Hermite Normal Form

Membership in the submodule spanned by a single interval is equivalent to integer lattice membership:

$$x \in A\mathbb{Z}^{r-l+1} + m\mathbb{Z}^d$$

This can be resolved via the Hermite Normal Form (HNF) of the lattice basis or the Smith Normal Form (SNF) of the corresponding matrix. However, membership testing requires basis change matrices; the diagonal invariants of SNF alone are insufficient to decide membership for an arbitrary $x$.

Our algorithm avoids computing standard forms for each interval from scratch. Instead, it maintains a digital basis simultaneously adapted to all suffixes, relying on timestamps and the single-cyclic-quotient property of vector insertion for efficient updates.

**Corollary:** If an interval retains $s$ active slots in its $p^k$-basis, its spanned submodule contains exactly $p^s$ elements. For general $m$, the submodule size is the product of component sizes. Our test suite utilizes this property to independently verify slot counts.

---

## 9. Extension to Arbitrary Finite Commutative Rings

A general finite commutative ring is not necessarily a chain ring over a prime power, so its elements cannot be parameterized by a single $p$-adic valuation. For instance, in:

$$\mathbb{F}_2[\epsilon, \eta] / (\epsilon^2, \epsilon\eta, \eta^2)$$

the maximal ideal possesses two independent directions. However, we can perform a universal reduction via its additive group structure.

Assume the ring's additive decomposition, coordinate conversions, and multiplication are given. For a $p$-primary component:

$$(R_p, +) \cong \bigoplus_{j=1}^{s_p} \mathbb{Z}/p^{e_j}\mathbb{Z}, \qquad E_p = \max_j e_j$$

Select additive generators $b_1, \ldots, b_{s_p}$ for these cyclic factors. For each raw vector $a_i$, expand it into $s_p$ vectors:

$$b_1 a_i, \ldots, b_{s_p} a_i$$

Because any ring coefficient can be decomposed as $\sum_j z_j b_j$, ring linear combinations correspond precisely to integer linear combinations of these product vectors.

Map each additive coordinate $z \pmod{p^{e_j}}$ injectively into $\mathbb{Z}/p^{E_p}\mathbb{Z}$ via:

$$z \longmapsto p^{E_p - e_j} z$$

This is an injective additive homomorphism, embedding a $d$-dimensional ring vector into a $d s_p$-dimensional integer vector modulo $p^{E_p}$. Target vectors undergo the identical mapping. Different $p$-primary components annihilate each other and are handled independently.

Assign each product vector a distinct virtual timestamp: the original interval $[l, r]$ maps to:

$$[(l-1)s_p + 1, \; r s_p]$$

Multiple generators within the same block cannot share a single timestamp, as that would invalidate the lemma that each step introduces a single cyclic quotient group.

Each $p$-primary component contains $n s_p$ vectors of dimension $d s_p$ with maximum exponent $E_p$, yielding a dominant preprocessing cost of:

$$O(n d^2 E_p s_p^3)$$

and a query cost of $O(d^2 s_p^2)$, summed over all prime factors $p$ (plus conversion and multiplication overhead).

While this generalizes the algorithm to arbitrary finite commutative rings, the complexity scales polynomially with the additive rank $s_p$. We do not claim ring decomposition or multiplication are free operations for arbitrary ring presentations, nor that this general bound is optimal.

---

## 10. Execution and Verification

The test harness uses the following input format:

```text
n d m q
<d coordinates of a_1>
...
<d coordinates of a_n>
l r <d coordinates of x>          # q lines in total

```

```sh
python3 solver.py < example.in
python3 solver.py --online < example.in
python3 solver.py --factors 2:2 < example.in
python3 test_solver.py
python3 benchmark.py

```

Outputs one line per query containing `YES` or `NO`. Sample outputs are provided in `example.out`.

* `solver.py`: Production implementation; supports offline querying, online append and history queries, and submodule size computation.
* `test_solver.py`: Independent brute-force generation of submodules to verify all targets, structured randomized testing, and general ring reduction tests.
* `experiment.py`: Early explicit $p$-multiple closure prototype used as a baseline.
* `fast_experiment.py`: Exploratory verification of the fast priority-queue implementation.
* `benchmark.py` / `benchmark_results.txt`: Reproducible performance benchmarks and raw outputs.
* `PROGRESS.md`: Research milestones, verified results, and complexity bounds.

All proofs and implementations in this directory were developed independently without external codebases. Test metrics and execution timings are documented in `PROGRESS.md`.