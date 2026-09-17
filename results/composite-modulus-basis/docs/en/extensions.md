# Supplement: normal forms and general finite rings

[中文](../zh/extensions.md) · [Artifact overview](../../README-EN.md)

## 1. Connection to Smith / Hermite Normal Form

Membership in the submodule spanned by a single interval is equivalent to integer lattice membership:

$$x \in A\mathbb{Z}^{r-l+1} + m\mathbb{Z}^d$$

This can be resolved via the Hermite Normal Form (HNF) of the lattice basis or the Smith Normal Form (SNF) of the corresponding matrix. However, membership testing requires basis change matrices; the diagonal invariants of SNF alone are insufficient to decide membership for an arbitrary $x$.

Our algorithm avoids computing standard forms for each interval from scratch. Instead, it maintains a digital basis simultaneously adapted to all suffixes, relying on timestamps and the single-cyclic-quotient property of vector insertion for efficient updates.

**Corollary:** If an interval retains $s$ active slots in its $p^k$-basis, its spanned submodule contains exactly $p^s$ elements. For general $m$, the submodule size is the product of component sizes. Tests check slot counts with this property and independently check returned cardinalities by enumeration or lattice indices. The `span_size` implementation scans all slots, using `O(dK)` slot checks plus exponentiation and big-integer costs; its complexity differs from membership queries.

---

## 2. Extension to Arbitrary Finite Commutative Rings

This is an additional mathematical reduction with small-ring program tests; it is outside the current core Lean theorem.

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

