# Testing, Coverage, and Reproduction

[中文](../zh/testing.md) · [Overview](../../README-EN.md) · [Lean proofs](formalization.md)

Tests check the reference program; they do not replace general mathematical proofs.
The core Lean theorems do not depend on these tests or on the prime, dimension, and length
ranges listed below.

## 1. Commands

Python 3.10+, standard library only. From this directory:

```sh
python3 implementation/test_solver.py                 # All tests.
python3 implementation/test_solver.py --suite small   # Exhaustive, metadata, prototype, finite-ring tests.
python3 implementation/test_solver.py --suite large   # Independent large-modulus checks.
python3 formal/verify.py --regression    # General proofs, axiom audit, finite Lean regression.
python3 implementation/benchmark.py                  # Three performance samples.
```

Tests use `assert`; entry points reject `python -O`. A failure returns a nonzero status and,
where practical, reports parameters, the interval, and the target. The large-suite seed is
`20260915`; the small-suite primary seed is `20260912`. Metadata, prototype, and finite-ring
checks use separate fixed seeds recorded in the code.

Refresh execution reports with:

```sh
python3 implementation/test_solver.py > artifacts/tests.txt 2>&1
python3 formal/verify.py --regression > artifacts/lean.txt 2>&1
python3 implementation/benchmark.py > artifacts/benchmarks.txt 2>&1
```

Timings vary with hardware, Python version, and load. Check counts and answers are determined
by the fixed seeds.

## 2. Why retain small-prime enumeration?

Small moduli allow enumeration of all coefficients and targets, producing expected answers
directly from the definition of a linear combination. This systematically checks edge cases
and should not be discarded merely to increase prime sizes. Exhaustive sequence spaces include:

| Modulus | Dimension | Sequence length |
|---:|---:|---:|
| 4 | 2 | 3 |
| 8 | 1 | 4 |
| 2 | 2 | 4 |
| 6 | 1 | 3 |
| 12 | 1 | 2 |

Additional tests enumerate all targets for random sequences modulo 1, 4, 5, 6, 8, 9, 12, and 18;
check timestamp/level identities and operation bounds; compare 1,200 cases with an explicit-closure
prototype; and test reductions for three small finite rings.

## 3. Larger primes, deep power levels, and CRT

Every fixed test prime is independently verified by trial division in the tests, without calling
the production factorization routine. Primes reach **2,147,483,647**, including common OI moduli
**998,244,353** and **1,000,000,007**.

| Modulus or factorization | Modulus bit length |
|---|---:|
| $17$ | 5 |
| $97^2$ | 14 |
| $257^4$ | 33 |
| $65537$ | 17 |
| $65537^3$ | 49 |
| $998244353$ | 30 |
| $998244353^2$ | 60 |
| $1000000007^3$ | 90 |
| $2147483647^2$ | 62 |
| $2^{64}$ | 65 |
| $3^{20}$ | 32 |
| $2^{12}\cdot97^3\cdot65537$ | 48 |
| $998244353^2\cdot1000000007^2$ | 120 |

Bit length means the binary length of a positive integer, so $2^{64}$ has 65 bits.
Large cases explicitly supply their known factorization to avoid expensive trial factorization.
Test dimensions are 1, 2, 4, 8, and 12, with sequence lengths 24 or 32; benchmarks additionally
cover dimension 16 and length 4,000.

### Independent expected answers

1. **Integer-lattice oracle** (`implementation/tests/oracles.py`). Reduce modular membership to membership in
   $\operatorname{span}_{\mathbb Z}(a_l,\ldots,a_r,mI_d)$. Extended gcd and determinant-one integer
   row operations construct a triangular basis, followed by integer substitution. No prime
   factorization, timestamps, power levels, or production elimination algorithm are used.
   The $mI_d$ rows in unprocessed coordinates permit intermediate-value reduction to prevent
   integer growth. The lattice index independently determines the module's cardinality.
   The oracle is first checked against coefficient enumeration on **4,656** small-modulus targets.
2. **Analytic constructions**. Begin with coordinate-axis generators whose coordinate ideals are
   determined by gcds of their coefficients with $m$. Apply the same known invertible integer
   coordinate transformation to inputs and targets. This creates dense inputs with unchanged
   answers; neither expected membership nor cardinality requires elimination. These large-modulus
   constructions also check the lattice oracle itself on 9,484 additional targets.
3. **One-dimensional gcd oracle**. For each interval compute $g=\gcd(m,a_l,\ldots,a_r)$ directly.
   Membership is $g\mid x$ and module size is $m/g$. All intervals are checked even at large moduli.

### Not just random full-rank data

Cases include zero and duplicate rows, nonunit multiples, coupled annihilator relations,
low-rank combinations, and newer suffixes missing particular coordinates. Targets include
explicit linear combinations, independent random vectors, unit vectors, and constructed
nonmembers. Every modulus configuration must produce both YES and NO cases.

Each query is checked immediately after appending, against historical versions after further
appends, and through the offline API. `span_size` is also checked. Every append verifies column
visits, pops, writes, reductions, and the `3kd²` coordinate-update allowance including input
normalization and power-row preparation. These assertions check the implementation; the general
bounds come from the mathematical and Lean proofs.

## 4. Recorded counts

This maintenance run is dated 2026-09-15; see [test_results.txt](../../artifacts/tests.txt).

| Suite | Counts |
|---|---|
| Original coefficient-enumeration main tests | 9,278 sequences; 79,694 intervals; 5,959,998 membership assertions |
| Additional finite-ring reduction tests | 153,600 assertions |
| New large-modulus suite | 78 sequences; 9,332 intervals; 240,420 membership assertions |
| Large interval breakdown | 4,296 lattice; 1,136 analytic; 3,900 one-dimensional gcd |
| Large query answers | 46,386 YES; 33,754 NO; 80,140 query cases |

Membership assertions count three APIs/stages checking the same query, not that many independent
inputs. Metadata, prototype comparisons, and oracle self-checks are reported separately and are
not included in the main sequence and interval counts.

## 5. Performance samples

[benchmark.py](../../implementation/benchmark.py) uses seed `120926` for three moduli:

- $72=2^3\cdot3^2$;
- $1000000007^2$;
- $998244353^2\cdot1000000007^2$.

Defaults are `n=4000, d=16, q=8000`, with both explicit-member and random targets. Timing covers
only offline solving; data generation, oracle spot checks, and the separate operation-count
pass are outside the timed region. Every 97th answer is independently checked, giving 83 lattice
checks per configuration. This does not independently validate every benchmark answer and is
not a worst-case runtime proof.

Parameters can be changed, for example:

```sh
python3 implementation/benchmark.py --case large-crt --n 1000 --dimension 12 --queries 2000
```

See [benchmark_results.txt](../../artifacts/benchmarks.txt) for local timings, answer counts, and counters.

## 6. Maintenance checks

The repository workflow `.github/workflows/composite-modulus-basis.yml` runs the full tests on
Python 3.10 and 3.14. A separate Lean job builds the proofs, audits axioms, and runs finite regression.
The workflow executes after pushes or pull requests; local validation is not a remote CI result.
