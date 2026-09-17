# Reference Program Usage

[中文](../zh/usage.md) · [Artifact overview](../../README-EN.md)

Python 3.10+, standard library only. Run from the result directory:

```sh
python3 implementation/solver.py < implementation/examples/example.in
python3 implementation/solver.py --online < implementation/examples/example.in
python3 implementation/solver.py --factors 2:2 < implementation/examples/example.in
```

## Input and output

```text
n d m q
<d coordinates of a_1>
...
<d coordinates of a_n>
l r x_1 ... x_d          # q queries
```

Require `n,d,m >= 1`, `q >= 0`, and `1 <= l <= r <= n`. Indices are one-based and inclusive.
Coordinates are integers and may be negative or noncanonical; the program normalizes them.
Output `YES` or `NO` per query. See [example.in](../../implementation/examples/example.in) and
[example.out](../../implementation/examples/example.out).

For large moduli, explicitly provide a factorization such as `--factors 998244353:2,1000000007:2`
and set the input modulus to that product. The program checks positivity, distinct bases, and
the product; **the caller guarantees primality**. Without factors, trial division takes up to
`O(sqrt(m))` trial divisions and is unsuitable for large-integer factorization.

## Python API

Start Python inside `implementation/`, or put that directory on the module search path:

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

`RangeBasis` supports appends and existing historical intervals, using prefix snapshots of
immutable rows. Interior edits and deletions are unsupported. Space is `O(nKd²)`.
`solve_offline` buckets queries by right endpoint and retains only the current basis, using
`O(Kd²)` basis space in addition to inputs, queries, and outputs. `span_size` takes `O(dK)`
slot checks plus exponentiation and integer bit costs; it does not have the membership-query bound.

## Verification entry points

```sh
make test                 # Full program tests.
make test-large           # Independent large-modulus checks.
make formal               # General proofs, axiom audit, finite regression.
make paper                # Compile both manuscripts.
make check                # Concordance and documentation consistency.
make benchmark            # Performance samples.
```

The reference implementation is [solver.py](../../implementation/solver.py). Historical prototypes
are in [experiments/](../../implementation/experiments/); they are not substitutes for the supported
API or its complexity guarantee.
