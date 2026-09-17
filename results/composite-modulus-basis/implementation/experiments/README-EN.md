# Historical Prototypes

[中文](README.md) · [Reference implementation](../solver.py)

- `explicit_closure.py`: explicitly inserts p-multiples after pivot writes; used for supplementary comparisons.
- `fast_prototype.py`: an early exploratory version of the fast algorithm, retained for traceability.

Run from `implementation/`:

```sh
python3 -m experiments.explicit_closure
python3 -m experiments.fast_prototype
```

These are not the supported API and do not establish the `O(nkd²)` guarantee.
See [README-EN.md](../../docs/en/usage.md) and [TESTING-EN.md](../../docs/en/testing.md) for the reference API,
input validation, and current tests.
