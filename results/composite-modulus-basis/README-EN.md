# Range-Generated Submodule Membership over Composite Moduli

[中文](README.md)

This directory is organized as a research paper and reproducible artifact. Chinese is the primary
manuscript; the English version uses identical definition, lemma, and theorem numbering.
The core algorithm is a timestamped p-adic echelon table with general Lean 4 correctness and
operation-count proofs.

## Paper and proofs

- **[English paper PDF](paper/output/pdf/paper-en.pdf)** / [Chinese paper PDF](paper/output/pdf/paper-zh.pdf)
- [English LaTeX source](paper/main-en.tex) / [Chinese LaTeX source](paper/main-zh.tex)
- **[Paper–Lean concordance](docs/en/proof-map.md)** / [Literal interval-index main theorems](formal/LeanVerification/Paper.lean)
- [Formalization scope and trust boundary](docs/en/formalization.md)
- [Novelty audit and prior-work comparison (2026-09-17)](docs/en/novelty-audit.md)
- [C++ implementations and standardized benchmarks](implementation/benchmark_cpp/README-EN.md)
- **[OI/CP performance results](docs/en/cpp-benchmark-results.md)** (basic/optimized C++, eight candidates, 36 datasets)

For a known factorization `m = ∏ p_s^k_s`, write `K = ∑ k_s` and let `w` be the component count.
Dominant coordinate updates are `O(nKd²)` for preprocessing and `O(wd²)` per membership query.
Inversion, valuation, heap, factorization, and integer bit costs are separate; the paper makes
these cost models explicit.

## Layout

```text
paper/           Bilingual manuscripts, bibliography, theorem map, and PDFs
formal/          Lean project, paper-facing theorems, declaration audit
implementation/  Reference program, tests, benchmarks, and I/O examples
  experiments/   Historical prototypes for supplementary comparisons
  tests/         Independent lattice oracle and large-modulus tests
docs/zh/         Chinese usage, verification, tests, extensions, and history
docs/en/         Corresponding English documentation
artifacts/       Actual test, build, and benchmark logs
```

## Reproduction

Python 3.10+; the reference program and tests use only its standard library. From this directory:

```sh
python3 implementation/solver.py < implementation/examples/example.in
make test
make formal
make paper
make check
```

- Lean setup and dependency caches: [formalization guide](docs/en/formalization.md).
- PDF compilation requires TeX Live/XeLaTeX with `ctex`, Fandol fonts, and `latexmk`.
- [API and input contracts](docs/en/usage.md) · [Test coverage](docs/en/testing.md) · [Mathematical supplements](docs/en/extensions.md)

Python reference tests include primes up to **2,147,483,647**, `2^64`, `(10^9+7)^3`, and a **120-bit CRT modulus**,
with YES, NO, historical-version, and operation-bound checks. Logs are in [artifacts/](artifacts/).
Formal verification is not Python source refinement and does not imply external peer review of the paper.

The separate C++ benchmark covers **32-bit moduli**, comparing basic/optimized timestamp tables,
Howell-style interval baselines, and field-specialized methods. Its implementation and performance
measurements are not verified by the existing Lean mathematical proofs; see the linked C++ guide.
