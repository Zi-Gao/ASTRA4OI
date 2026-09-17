# Maintenance and Verification History

[中文](../zh/history.md) · [Current overview](../../README-EN.md)

This file records development history. The current specification is in
[ARTICLE-EN.md](../../paper/main-en.tex), [SOLUTION-EN.md](extensions.md), and
[LEAN_VERIFICATION-EN.md](formalization.md). Actual run outputs are stored separately to
avoid duplicating mutable counts in historical notes.

## 2026-09-11: prototypes and counterexamples

- Investigated interval-generated submodule membership over prime powers.
- Checked membership using a prototype that explicitly inserts p-multiples for closure.
- Confirmed two failures of naive generalization: modulo 4, `(2,1)` needs the later pivot `(0,2)`;
  the sequence `1,2` cannot be represented by retaining only the newest original vector.
- Explored immediately continuing displaced old rows; that variant is not the guaranteed algorithm.

## 2026-09-12: algorithm and implementation

- Established descending-timestamp processing with displaced residuals returned to the queue.
- Gave the cyclic-quotient power-level proof and nonbranching-chain cost bound, and implemented
  Python append, historical-query, and offline APIs.
- Added coefficient enumeration, metadata checks, explicit-closure comparisons, and small
  general-finite-ring reduction tests.

## 2026-09-14: core formal-proof review

- Reviewed the complete Mathlib proof chain: digit bases, collision exclusion, insertion
  termination, suffix queries, and CRT.
- Included initial power-row preparation in the accounting, giving a `3nkd²` dominant
  coordinate-update allowance for positive dimension.
- Distinguished mathematical operation counts, scalar-subroutine costs, and Python source refinement.

## 2026-09-15: public-repository organization

- Added the general proofs under `lean/`, with pinned toolchain and dependency commits;
  retained the optional finite model as `LeanRegression`.
- Added `verify_lean.py` to build and audit the axiom allowlist of eight core theorems.
- Moved historical prototypes into `experiments/`; `solver.py` remains the reference entry point.
- Generate precomputed powers incrementally, omit the unused last power-row calculation,
  and count column visits and initial row passes.
- Report noninteger CLI input as a clear argument error; retain the explicit caller contract
  that supplied factor bases must be prime.
- Added an independent integer-lattice oracle, invertible-coordinate constructions, and
  one-dimensional gcd tests under `tests/`.
- Expanded to 31-bit primes, deep power levels, and a 120-bit CRT modulus; retained small exhaustive
  cases and checked YES, NO, historical versions, and operation bounds.
- Added performance samples for a small composite, large prime power, and large CRT modulus,
  with independent lattice spot checks.
- Use the Chinese core article as the primary presentation, with synchronized English usage,
  proofs, Lean scope, testing, and maintenance records.
- Added GitHub Actions for Python 3.10/3.14 and Lean; remote results depend on actual GitHub execution.

Execution reports: [program tests](../../artifacts/tests.txt), [Lean checks](../../artifacts/lean.txt),
[performance samples](../../artifacts/benchmarks.txt).

## 2026-09-16: paper format and formal concordance

- Retain only entry/build files at the root; separate manuscripts, Lean, implementation, documentation, and logs.
- Write bilingual LaTeX manuscripts with aligned definitions, lemmas, main theorems, and references.
- Add `Paper.lean`, relating one-based inclusive intervals to timestamp semantics and proving literal-interval main results.
- Generate bilingual concordance from one JSON map: 15 paper claims and 32 Lean declarations, all covered by the axiom audit.
- Distinguish event counts from implementation contracts in the full-cost proposition.
