# Paper and Lean 4 Formalization

[中文](../zh/formalization.md) · [Artifact overview](../../README-EN.md) · [Declaration concordance](proof-map.md)

## What is machine checked?

The paper has 15 numbered definitions, lemmas, theorems, a corollary, and a cost proposition,
mapped to 32 Lean declarations. [theorem-map.json](../../paper/theorem-map.json) is the single
source of correspondence data. The [synchronizer](../../formal/sync_paper.py) generates bilingual
Markdown tables, LaTeX tables, and [Audit.lean](../../formal/Audit.lean). `--check` detects drift
in numbering, source locations, or generated files.

[Paper.lean](../../formal/LeanVerification/Paper.lean) does more than rename existing results:

- `intervalSpan` directly defines the generated submodule using one-based inclusive input indices.
- `prefixSource_span` and `compositePrefix_span` equate it to the prefix table's threshold semantics.
- `theorem_1_prime_power` combines prefix construction, at most `dk` rows, the `3rkd²` allowance
  for power-row preparation and elimination, and correct interval answers with at most `d` reductions.
- `theorem_2_composite_interval` and `theorem_2_composite_preprocessing` give literal-interval CRT
  correctness and aggregated counters.

The underlying proofs cover digit injectivity, cardinality-based completeness, cyclic quotient
orders, missing-slot leads, protected levels, equal-time collision exclusion, and termination.
Construction starts from the empty table; successful execution is not an assumed premise.

## Cost-model boundary

A replacement normalizes and forms a displaced residual, so the drain takes at most `2kd²`
coordinate updates. One input-normalization pass and at most `k-1` passes multiplying by p add
an allowance `kd`, bounded in total by `3kd²` for positive dimension. Lean proves these algebraic
and combinatorial counts. The paper's full-cost proposition is explicitly marked “event counts
only”: array, binary-heap, inversion, and valuation costs depend on the written implementation contracts.

Lean's mathematical constructions use lists, execution relations, and choice. Their compiled
runtime is not claimed to match the reference array/heap implementation. Python source refinement,
byte-level allocation, complete integer bit complexity, and the supplementary general-ring
reduction are outside the machine proof.

## Building and auditing

Install [elan](https://github.com/leanprover/elan), then initially run from the artifact directory:

```sh
cd formal
lake exe cache get
cd ..
make formal
```

Lean is pinned to 4.32.0 and Mathlib to v4.32.0, with dependency commits in
[lake-manifest.json](../../formal/lake-manifest.json). Initial setup needs network access and
several GB of disk.

```sh
make core                         # General proofs and 32-declaration axiom audit.
make formal                       # Also run optional finite-model regression.
python3 formal/sync_paper.py --check
```

Transitive axioms of every mapped declaration must be among `propext`, `Classical.choice`, and
`Quot.sound`. The audit rejects `sorryAx`, native-evaluation axioms, and any other non-allowlisted
axiom. Declarations without axioms are handled explicitly. The default
[LeanVerification.lean](../../formal/LeanVerification.lean) imports all general proofs, including
the new paper-facing entry point.

## Role of the finite model

[LeanRegression.lean](../../formal/LeanRegression.lean) uses `native_decide` for 83,598 membership
comparisons modulo 4, 8, 9, and CRT moduli 6 and 12, plus two regression counterexamples.
This optional independent finite model is not imported by the general entry point and cannot
replace arbitrary-parameter proofs.

Actual output is in [artifacts/lean.txt](../../artifacts/lean.txt).
