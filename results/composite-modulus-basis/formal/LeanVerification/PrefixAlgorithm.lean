import LeanVerification.Totality
import Mathlib.Data.List.Induction
import Mathlib.Tactic

/-!
# End-to-end prefix construction

Starting from the empty table, repeatedly apply the total timestamped append.
The resulting final table answers every left endpoint of the current prefix,
and the accumulated counters give the full `n k d²` preprocessing bound.
-/

namespace CompositeModulusBasis.PrefixAlgorithm

open BasisQuery FastAppend PadicEchelon TimestampedBasis TimestampLayerInvariant
  Totality VerifiedScan WorklistRefinement

/-- A completed build for one source prefix, with aggregate operation counts. -/
structure BuildResult {p k d : Nat} (hp : p.Prime)
    (source : List (SourceVector p k d)) where
  table : FastTable hp source
  visits : Nat
  pops : Nat
  valuations : Nat
  normalizations : Nat
  vectorPasses : Nat
  visits_le : visits ≤ source.length * (k * d)
  pops_le : pops ≤ source.length * (k * (d + 1))
  valuations_le : valuations ≤ source.length * (k * d)
  normalizations_le : normalizations ≤ source.length * (k * d)
  vectorPasses_le : vectorPasses ≤ 2 * (source.length * (k * d))
  cellOps_le : vectorPasses * d ≤ 2 * source.length * k * d * d

/-- Every strictly timestamp-increasing source list has a fully built fast
table.  Reverse induction exposes exactly the latest element required by the
append theorem. -/
theorem buildResult_nonempty {p k d : Nat} (hp : p.Prime)
    (source : List (SourceVector p k d)) (hstrict : SourceStrict source) :
    Nonempty (BuildResult hp source) := by
  induction source using List.reverseRecOn with
  | nil =>
      exact ⟨⟨emptyFastTable hp, 0, 0, 0, 0, 0,
        by simp, by simp, by simp, by simp, by simp, by simp⟩⟩
  | append_singleton priorSource item ih =>
      rw [SourceStrict, List.pairwise_append] at hstrict
      have hprefixStrict : SourceStrict priorSource := hstrict.1
      have hlatest : ∀ old ∈ priorSource, old.timestamp < item.timestamp := by
        intro old hold
        exact hstrict.2.2 old hold item (by simp)
      rcases ih hprefixStrict with ⟨previous⟩
      let appended := totalAppend hp previous.table item hlatest
      have hvisits : previous.visits + appended.visits ≤
          (priorSource ++ [item]).length * (k * d) := by
        have hadd := Nat.add_le_add previous.visits_le appended.visits_le
        simpa [List.length_append, Nat.add_mul] using hadd
      have hpops : previous.pops + appended.pops ≤
          (priorSource ++ [item]).length * (k * (d + 1)) := by
        have hadd := Nat.add_le_add previous.pops_le appended.pops_le
        simpa [List.length_append, Nat.add_mul] using hadd
      have hvaluations : previous.valuations + appended.drain.valuations ≤
          (priorSource ++ [item]).length * (k * d) := by
        have hadd := Nat.add_le_add previous.valuations_le appended.valuations_le
        simpa [List.length_append, Nat.add_mul] using hadd
      have hnormalizations : previous.normalizations + appended.drain.normalizations ≤
          (priorSource ++ [item]).length * (k * d) := by
        have hadd := Nat.add_le_add previous.normalizations_le appended.normalizations_le
        simpa [List.length_append, Nat.add_mul] using hadd
      have hpasses : previous.vectorPasses + appended.drain.vectorPasses ≤
          2 * ((priorSource ++ [item]).length * (k * d)) := by
        have hadd := Nat.add_le_add previous.vectorPasses_le appended.vectorPasses_le
        simpa [List.length_append, Nat.add_mul, Nat.mul_add, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hadd
      refine ⟨⟨appended.result, previous.visits + appended.visits,
        previous.pops + appended.pops,
        previous.valuations + appended.drain.valuations,
        previous.normalizations + appended.drain.normalizations,
        previous.vectorPasses + appended.drain.vectorPasses,
        hvisits, hpops, hvaluations, hnormalizations, hpasses, ?_⟩⟩
      calc
        (previous.vectorPasses + appended.drain.vectorPasses) * d ≤
            (2 * ((priorSource ++ [item]).length * (k * d))) * d :=
          Nat.mul_le_mul_right d hpasses
        _ = 2 * (priorSource ++ [item]).length * k * d * d := by ring

noncomputable def build {p k d : Nat} (hp : p.Prime)
    (source : List (SourceVector p k d)) (hstrict : SourceStrict source) :
    BuildResult hp source :=
  Classical.choice (buildResult_nonempty hp source hstrict)

/-- The final table is simultaneously correct for every timestamp threshold,
which is exactly every interval ending at this prefix. -/
theorem BuildResult.correct {p k d : Nat} {hp : p.Prime}
    {source : List (SourceVector p k d)} (built : BuildResult hp source) :
    CorrectTable source built.table.entries :=
  built.table.correct

/-- There is at most one stored row per `(column, p-level)` slot. -/
theorem BuildResult.table_length_le {p k d : Nat} {hp : p.Prime}
    {source : List (SourceVector p k d)} (built : BuildResult hp source) :
    built.table.entries.length ≤ d * k := by
  have hslots := ordered_slots_nodup built.table.ordered
  have hcard := hslots.length_le_card
  simpa [Slot] using hcard

/-- End-to-end interval membership: a certified query exists, its Boolean is
correct in both directions, it performs at most `d` row reductions, and hence
at most `d²` coordinate operations. -/
theorem BuildResult.query_complete {p k d : Nat} {hp : p.Prime}
    {source : List (SourceVector p k d)} (built : BuildResult hp source)
    (left : Nat) (target : Vector p k d) :
    ∃ answer : Bool,
      ∃ derivation : Derivation (basisAt built.correct left) target answer,
        (answer = true ↔ target ∈ sourceSubmodule source left) ∧
        derivation.reductions ≤ d ∧ derivation.reductions * d ≤ d * d := by
  rcases TimestampedBasis.query_complete hp built.correct left target with
    ⟨answer, derivation, hcorrect, hreductions⟩
  exact ⟨answer, derivation, hcorrect, hreductions,
    Nat.mul_le_mul_right d hreductions⟩

/-- One statement collecting total construction, all-threshold correctness,
and the global preprocessing bounds. -/
theorem end_to_end {p k d : Nat} (hp : p.Prime)
    (source : List (SourceVector p k d)) (hstrict : SourceStrict source) :
    ∃ built : BuildResult hp source,
      CorrectTable source built.table.entries ∧
      built.visits ≤ source.length * (k * d) ∧
      built.pops ≤ source.length * (k * (d + 1)) ∧
      built.valuations ≤ source.length * (k * d) ∧
      built.normalizations ≤ source.length * (k * d) ∧
      built.vectorPasses * d ≤ 2 * source.length * k * d * d := by
  let built := build hp source hstrict
  exact ⟨built, built.correct, built.visits_le, built.pops_le,
    built.valuations_le, built.normalizations_le, built.cellOps_le⟩

/-- Generating the initial power rows by repeated multiplication by `p`
costs at most `k*d` coordinate updates per source vector.  The original
`cellOps_le` counts only the drain; this bound includes that initialization.
A coordinate update denotes one scaling or multiply-subtract, not one
individual ring operation.  Lookup, valuation, inversion and heap costs are
accounted for separately.  The unsimplified bound also covers `d = 0`. -/
theorem BuildResult.cellOps_with_power_rows_le {p k d : Nat} {hp : p.Prime}
    {source : List (SourceVector p k d)} (built : BuildResult hp source) :
    source.length * k * d + built.vectorPasses * d ≤
      source.length * k * d + 2 * source.length * k * d * d := by
  exact Nat.add_le_add_left built.cellOps_le _

/-- For positive dimension, initialization is absorbed into `3 n k d²`.
Thus the advertised preprocessing bound covers the initial power rows as
well as all normalization and elimination passes. -/
theorem BuildResult.core_cellOps_le {p k d : Nat} {hp : p.Prime}
    {source : List (SourceVector p k d)} (built : BuildResult hp source)
    (hd : 0 < d) :
    source.length * k * d + built.vectorPasses * d ≤
      3 * source.length * k * d * d := by
  have hinit : source.length * k * d ≤ source.length * k * d * d := by
    simpa using Nat.mul_le_mul_left (source.length * k * d)
      (show 1 ≤ d by omega)
  calc
    source.length * k * d + built.vectorPasses * d ≤
        source.length * k * d * d + 2 * source.length * k * d * d :=
      Nat.add_le_add hinit built.cellOps_le
    _ = 3 * source.length * k * d * d := by ring

end CompositeModulusBasis.PrefixAlgorithm
