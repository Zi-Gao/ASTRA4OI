import LeanVerification.CompositeAlgorithm

/-!
Paper-facing statements with literal one-based interval indices.  These
wrappers discharge the translation from a sequence prefix to the existing
strict-timestamp construction; they add no assumptions about successful runs.
-/

namespace CompositeModulusBasis.Paper

open scoped BigOperators
open PadicEchelon TimestampedBasis TimestampLayerInvariant PrefixAlgorithm
  CompositeAlgorithm

/-- The paper's interval-generated submodule, with one-based inclusive indices. -/
def intervalSpan {R : Type*} [CommRing R] {n d : Nat}
    (a : Fin n → Fin d → R) (left right : Nat) : Submodule R (Fin d → R) :=
  Submodule.span R {row | ∃ i : Fin n,
    left ≤ i.val + 1 ∧ i.val + 1 ≤ right ∧ row = a i}

def prefixSource {p k d n : Nat} (a : Fin n → Vector p k d)
    (right : Nat) (hright : right ≤ n) : List (SourceVector p k d) :=
  List.ofFn fun i : Fin right =>
    { timestamp := i.val + 1
      row := a ⟨i.val, lt_of_lt_of_le i.isLt hright⟩ }

theorem prefixSource_strict {p k d n : Nat} (a : Fin n → Vector p k d)
    (right : Nat) (hright : right ≤ n) :
    SourceStrict (prefixSource a right hright) := by
  rw [SourceStrict, prefixSource, List.pairwise_ofFn]
  intro i j hij
  exact Nat.add_lt_add_right hij 1

theorem prefixSource_span {p k d n : Nat} (a : Fin n → Vector p k d)
    (right : Nat) (hright : right ≤ n) (left : Nat) :
    sourceSubmodule (prefixSource a right hright) left = intervalSpan a left right := by
  unfold sourceSubmodule intervalSpan
  congr 1
  ext row
  constructor
  · rintro ⟨entry, hentry, hleft, hrow⟩
    simp only [prefixSource, List.mem_ofFn'] at hentry
    rcases hentry with ⟨i, rfl⟩
    exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hright⟩, hleft, Nat.succ_le_of_lt i.isLt, hrow⟩
  · rintro ⟨i, hleft, hbound, hrow⟩
    let j : Fin right := ⟨i.val, by omega⟩
    refine ⟨{ timestamp := j.val + 1
              row := a ⟨j.val, lt_of_lt_of_le j.isLt hright⟩ }, ?_, hleft, ?_⟩
    · simp only [prefixSource, List.mem_ofFn']
      exact ⟨j, rfl⟩
    · simpa [j] using hrow

/-- Theorem 1: an actual prefix construction, its storage/core-update bounds,
and a correct bounded query for every one-based interval ending at `right`.
The statement also permits empty intervals, so the paper's `1 ≤ left ≤ right`
precondition is a specialization rather than an additional proof assumption. -/
theorem theorem_1_prime_power {p k d n : Nat} (hp : p.Prime)
    (hd : 0 < d) (a : Fin n → Vector p k d) (right : Nat) (hright : right ≤ n) :
    ∃ built : BuildResult hp (prefixSource a right hright),
      built.table.entries.length ≤ d * k ∧
      right * k * d + built.vectorPasses * d ≤ 3 * right * k * d * d ∧
      ∀ (left : Nat) (target : Vector p k d),
        ∃ answer : Bool,
          ∃ derivation : BasisQuery.Derivation (basisAt built.correct left) target answer,
            (answer = true ↔ target ∈ intervalSpan a left right) ∧
            derivation.reductions ≤ d ∧ derivation.reductions * d ≤ d * d := by
  let built := build hp (prefixSource a right hright) (prefixSource_strict a right hright)
  refine ⟨built, built.table_length_le, ?_, ?_⟩
  · simpa [prefixSource] using built.core_cellOps_le hd
  · intro left target
    rcases built.query_complete left target with ⟨answer, derivation, hcorrect, hcost⟩
    rw [prefixSource_span a right hright left] at hcorrect
    exact ⟨answer, derivation, hcorrect, hcost⟩

def compositePrefix {ι : Type*} [Fintype ι]
    {primes exponents : ι → Nat} {d n : Nat}
    (a : Fin n → Fin d → ZMod (FullModulus primes exponents))
    (right : Nat) (hright : right ≤ n) :
    List (CompositeSourceVector primes exponents d) :=
  List.ofFn fun i : Fin right =>
    { timestamp := i.val + 1
      row := a ⟨i.val, lt_of_lt_of_le i.isLt hright⟩ }

theorem compositePrefix_strict {ι : Type*} [Fintype ι]
    {primes exponents : ι → Nat} {d n : Nat}
    (a : Fin n → Fin d → ZMod (FullModulus primes exponents))
    (right : Nat) (hright : right ≤ n) :
    CompositeSourceStrict (compositePrefix a right hright) := by
  rw [CompositeSourceStrict, compositePrefix, List.pairwise_ofFn]
  intro i j hij
  exact Nat.add_lt_add_right hij 1

theorem compositePrefix_span {ι : Type*} [Fintype ι]
    {primes exponents : ι → Nat} {d n : Nat}
    (a : Fin n → Fin d → ZMod (FullModulus primes exponents))
    (right : Nat) (hright : right ≤ n) (left : Nat) :
    compositeSubmodule (compositePrefix a right hright) left = intervalSpan a left right := by
  unfold compositeSubmodule intervalSpan
  congr 1
  ext row
  constructor
  · intro hrow
    rcases List.mem_map.mp hrow with ⟨entry, hentry, heq⟩
    rcases List.mem_filter.mp hentry with ⟨hentry, hleft⟩
    simp only [compositePrefix, List.mem_ofFn'] at hentry
    rcases hentry with ⟨i, rfl⟩
    refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hright⟩, ?_, Nat.succ_le_of_lt i.isLt, heq.symm⟩
    simpa using hleft
  · rintro ⟨i, hleft, hbound, hrow⟩
    let j : Fin right := ⟨i.val, by omega⟩
    apply List.mem_map.mpr
    refine ⟨{ timestamp := j.val + 1
              row := a ⟨j.val, lt_of_lt_of_le j.isLt hright⟩ }, ?_, ?_⟩
    · apply List.mem_filter.mpr
      constructor
      · simp only [compositePrefix, List.mem_ofFn']
        exact ⟨j, rfl⟩
      · simpa [j] using hleft
    · simpa [j] using hrow.symm

/-- Theorem 2, query part: CRT conjunction is equivalent to the literal
interval span and carries the summed `w*d²` coordinate-update bound. -/
theorem theorem_2_composite_interval {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat) (hprime : ∀ i, (primes i).Prime)
    (hdistinct : Function.Injective primes) {d n : Nat}
    (a : Fin n → Fin d → ZMod (FullModulus primes exponents))
    (right : Nat) (hright : right ≤ n) (left : Nat)
    (target : Fin d → ZMod (FullModulus primes exponents)) :
    ∃ answers : ι → Bool, ∃ reductions : ι → Nat,
      ((∀ i, answers i = true) ↔ target ∈ intervalSpan a left right) ∧
      (∀ i, reductions i ≤ d) ∧
      (∑ i, reductions i * d) ≤ Fintype.card ι * d * d := by
  have h := composite_query_cost primes exponents hprime
    (primePowers_pairwise_coprime primes exponents hprime hdistinct)
    (compositePrefix a right hright) (compositePrefix_strict a right hright) left target
  simpa only [compositePrefix_span] using h

/-- Theorem 2, preprocessing part: the same constructed component prefixes
have at most `3*right*K*d²` core coordinate updates, including power rows. -/
theorem theorem_2_composite_preprocessing {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat) (hprime : ∀ i, (primes i).Prime)
    (hdistinct : Function.Injective primes) {d n : Nat} (hd : 0 < d)
    (a : Fin n → Fin d → ZMod (FullModulus primes exponents))
    (right : Nat) (hright : right ≤ n) :
    (∑ i, (right * exponents i * d +
      (componentBuild primes exponents hprime
        (primePowers_pairwise_coprime primes exponents hprime hdistinct)
        (compositePrefix a right hright) (compositePrefix_strict a right hright) i).vectorPasses * d)) ≤
      3 * right * (∑ i, exponents i) * d * d := by
  simpa [compositePrefix] using componentBuilds_core_cellOps_le primes exponents hprime
    (primePowers_pairwise_coprime primes exponents hprime hdistinct)
    (compositePrefix a right hright) (compositePrefix_strict a right hright) hd

end CompositeModulusBasis.Paper
