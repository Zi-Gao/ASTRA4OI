import LeanVerification.CyclicExtension
import Mathlib.Tactic

/-!
# A fully verified basis for one interval / suffix

This module packages the cyclic-extension theorem into a recursive basis
builder.  It already gives a complete correctness proof and the `O(k d²)`
cost of adding one vector to one suffix.  The timestamped streaming refinement
is proved separately because it shares these suffix bases in one table.
-/

namespace CompositeModulusBasis.StaticSuffix

open BasisQuery CyclicExtension CyclicQuotient DigitCardinality PadicEchelon

noncomputable def emptyBasis (p k d : Nat) (_hp : p.Prime) : Basis p k d where
  pivots := []
  ordered := by simp [Ordered]
  generated := ⊥
  generated_eq_span := by simp [rowsOf]
  card_generated := by
    letI : NeZero (p ^ k) := ⟨pow_ne_zero _ _hp.ne_zero⟩
    simp

noncomputable def extensionExponent {p k d : Nat} (hp : p.Prime)
    (basis : Basis p k d) (a : Vector p k d) : Nat :=
  Classical.choose (exists_quotient_order_exponent hp basis.submodule a)

theorem extensionExponent_le {p k d : Nat} (hp : p.Prime)
    (basis : Basis p k d) (a : Vector p k d) :
    extensionExponent hp basis a ≤ k :=
  (Classical.choose_spec (exists_quotient_order_exponent hp basis.submodule a)).1

theorem extensionExponent_order {p k d : Nat} (hp : p.Prime)
    (basis : Basis p k d) (a : Vector p k d) :
    addOrderOf (basis.submodule.mkQ a) = p ^ extensionExponent hp basis a :=
  (Classical.choose_spec (exists_quotient_order_exponent hp basis.submodule a)).2

noncomputable def appendBasis {p k d : Nat} (hp : p.Prime)
    (basis : Basis p k d) (a : Vector p k d) : Basis p k d :=
  extendBasis basis hp a (extensionExponent_order hp basis a)

@[simp] theorem appendBasis_generated {p k d : Nat} (hp : p.Prime)
    (basis : Basis p k d) (a : Vector p k d) :
    (appendBasis hp basis a).generated = extendedSubmodule basis a := rfl

@[simp] theorem appendBasis_length {p k d : Nat} (hp : p.Prime)
    (basis : Basis p k d) (a : Vector p k d) :
    (appendBasis hp basis a).pivots.length =
      basis.pivots.length + extensionExponent hp basis a := by
  simp [appendBasis, extendBasis]

theorem appendBasis_new_pivots_le {p k d : Nat} (hp : p.Prime)
    (basis : Basis p k d) (a : Vector p k d) :
    (appendBasis hp basis a).pivots.length ≤ basis.pivots.length + k := by
  rw [appendBasis_length]
  exact Nat.add_le_add_left (extensionExponent_le hp basis a) _

noncomputable def buildSuffix {p k d : Nat} (hp : p.Prime) :
    List (Vector p k d) → Basis p k d
  | [] => emptyBasis p k d hp
  | a :: rest => appendBasis hp (buildSuffix hp rest) a

/-- The constructed basis spans exactly the input list. -/
theorem buildSuffix_generated {p k d : Nat} (hp : p.Prime)
    (vectors : List (Vector p k d)) :
    (buildSuffix hp vectors).generated =
      Submodule.span (Ring p k) {x | x ∈ vectors} := by
  classical
  induction vectors with
  | nil => simp [buildSuffix, emptyBasis]
  | cons a rest ih =>
      rw [buildSuffix, appendBasis_generated]
      change (buildSuffix hp rest).generated ⊔ Submodule.span (Ring p k) {a} = _
      rw [ih]
      calc
        Submodule.span (Ring p k) {x | x ∈ rest} ⊔ Submodule.span (Ring p k) {a} =
            Submodule.span (Ring p k) {a} ⊔ Submodule.span (Ring p k) {x | x ∈ rest} :=
          sup_comm _ _
        _ = Submodule.span (Ring p k) (insert a {x | x ∈ rest}) :=
          (Submodule.span_insert a {x | x ∈ rest}).symm
        _ = Submodule.span (Ring p k) {x | x ∈ a :: rest} := by
          congr 1
          ext x
          simp only [Set.mem_insert_iff, Set.mem_setOf_eq, List.mem_cons]

/-- Complete interval-membership correctness, with at most `d` row reductions per query. -/
theorem query_complete {p k d : Nat} (hp : p.Prime)
    (vectors : List (Vector p k d)) (target : Vector p k d) :
    ∃ answer : Bool, ∃ derivation : Derivation (buildSuffix hp vectors) target answer,
      (answer = true ↔
        target ∈ Submodule.span (Ring p k) {x | x ∈ vectors}) ∧
      derivation.reductions ≤ d := by
  rcases exists_correct_answer (buildSuffix hp vectors) hp.one_lt target with
    ⟨answer, derivation, hcorrect, hcost⟩
  refine ⟨answer, derivation, ?_, hcost⟩
  rw [← buildSuffix_generated hp vectors]
  exact hcorrect

noncomputable def extensionReductions {p k d h : Nat} (basis : Basis p k d) (hp : p.Prime)
    (a : Vector p k d) (_horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) : Nat :=
  ∑ index : Fin h,
    (chainDerivation basis hp.one_lt a index).reductions

theorem extensionReductions_le {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    extensionReductions basis hp a horder ≤ h * d := by
  unfold extensionReductions
  calc
    (∑ index : Fin h, (chainDerivation basis hp.one_lt a index).reductions) ≤
        ∑ _index : Fin h, d := by
      apply Finset.sum_le_sum
      intro index hindex
      exact chainDerivation_reductions_le basis hp.one_lt a index
    _ = h * d := by simp

/-- One suffix extension performs at most `k*d` reductions. -/
theorem append_reductions_le {p k d : Nat} (hp : p.Prime)
    (basis : Basis p k d) (a : Vector p k d) :
    extensionReductions basis hp a (extensionExponent_order hp basis a) ≤ k * d := by
  exact (extensionReductions_le basis hp a _).trans
    (Nat.mul_le_mul_right d (extensionExponent_le hp basis a))

/-- With length-`d` row operations, one suffix extension touches at most `k*d²` cells. -/
theorem append_cell_operations_le {p k d : Nat} (hp : p.Prime)
    (basis : Basis p k d) (a : Vector p k d) :
    extensionReductions basis hp a (extensionExponent_order hp basis a) * d ≤ k * d * d :=
  Nat.mul_le_mul_right d (append_reductions_le hp basis a)

end CompositeModulusBasis.StaticSuffix
