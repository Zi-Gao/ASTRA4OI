import LeanVerification.CyclicExtension
import Mathlib.Tactic

/-!
# Cyclic extension from arbitrary legal residual rows

The fast timestamp algorithm need not choose the same normal forms as
`residualChain`.  This module proves that any ordered, fresh family containing
one unit-scaled representative for every surviving cyclic layer produces the
same extended submodule and cardinal basis.
-/

namespace CompositeModulusBasis.ArbitraryExtension

open BasisQuery CyclicExtension CyclicQuotient DigitCardinality
  OrderedInsertion PadicEchelon

def familyPivots {p k d h : Nat} (family : Fin h → PivotRow p k d) :
    List (PivotRow p k d) := List.ofFn family

def familyCombined {p k d h : Nat} (basis : Basis p k d)
    (family : Fin h → PivotRow p k d) : List (PivotRow p k d) :=
  insertAll (familyPivots family) basis.pivots

@[simp] theorem familyPivots_length {p k d h : Nat}
    (family : Fin h → PivotRow p k d) :
    (familyPivots family).length = h := by
  simp [familyPivots]

@[simp] theorem familyCombined_length {p k d h : Nat} (basis : Basis p k d)
    (family : Fin h → PivotRow p k d) :
    (familyCombined basis family).length = basis.pivots.length + h := by
  simp [familyCombined]

@[simp] theorem mem_familyCombined {p k d h : Nat} (basis : Basis p k d)
    (family : Fin h → PivotRow p k d) (pivot : PivotRow p k d) :
    pivot ∈ familyCombined basis family ↔
      pivot ∈ familyPivots family ∨ pivot ∈ basis.pivots := by
  simp [familyCombined]

theorem familyCombined_ordered {p k d h : Nat} (basis : Basis p k d)
    (family : Fin h → PivotRow p k d)
    (hordered : Ordered (familyPivots family))
    (hfresh : ∀ added ∈ familyPivots family,
      ∀ current ∈ basis.pivots, current.slot ≠ added.slot) :
    Ordered (familyCombined basis family) :=
  ordered_insertAll _ _ hordered basis.ordered hfresh

theorem family_ordered_of_layers {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (family : Fin h → PivotRow p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h)
    (hrepresentative : ∀ index : Fin h,
      LayerRepresentative basis.submodule a index (family index).row)
    (hmissing : ∀ index : Fin h, ∀ current ∈ basis.pivots,
      current.slot ≠ (family index).slot) :
    Ordered (familyPivots family) := by
  rw [Ordered, familyPivots, List.pairwise_ofFn]
  intro left right hleft
  exact layerRepresentative_slot_lt basis hp a horder hleft right.isLt
    (hrepresentative left) (hrepresentative right)
    ((family left).hasLead hp.one_lt) ((family right).hasLead hp.one_lt)
    (hmissing left) (hmissing right)

theorem family_fresh_of_missing {p k d h : Nat} (basis : Basis p k d)
    (family : Fin h → PivotRow p k d)
    (hmissing : ∀ index : Fin h, ∀ current ∈ basis.pivots,
      current.slot ≠ (family index).slot) :
    ∀ added ∈ familyPivots family,
      ∀ current ∈ basis.pivots, current.slot ≠ added.slot := by
  intro added hadded
  rw [familyPivots, List.mem_ofFn'] at hadded
  rcases hadded with ⟨index, rfl⟩
  exact hmissing index

def familySpan {p k d h : Nat} (basis : Basis p k d)
    (family : Fin h → PivotRow p k d) :
    Submodule (Ring p k) (Vector p k d) :=
  Submodule.span (Ring p k) {row | row ∈ rowsOf (familyCombined basis family)}

theorem old_le_familySpan {p k d h : Nat} (basis : Basis p k d)
    (family : Fin h → PivotRow p k d) :
    basis.submodule ≤ familySpan basis family := by
  change basis.generated ≤ familySpan basis family
  rw [basis.generated_eq_span]
  apply Submodule.span_mono
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨pivot, hpivot, rfl⟩
  exact List.mem_map.mpr ⟨pivot,
    (mem_familyCombined basis family pivot).2 (Or.inr hpivot), rfl⟩

theorem family_row_mem {p k d h : Nat} (basis : Basis p k d)
    (a : Vector p k d) (family : Fin h → PivotRow p k d)
    (hrepresentative : ∀ index : Fin h,
      LayerRepresentative basis.submodule a index (family index).row)
    (index : Fin h) :
    (family index).row ∈ extendedSubmodule basis a := by
  rcases hrepresentative index with ⟨unit, hdifference⟩
  let layer : Vector p k d := (((p ^ (index : Nat) : Nat) : Ring p k) • a)
  have hdifference' : (family index).row - (unit : Ring p k) • layer ∈
      extendedSubmodule basis a :=
    (show basis.submodule ≤ extendedSubmodule basis a from le_sup_left) hdifference
  have hlayer : layer ∈ extendedSubmodule basis a := by
    apply (show Submodule.span (Ring p k) {a} ≤ extendedSubmodule basis a from le_sup_right)
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  have hscaled := (extendedSubmodule basis a).smul_mem (unit : Ring p k) hlayer
  have hsum := (extendedSubmodule basis a).add_mem hdifference' hscaled
  simpa [layer] using hsum

theorem familySpan_le_extended {p k d h : Nat} (basis : Basis p k d)
    (a : Vector p k d) (family : Fin h → PivotRow p k d)
    (hrepresentative : ∀ index : Fin h,
      LayerRepresentative basis.submodule a index (family index).row) :
    familySpan basis family ≤ extendedSubmodule basis a := by
  apply Submodule.span_le.2
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨pivot, hpivot, rfl⟩
  rw [mem_familyCombined] at hpivot
  rcases hpivot with hfamily | hold
  · rw [familyPivots, List.mem_ofFn'] at hfamily
    rcases hfamily with ⟨index, rfl⟩
    exact family_row_mem basis a family hrepresentative index
  · exact (show basis.submodule ≤ extendedSubmodule basis a from le_sup_left)
      (basis.pivot_mem hold)

theorem extended_le_familySpan {p k d h : Nat} (basis : Basis p k d)
    (a : Vector p k d) (family : Fin h → PivotRow p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h)
    (hrepresentative : ∀ index : Fin h,
      LayerRepresentative basis.submodule a index (family index).row) :
    extendedSubmodule basis a ≤ familySpan basis family := by
  apply sup_le
  · exact old_le_familySpan basis family
  · apply Submodule.span_le.2
    intro value hvalue
    have hvalueEq : value = a := by simpa using hvalue
    subst value
    cases h with
    | zero =>
        have horderOne : addOrderOf (basis.submodule.mkQ a) = 1 := by simpa using horder
        have hcosetZero : basis.submodule.mkQ a = 0 :=
          AddMonoid.addOrderOf_eq_one_iff.mp horderOne
        exact old_le_familySpan basis family
          ((Submodule.Quotient.mk_eq_zero basis.submodule).1 hcosetZero)
    | succ h =>
        let first : Fin (h + 1) := ⟨0, Nat.zero_lt_succ h⟩
        have hfirstMem : family first ∈ familyPivots family := by
          rw [familyPivots, List.mem_ofFn']
          exact ⟨first, rfl⟩
        have hfirstCombined : family first ∈ familyCombined basis family :=
          (mem_familyCombined basis family _).2 (Or.inl hfirstMem)
        have hfirstRow : (family first).row ∈ familySpan basis family := by
          apply Submodule.subset_span
          exact List.mem_map.mpr ⟨family first, hfirstCombined, rfl⟩
        rcases hrepresentative first with ⟨unit, hdifference⟩
        have hdifference' : (family first).row - (unit : Ring p k) • a ∈
            familySpan basis family := by
          have hold := old_le_familySpan basis family hdifference
          simpa [first] using hold
        have hscaledA : (unit : Ring p k) • a ∈ familySpan basis family := by
          have hsub := (familySpan basis family).sub_mem hfirstRow hdifference'
          simpa only [sub_sub_cancel] using hsub
        have hback := (familySpan basis family).smul_mem
          ((unit⁻¹ : (Ring p k)ˣ) : Ring p k) hscaledA
        simpa [← mul_smul] using hback

theorem extended_eq_familySpan {p k d h : Nat} (basis : Basis p k d)
    (a : Vector p k d) (family : Fin h → PivotRow p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h)
    (hrepresentative : ∀ index : Fin h,
      LayerRepresentative basis.submodule a index (family index).row) :
    extendedSubmodule basis a = familySpan basis family :=
  le_antisymm
    (extended_le_familySpan basis a family horder hrepresentative)
    (familySpan_le_extended basis a family hrepresentative)

theorem family_card_extended {p k d h : Nat} (basis : Basis p k d)
    (a : Vector p k d) (family : Fin h → PivotRow p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    Nat.card (extendedSubmodule basis a) =
      p ^ (familyCombined basis family).length := by
  rw [familyCombined_length]
  calc
    Nat.card (extendedSubmodule basis a) =
        Nat.card basis.submodule * addOrderOf (basis.submodule.mkQ a) :=
      card_sup_span_singleton basis.submodule a
    _ = p ^ basis.pivots.length * p ^ h := by
      have hcard : Nat.card basis.submodule = p ^ basis.pivots.length :=
        basis.card_generated
      rw [hcard, horder]
    _ = p ^ (basis.pivots.length + h) := (pow_add p _ _).symm

/-- The generalized extension constructor used by a settled timestamp batch. -/
noncomputable def basisFromLayerFamily {p k d h : Nat} (basis : Basis p k d)
    (a : Vector p k d)
    (family : Fin h → PivotRow p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h)
    (hrepresentative : ∀ index : Fin h,
      LayerRepresentative basis.submodule a index (family index).row)
    (hordered : Ordered (familyPivots family))
    (hfresh : ∀ added ∈ familyPivots family,
      ∀ current ∈ basis.pivots, current.slot ≠ added.slot) : Basis p k d where
  pivots := familyCombined basis family
  ordered := familyCombined_ordered basis family hordered hfresh
  generated := extendedSubmodule basis a
  generated_eq_span := extended_eq_familySpan basis a family horder hrepresentative
  card_generated := family_card_extended basis a family horder

/-- A terminal batch only has to certify the layer identity and that every row
stopped at a slot missing from the newer suffix basis; ordering and freshness
then follow from intrinsic quotient leads. -/
noncomputable def basisFromSettledLayers {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (family : Fin h → PivotRow p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h)
    (hrepresentative : ∀ index : Fin h,
      LayerRepresentative basis.submodule a index (family index).row)
    (hmissing : ∀ index : Fin h, ∀ current ∈ basis.pivots,
      current.slot ≠ (family index).slot) : Basis p k d :=
  basisFromLayerFamily basis a family horder hrepresentative
    (family_ordered_of_layers basis hp a family horder hrepresentative hmissing)
    (family_fresh_of_missing basis family hmissing)

end CompositeModulusBasis.ArbitraryExtension
