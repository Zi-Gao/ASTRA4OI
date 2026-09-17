import LeanVerification.BasisQuery
import LeanVerification.CyclicQuotient
import LeanVerification.OrderedInsertion
import Mathlib.Tactic

/-!
# Successive normal forms of one cyclic quotient extension

For a complete suffix basis `H` and a new vector `a`, repeatedly normalize
`a, p*a, ...` modulo `H`.  This file proves that the residuals represent the
correct quotient powers, are nonzero exactly below the quotient exponent, and
have strictly increasing leading slots.  These are the mathematical facts used
to rule out same-timestamp collisions in insertion.
-/

namespace CompositeModulusBasis.CyclicExtension

open BasisQuery CyclicQuotient DigitCardinality OrderedInsertion PadicEchelon

noncomputable def normalAnswer {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (x : Vector p k d) : Bool :=
  Classical.choose (derivation_exists basis hp x)

noncomputable def normalDerivation {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (x : Vector p k d) : Derivation basis x (normalAnswer basis hp x) :=
  Classical.choose (Classical.choose_spec (derivation_exists basis hp x))

noncomputable def normalResidual {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (x : Vector p k d) : Vector p k d :=
  (normalDerivation basis hp x).finalResidual

theorem normal_reductions_le {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (x : Vector p k d) : (normalDerivation basis hp x).reductions ≤ d :=
  Classical.choose_spec (Classical.choose_spec (derivation_exists basis hp x))

theorem normal_zero_iff_mem {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (x : Vector p k d) : normalResidual basis hp x = 0 ↔ x ∈ basis.submodule :=
  (normalDerivation basis hp x).final_zero_iff_mem basis hp

theorem normal_mkQ_eq {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (x : Vector p k d) :
    basis.submodule.mkQ (normalResidual basis hp x) = basis.submodule.mkQ x :=
  (normalDerivation basis hp x).mkQ_final_eq_input

/-- A row carrying source layer `e`: modulo the newer suffix it is a unit
multiple of `p^e a`.  This formulation is stable under every elementary row
operation used by timestamped insertion. -/
def LayerRepresentative {p k d : Nat}
    (submodule : Submodule (Ring p k) (Vector p k d))
    (a : Vector p k d) (e : Nat) (x : Vector p k d) : Prop :=
  ∃ unit : (Ring p k)ˣ,
    x - (unit : Ring p k) • (((p ^ e : Nat) : Ring p k) • a) ∈ submodule

theorem LayerRepresentative.mono {p k d : Nat}
    {small large : Submodule (Ring p k) (Vector p k d)}
    (hle : small ≤ large) {a x : Vector p k d} {e : Nat}
    (hx : LayerRepresentative small a e x) :
    LayerRepresentative large a e x := by
  rcases hx with ⟨unit, hx⟩
  exact ⟨unit, hle hx⟩

theorem LayerRepresentative.sub_mem {p k d : Nat}
    {submodule : Submodule (Ring p k) (Vector p k d)}
    {a x z : Vector p k d} {e : Nat}
    (hx : LayerRepresentative submodule a e x) (hz : z ∈ submodule) :
    LayerRepresentative submodule a e (x - z) := by
  rcases hx with ⟨unit, hx⟩
  refine ⟨unit, ?_⟩
  have hmem := submodule.sub_mem hx hz
  convert hmem using 1
  abel

theorem LayerRepresentative.unit_smul {p k d : Nat}
    {submodule : Submodule (Ring p k) (Vector p k d)}
    {a x : Vector p k d} {e : Nat}
    (scale : (Ring p k)ˣ) (hx : LayerRepresentative submodule a e x) :
    LayerRepresentative submodule a e ((scale : Ring p k) • x) := by
  rcases hx with ⟨unit, hx⟩
  refine ⟨scale * unit, ?_⟩
  have hmem := submodule.smul_mem (scale : Ring p k) hx
  convert hmem using 1
  module

theorem LayerRepresentative.mkQ_eq {p k d : Nat}
    {submodule : Submodule (Ring p k) (Vector p k d)}
    {a x : Vector p k d} {e : Nat}
    (hx : LayerRepresentative submodule a e x) :
    ∃ unit : (Ring p k)ˣ,
      submodule.mkQ x =
        (unit : Ring p k) • (p ^ e • submodule.mkQ a) := by
  rcases hx with ⟨unit, hx⟩
  refine ⟨unit, ?_⟩
  have hzero := (Submodule.Quotient.mk_eq_zero submodule).2 hx
  change submodule.mkQ
      (x - (unit : Ring p k) • (((p ^ e : Nat) : Ring p k) • a)) = 0 at hzero
  rw [map_sub, map_smul, map_smul] at hzero
  rw [sub_eq_zero] at hzero
  rw [← Nat.cast_smul_eq_nsmul (Ring p k)]
  exact hzero

theorem LayerRepresentative.ne_zero_of_lt {p k d h : Nat}
    (hp : p.Prime)
    {submodule : Submodule (Ring p k) (Vector p k d)}
    {a x : Vector p k d} {e : Nat}
    (horder : addOrderOf (submodule.mkQ a) = p ^ h)
    (he : e < h) (hx : LayerRepresentative submodule a e x) : x ≠ 0 := by
  rcases hx.mkQ_eq with ⟨unit, hcoset⟩
  have hpowerNe : p ^ e • submodule.mkQ a ≠ 0 :=
    (nsmul_pow_ne_zero_iff hp _ horder).2 he
  intro hzero
  have hscaledZero : (unit : Ring p k) • (p ^ e • submodule.mkQ a) = 0 := by
    rw [← hcoset, hzero, map_zero]
  apply hpowerNe
  have hback := congrArg
    (((unit⁻¹ : (Ring p k)ˣ) : Ring p k) • ·) hscaledZero
  simpa [← mul_smul] using hback

theorem LayerRepresentative.mem_of_exponent_le {p k d h : Nat}
    (hp : p.Prime)
    {submodule : Submodule (Ring p k) (Vector p k d)}
    {a x : Vector p k d} {e : Nat}
    (horder : addOrderOf (submodule.mkQ a) = p ^ h)
    (he : h ≤ e) (hx : LayerRepresentative submodule a e x) :
    x ∈ submodule := by
  rcases hx.mkQ_eq with ⟨unit, hcoset⟩
  have hpower : p ^ e • submodule.mkQ a = 0 := by
    by_contra hne
    have := (nsmul_pow_ne_zero_iff hp _ horder).1 hne
    omega
  apply (Submodule.Quotient.mk_eq_zero submodule).1
  change submodule.mkQ x = 0
  rw [hcoset, hpower, smul_zero]

/-- Each successor is the normal form of `p` times the previous residual. -/
noncomputable def residualChain {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) : Nat → Vector p k d
  | 0 => normalResidual basis hp a
  | e + 1 => normalResidual basis hp (p • residualChain basis hp a e)

noncomputable def chainDerivation {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) : (e : Nat) →
      Derivation basis
        (match e with | 0 => a | n + 1 => p • residualChain basis hp a n)
        (normalAnswer basis hp (match e with | 0 => a | n + 1 => p • residualChain basis hp a n))
  | 0 => normalDerivation basis hp a
  | _ + 1 => normalDerivation basis hp _

theorem chainDerivation_reductions_le {p k d : Nat} (basis : Basis p k d)
    (hp : 1 < p) (a : Vector p k d) (e : Nat) :
    (chainDerivation basis hp a e).reductions ≤ d := by
  cases e with
  | zero => exact normal_reductions_le basis hp a
  | succ e => exact normal_reductions_le basis hp _

@[simp] theorem residualChain_zero {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) : residualChain basis hp a 0 = normalResidual basis hp a := rfl

@[simp] theorem residualChain_succ {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) (e : Nat) :
    residualChain basis hp a (e + 1) =
      normalResidual basis hp (p • residualChain basis hp a e) := rfl

/-- The recursive residual still represents `p^e a` in the quotient. -/
theorem mkQ_residualChain {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) (e : Nat) :
    basis.submodule.mkQ (residualChain basis hp a e) =
      p ^ e • basis.submodule.mkQ a := by
  induction e with
  | zero => simpa using normal_mkQ_eq basis hp a
  | succ e ih =>
      rw [residualChain_succ, normal_mkQ_eq, map_nsmul, ih]
      simp [pow_succ, ← mul_nsmul, Nat.mul_comm]

theorem residualChain_sub_layer_mem {p k d : Nat}
    (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) (e : Nat) :
    residualChain basis hp a e -
      (((p ^ e : Nat) : Ring p k) • a) ∈ basis.submodule := by
  apply (Submodule.Quotient.mk_eq_zero basis.submodule).1
  have hmap : basis.submodule.mkQ (((p ^ e : Nat) : Ring p k) • a) =
      ((p ^ e : Nat) : Ring p k) • basis.submodule.mkQ a :=
    map_smul basis.submodule.mkQ _ _
  change basis.submodule.mkQ
      (residualChain basis hp a e -
        (((p ^ e : Nat) : Ring p k) • a)) = 0
  rw [map_sub, mkQ_residualChain, hmap]
  rw [Nat.cast_smul_eq_nsmul]
  exact sub_self _

theorem residualChain_layerRepresentative {p k d : Nat}
    (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) (e : Nat) :
    LayerRepresentative basis.submodule a e (residualChain basis hp a e) := by
  refine ⟨1, ?_⟩
  simpa using residualChain_sub_layer_mem basis hp a e

theorem residualChain_zero_iff {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) (e : Nat) :
    residualChain basis hp a e = 0 ↔ p ^ e • basis.submodule.mkQ a = 0 := by
  constructor
  · intro hzero
    rw [← mkQ_residualChain basis hp a e, hzero, map_zero]
  · intro hcoset
    cases e with
    | zero =>
        rw [residualChain_zero, normal_zero_iff_mem]
        exact (Submodule.Quotient.mk_eq_zero basis.submodule).1 (by simpa using hcoset)
    | succ e =>
        rw [residualChain_succ, normal_zero_iff_mem]
        apply (Submodule.Quotient.mk_eq_zero basis.submodule).1
        change p • basis.submodule.mkQ (residualChain basis hp a e) = 0
        rw [mkQ_residualChain]
        simpa [← mul_nsmul, pow_succ, Nat.mul_comm] using hcoset

/-- Exactly the first `h` residuals survive when the quotient order is `p^h`. -/
theorem residualChain_ne_zero_iff {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) (e : Nat) :
    residualChain basis hp.one_lt a e ≠ 0 ↔ e < h := by
  rw [ne_eq, residualChain_zero_iff]
  exact nsmul_pow_ne_zero_iff hp _ horder

noncomputable def residualSlot {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) (e : Nat) (hne : residualChain basis hp a e ≠ 0) : Slot d k :=
  Classical.choose (exists_hasLead hp hne)

theorem residualSlot_hasLead {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) (e : Nat) (hne : residualChain basis hp a e ≠ 0) :
    HasLead (residualChain basis hp a e) (residualSlot basis hp a e hne) :=
  Classical.choose_spec (exists_hasLead hp hne)

/-- Consecutive nonzero residuals have strictly increasing slots. -/
theorem residualSlot_lt_succ {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) (e : Nat)
    (hne : residualChain basis hp a e ≠ 0)
    (hsucc : residualChain basis hp a (e + 1) ≠ 0) :
    Slot.lt (residualSlot basis hp a e hne)
      (residualSlot basis hp a (e + 1) hsucc) := by
  have hstep := Derivation.p_nsmul_final_strictly_later basis hp
    (residualSlot_hasLead basis hp a e hne)
    (normalDerivation basis hp (p • residualChain basis hp a e))
  have hstep' : residualChain basis hp a (e + 1) = 0 ∨
      ∃ slot : Slot d k, HasLead (residualChain basis hp a (e + 1)) slot ∧
        Slot.lt (residualSlot basis hp a e hne) slot := by
    simpa [residualChain_succ, normalResidual] using hstep
  rcases hstep' with hzero | ⟨slot, hlead, hlater⟩
  · exact False.elim (hsucc hzero)
  · have hslot : slot = residualSlot basis hp a (e + 1) hsucc :=
      hlead.unique hp (residualSlot_hasLead basis hp a (e + 1) hsucc)
    simpa [hslot] using hlater

theorem residualSlot_missing {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (a : Vector p k d) (e : Nat) (hne : residualChain basis hp a e ≠ 0) :
    ∀ pivot ∈ basis.pivots, pivot.slot ≠ residualSlot basis hp a e hne := by
  have hshape := (chainDerivation basis hp a e).final_zero_or_missing
  have hshape' : residualChain basis hp a e = 0 ∨
      ∃ slot : Slot d k, HasLead (residualChain basis hp a e) slot ∧
        ∀ pivot ∈ basis.pivots, pivot.slot ≠ slot := by
    cases e <;> simpa [chainDerivation, residualChain, normalResidual] using hshape
  rcases hshape' with hzero | ⟨slot, hlead, hmissing⟩
  · exact False.elim (hne hzero)
  · have hslot : slot = residualSlot basis hp a e hne :=
      hlead.unique hp (residualSlot_hasLead basis hp a e hne)
    simpa [hslot] using hmissing

/-- Strict increase extends from consecutive layers to any two retained layers. -/
theorem residualSlot_lt_of_lt {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h)
    {e f : Nat} (hef : e < f) (hf : f < h) :
    Slot.lt
      (residualSlot basis hp.one_lt a e
        ((residualChain_ne_zero_iff basis hp a horder e).2 (lt_trans hef hf)))
      (residualSlot basis hp.one_lt a f
        ((residualChain_ne_zero_iff basis hp a horder f).2 hf)) := by
  induction f with
  | zero => omega
  | succ f ih =>
      by_cases heq : e = f
      · subst e
        apply residualSlot_lt_succ
      · have hef' : e < f := by omega
        have hf' : f < h := by omega
        exact Slot.lt_trans (ih hef' hf')
          (residualSlot_lt_succ basis hp.one_lt a f
            ((residualChain_ne_zero_iff basis hp a horder f).2 hf')
            ((residualChain_ne_zero_iff basis hp a horder (f + 1)).2 hf))

/-- Every missing-lead representative of a nonzero cyclic layer has the same
slot as the canonical residual, even when its layer is scaled by an arbitrary
unit. -/
theorem layerRepresentative_slot_eq {p k d h : Nat}
    (basis : Basis p k d) (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h)
    {e : Nat} (he : e < h) {x : Vector p k d} {slot : Slot d k}
    (hx : LayerRepresentative basis.submodule a e x)
    (xLead : HasLead x slot)
    (xMissing : ∀ pivot ∈ basis.pivots, pivot.slot ≠ slot) :
    slot = residualSlot basis hp.one_lt a e
      ((residualChain_ne_zero_iff basis hp a horder e).2 he) := by
  rcases hx with ⟨unit, hx⟩
  let scaled : Vector p k d := ((unit⁻¹ : (Ring p k)ˣ) : Ring p k) • x
  have scaledLead : HasLead scaled slot := by
    exact xLead.unit_smul hp.one_lt unit⁻¹
  have scaledSubLayer :
      scaled - (((p ^ e : Nat) : Ring p k) • a) ∈ basis.submodule := by
    have hscaled := basis.submodule.smul_mem
      ((unit⁻¹ : (Ring p k)ˣ) : Ring p k) hx
    convert hscaled using 1
    dsimp [scaled]
    rw [smul_sub]
    congr 1
    rw [← mul_smul]
    simp
  let chain := residualChain basis hp.one_lt a e
  have chainSubLayer :
      chain - (((p ^ e : Nat) : Ring p k) • a) ∈ basis.submodule := by
    exact residualChain_sub_layer_mem basis hp.one_lt a e
  have sameCoset : scaled - chain ∈ basis.submodule := by
    have hdiff := basis.submodule.sub_mem scaledSubLayer chainSubLayer
    convert hdiff using 1
    abel
  let hne := (residualChain_ne_zero_iff basis hp a horder e).2 he
  have chainLead : HasLead chain (residualSlot basis hp.one_lt a e hne) := by
    exact residualSlot_hasLead basis hp.one_lt a e hne
  have chainMissing : ∀ pivot ∈ basis.pivots,
      pivot.slot ≠ residualSlot basis hp.one_lt a e hne := by
    exact residualSlot_missing basis hp.one_lt a e hne
  exact basis.missing_coset_lead_unique hp.one_lt
    scaledLead chainLead xMissing chainMissing sameCoset

/-- Distinct surviving source layers necessarily stop at strictly increasing
missing slots, independently of the legal reduction path. -/
theorem layerRepresentative_slot_lt {p k d h : Nat}
    (basis : Basis p k d) (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h)
    {e f : Nat} (hef : e < f) (hf : f < h)
    {x y : Vector p k d} {xSlot ySlot : Slot d k}
    (hx : LayerRepresentative basis.submodule a e x)
    (hy : LayerRepresentative basis.submodule a f y)
    (xLead : HasLead x xSlot) (yLead : HasLead y ySlot)
    (xMissing : ∀ pivot ∈ basis.pivots, pivot.slot ≠ xSlot)
    (yMissing : ∀ pivot ∈ basis.pivots, pivot.slot ≠ ySlot) :
    Slot.lt xSlot ySlot := by
  rw [layerRepresentative_slot_eq basis hp a horder (lt_trans hef hf)
      hx xLead xMissing,
    layerRepresentative_slot_eq basis hp a horder hf hy yLead yMissing]
  exact residualSlot_lt_of_lt basis hp a horder hef hf

theorem layerRepresentative_slots_ne {p k d h : Nat}
    (basis : Basis p k d) (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h)
    {e f : Nat} (he : e < h) (hf : f < h) (hef : e ≠ f)
    {x y : Vector p k d} {xSlot ySlot : Slot d k}
    (hx : LayerRepresentative basis.submodule a e x)
    (hy : LayerRepresentative basis.submodule a f y)
    (xLead : HasLead x xSlot) (yLead : HasLead y ySlot)
    (xMissing : ∀ pivot ∈ basis.pivots, pivot.slot ≠ xSlot)
    (yMissing : ∀ pivot ∈ basis.pivots, pivot.slot ≠ ySlot) :
    xSlot ≠ ySlot := by
  rcases lt_or_gt_of_ne hef with hlt | hgt
  · intro hslot
    subst ySlot
    exact Slot.lt_irrefl _
      (layerRepresentative_slot_lt basis hp a horder hlt hf
        hx hy xLead yLead xMissing yMissing)
  · intro hslot
    subst ySlot
    exact Slot.lt_irrefl _
      (layerRepresentative_slot_lt basis hp a horder hgt he
        hy hx yLead xLead yMissing xMissing)

/-- This is the exact no-same-timestamp-collision theorem used by the scanner:
two distinct source layers that have both reached slots missing from the newer
basis cannot occupy the same slot.  The fact that the layers survive is derived,
not assumed. -/
theorem no_same_slot_of_missing_layers {p k d h : Nat}
    (basis : Basis p k d) (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h)
    {e f : Nat} (hef : e ≠ f)
    {x y : Vector p k d} {xSlot ySlot : Slot d k}
    (hx : LayerRepresentative basis.submodule a e x)
    (hy : LayerRepresentative basis.submodule a f y)
    (xLead : HasLead x xSlot) (yLead : HasLead y ySlot)
    (xMissing : ∀ pivot ∈ basis.pivots, pivot.slot ≠ xSlot)
    (yMissing : ∀ pivot ∈ basis.pivots, pivot.slot ≠ ySlot) :
    xSlot ≠ ySlot := by
  have he : e < h := by
    by_contra hnot
    exact (basis.not_mem_of_missing_lead hp.one_lt xLead xMissing)
      (hx.mem_of_exponent_le hp horder (Nat.le_of_not_gt hnot))
  have hf : f < h := by
    by_contra hnot
    exact (basis.not_mem_of_missing_lead hp.one_lt yLead yMissing)
      (hy.mem_of_exponent_le hp horder (Nat.le_of_not_gt hnot))
  exact layerRepresentative_slots_ne basis hp a horder he hf hef
    hx hy xLead yLead xMissing yMissing

/-- Each retained residual admits exactly the unit normalization used by the table. -/
theorem exists_chainPivot {p k d : Nat} (basis : Basis p k d) (hp : p.Prime)
    (a : Vector p k d) (e : Nat) (hne : residualChain basis hp.one_lt a e ≠ 0) :
    ∃ pivot : PivotRow p k d,
      pivot.slot = residualSlot basis hp.one_lt a e hne ∧
      ∃ unit : (Ring p k)ˣ,
        pivot.row = (unit : Ring p k) • residualChain basis hp.one_lt a e :=
  exists_normalized_pivot hp (residualSlot_hasLead basis hp.one_lt a e hne)

noncomputable def retainedPivot {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) (index : Fin h) :
    PivotRow p k d :=
  Classical.choose (exists_chainPivot basis hp a index
    ((residualChain_ne_zero_iff basis hp a horder index).2 index.isLt))

theorem retainedPivot_slot {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) (index : Fin h) :
    (retainedPivot basis hp a horder index).slot =
      residualSlot basis hp.one_lt a index
        ((residualChain_ne_zero_iff basis hp a horder index).2 index.isLt) :=
  (Classical.choose_spec (exists_chainPivot basis hp a index
    ((residualChain_ne_zero_iff basis hp a horder index).2 index.isLt))).1

theorem retainedPivot_unit {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) (index : Fin h) :
    ∃ unit : (Ring p k)ˣ,
      (retainedPivot basis hp a horder index).row =
        (unit : Ring p k) • residualChain basis hp.one_lt a index :=
  (Classical.choose_spec (exists_chainPivot basis hp a index
    ((residualChain_ne_zero_iff basis hp a horder index).2 index.isLt))).2

noncomputable def retainedPivots {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    List (PivotRow p k d) := List.ofFn (retainedPivot basis hp a horder)

@[simp] theorem retainedPivots_length {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    (retainedPivots basis hp a horder).length = h := by
  simp [retainedPivots]

theorem retainedPivots_ordered {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    Ordered (retainedPivots basis hp a horder) := by
  rw [Ordered, retainedPivots, List.pairwise_ofFn]
  intro left right hleftRight
  rw [retainedPivot_slot, retainedPivot_slot]
  exact residualSlot_lt_of_lt basis hp a horder hleftRight right.isLt

theorem retainedPivots_fresh {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    ∀ added ∈ retainedPivots basis hp a horder,
      ∀ current ∈ basis.pivots, current.slot ≠ added.slot := by
  intro added hadded
  rw [retainedPivots, List.mem_ofFn'] at hadded
  rcases hadded with ⟨index, rfl⟩
  intro current hcurrent
  rw [retainedPivot_slot]
  exact residualSlot_missing basis hp.one_lt a index _ current hcurrent

noncomputable def combinedPivots {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    List (PivotRow p k d) :=
  insertAll (retainedPivots basis hp a horder) basis.pivots

@[simp] theorem combinedPivots_length {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    (combinedPivots basis hp a horder).length = basis.pivots.length + h := by
  simp [combinedPivots]

theorem combinedPivots_ordered {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    Ordered (combinedPivots basis hp a horder) := by
  exact ordered_insertAll _ _ (retainedPivots_ordered basis hp a horder)
    basis.ordered (retainedPivots_fresh basis hp a horder)

@[simp] theorem mem_combinedPivots {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h)
    (pivot : PivotRow p k d) :
    pivot ∈ combinedPivots basis hp a horder ↔
      pivot ∈ retainedPivots basis hp a horder ∨ pivot ∈ basis.pivots := by
  simp [combinedPivots]

def extendedSubmodule {p k d : Nat} (basis : Basis p k d) (a : Vector p k d) :
    Submodule (Ring p k) (Vector p k d) :=
  basis.submodule ⊔ Submodule.span (Ring p k) {a}

def combinedSpan {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    Submodule (Ring p k) (Vector p k d) :=
  Submodule.span (Ring p k) {row | row ∈ rowsOf (combinedPivots basis hp a horder)}

theorem old_le_combinedSpan {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    basis.submodule ≤ combinedSpan basis hp a horder := by
  change basis.generated ≤ combinedSpan basis hp a horder
  rw [basis.generated_eq_span]
  apply Submodule.span_mono
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨pivot, hpivot, rfl⟩
  exact List.mem_map.mpr ⟨pivot, (mem_combinedPivots basis hp a horder pivot).2
    (Or.inr hpivot), rfl⟩

theorem residualChain_mem_extended {p k d : Nat} (basis : Basis p k d)
    (hp : 1 < p) (a : Vector p k d) (e : Nat) :
    residualChain basis hp a e ∈ extendedSubmodule basis a := by
  let power : Vector p k d := p ^ e • a
  have hcoset : basis.submodule.mkQ (residualChain basis hp a e) =
      basis.submodule.mkQ power := by
    rw [mkQ_residualChain]
    exact (map_nsmul basis.submodule.mkQ (p ^ e) a).symm
  have hdifference : residualChain basis hp a e - power ∈ basis.submodule := by
    apply (Submodule.Quotient.mk_eq_zero basis.submodule).1
    change basis.submodule.mkQ (residualChain basis hp a e) -
      basis.submodule.mkQ power = 0
    rw [hcoset, sub_self]
  have hpower : power ∈ Submodule.span (Ring p k) {a} := by
    dsimp [power]
    exact (Submodule.span (Ring p k) {a}).toAddSubgroup.nsmul_mem
      (Submodule.mem_span_singleton_self a) (p ^ e)
  have hdifference' : residualChain basis hp a e - power ∈ extendedSubmodule basis a :=
    (show basis.submodule ≤ extendedSubmodule basis a from le_sup_left) hdifference
  have hpower' : power ∈ extendedSubmodule basis a :=
    (show Submodule.span (Ring p k) {a} ≤ extendedSubmodule basis a from le_sup_right) hpower
  have hsum := (extendedSubmodule basis a).add_mem hdifference' hpower'
  simpa only [sub_add_cancel] using hsum

theorem retainedPivot_mem_extended {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) (index : Fin h) :
    (retainedPivot basis hp a horder index).row ∈ extendedSubmodule basis a := by
  rcases retainedPivot_unit basis hp a horder index with ⟨unit, hunit⟩
  rw [hunit]
  exact (extendedSubmodule basis a).smul_mem _
    (residualChain_mem_extended basis hp.one_lt a index)

theorem combinedSpan_le_extended {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    combinedSpan basis hp a horder ≤ extendedSubmodule basis a := by
  apply Submodule.span_le.2
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨pivot, hpivot, rfl⟩
  rw [mem_combinedPivots] at hpivot
  rcases hpivot with hretained | hold
  · rw [retainedPivots, List.mem_ofFn'] at hretained
    rcases hretained with ⟨index, rfl⟩
    exact retainedPivot_mem_extended basis hp a horder index
  · exact (show basis.submodule ≤ extendedSubmodule basis a from le_sup_left)
      (basis.pivot_mem hold)

theorem extended_le_combinedSpan {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    extendedSubmodule basis a ≤ combinedSpan basis hp a horder := by
  apply sup_le
  · exact old_le_combinedSpan basis hp a horder
  · apply Submodule.span_le.2
    intro value hvalue
    have hvalueEq : value = a := by simpa using hvalue
    subst value
    cases h with
    | zero =>
        have horderOne : addOrderOf (basis.submodule.mkQ a) = 1 := by simpa using horder
        have hcosetZero : basis.submodule.mkQ a = 0 :=
          AddMonoid.addOrderOf_eq_one_iff.mp horderOne
        exact old_le_combinedSpan basis hp a horder
          ((Submodule.Quotient.mk_eq_zero basis.submodule).1 hcosetZero)
    | succ h =>
        let first : Fin (h + 1) := ⟨0, Nat.zero_lt_succ h⟩
        let firstPivot := retainedPivot basis hp a horder first
        have hfirstRetained : firstPivot ∈ retainedPivots basis hp a horder := by
          rw [retainedPivots, List.mem_ofFn']
          exact ⟨first, rfl⟩
        have hfirstCombined : firstPivot ∈ combinedPivots basis hp a horder :=
          (mem_combinedPivots basis hp a horder firstPivot).2 (Or.inl hfirstRetained)
        have hfirstRow : firstPivot.row ∈ combinedSpan basis hp a horder := by
          apply Submodule.subset_span
          exact List.mem_map.mpr ⟨firstPivot, hfirstCombined, rfl⟩
        rcases retainedPivot_unit basis hp a horder first with ⟨unit, hunit⟩
        have hresidual : residualChain basis hp.one_lt a 0 ∈
            combinedSpan basis hp a horder := by
          have hscaled := (combinedSpan basis hp a horder).smul_mem
            (↑(unit⁻¹) : Ring p k) hfirstRow
          rw [hunit] at hscaled
          simpa [first, smul_smul] using hscaled
        have hdifference : a - residualChain basis hp.one_lt a 0 ∈ basis.submodule := by
          simpa [residualChain, normalResidual] using
            (normalDerivation basis hp.one_lt a).input_sub_final_mem
        have hdifference' : a - residualChain basis hp.one_lt a 0 ∈
            combinedSpan basis hp a horder :=
          old_le_combinedSpan basis hp a horder hdifference
        have hsum := (combinedSpan basis hp a horder).add_mem hdifference' hresidual
        change a ∈ combinedSpan basis hp a horder
        simpa only [sub_add_cancel] using hsum

theorem extended_eq_combinedSpan {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    extendedSubmodule basis a = combinedSpan basis hp a horder :=
  le_antisymm (extended_le_combinedSpan basis hp a horder)
    (combinedSpan_le_extended basis hp a horder)

theorem card_extended {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) :
    Nat.card (extendedSubmodule basis a) =
      p ^ (combinedPivots basis hp a horder).length := by
  rw [combinedPivots_length]
  calc
    Nat.card (extendedSubmodule basis a) =
        Nat.card basis.submodule * addOrderOf (basis.submodule.mkQ a) :=
      card_sup_span_singleton basis.submodule a
    _ = p ^ basis.pivots.length * p ^ h := by
      have hcard : Nat.card basis.submodule = p ^ basis.pivots.length :=
        basis.card_generated
      rw [hcard, horder]
    _ = p ^ (basis.pivots.length + h) := (pow_add p _ _).symm

/-- One-vector extension produces a new complete normalized cardinal basis. -/
noncomputable def extendBasis {p k d h : Nat} (basis : Basis p k d)
    (hp : p.Prime) (a : Vector p k d)
    (horder : addOrderOf (basis.submodule.mkQ a) = p ^ h) : Basis p k d where
  pivots := combinedPivots basis hp a horder
  ordered := combinedPivots_ordered basis hp a horder
  generated := extendedSubmodule basis a
  generated_eq_span := extended_eq_combinedSpan basis hp a horder
  card_generated := card_extended basis hp a horder

end CompositeModulusBasis.CyclicExtension
