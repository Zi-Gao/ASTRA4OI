import LeanVerification.PadicEchelon
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.Tactic

/-!
# The cyclic quotient created by one input vector

Adding one vector to a suffix submodule creates a cyclic additive quotient.
This file proves that its order is exactly `p^h` for some `h ≤ k`, and that the
nonzero power layers are precisely `e < h`.
-/

namespace CompositeModulusBasis.CyclicQuotient

open PadicEchelon

theorem modulus_nsmul_eq_zero {p k : Nat} {A : Type*} [AddCommGroup A]
    [Module (Ring p k) A] (x : A) : p ^ k • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (Ring p k)]
  have hcast : ((p ^ k : Nat) : Ring p k) = 0 :=
    (ZMod.natCast_eq_zero_iff (p ^ k) (p ^ k)).2 dvd_rfl
  rw [hcast, zero_smul]

/-- The additive order of any quotient coset divides the ring characteristic. -/
theorem quotient_order_dvd {p k d : Nat}
    (submodule : Submodule (Ring p k) (Vector p k d)) (x : Vector p k d) :
    addOrderOf (submodule.mkQ x) ∣ p ^ k := by
  rw [addOrderOf_dvd_iff_nsmul_eq_zero]
  exact modulus_nsmul_eq_zero _

/-- Passing to a quotient by a larger submodule can only decrease the order of
the represented coset. -/
theorem quotient_order_dvd_of_le {p k d : Nat}
    (small large : Submodule (Ring p k) (Vector p k d))
    (hle : small ≤ large) (x : Vector p k d) :
    addOrderOf (large.mkQ x) ∣ addOrderOf (small.mkQ x) := by
  rw [addOrderOf_dvd_iff_nsmul_eq_zero]
  rw [← map_nsmul]
  apply (Submodule.Quotient.mk_eq_zero large).2
  apply hle
  apply (Submodule.Quotient.mk_eq_zero small).1
  change small.mkQ (addOrderOf (small.mkQ x) • x) = 0
  rw [map_nsmul]
  exact addOrderOf_nsmul_eq_zero (small.mkQ x)

/-- In prime-power quotients, enlarging the represented suffix can only lower
the p-power exponent of a coset. -/
theorem quotient_exponent_anti {p k d smallExponent largeExponent : Nat}
    (hp : p.Prime)
    (small large : Submodule (Ring p k) (Vector p k d))
    (hle : small ≤ large) (x : Vector p k d)
    (hsmall : addOrderOf (small.mkQ x) = p ^ smallExponent)
    (hlarge : addOrderOf (large.mkQ x) = p ^ largeExponent) :
    largeExponent ≤ smallExponent := by
  have hdvd := quotient_order_dvd_of_le small large hle x
  rw [hlarge, hsmall] at hdvd
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd

/-- For prime `p`, every quotient coset has order `p^h`, with `h ≤ k`. -/
theorem exists_quotient_order_exponent {p k d : Nat} (hp : p.Prime)
    (submodule : Submodule (Ring p k) (Vector p k d)) (x : Vector p k d) :
    ∃ h ≤ k, addOrderOf (submodule.mkQ x) = p ^ h := by
  exact (Nat.dvd_prime_pow hp).1 (quotient_order_dvd submodule x)

/-- Once the quotient order is `p^h`, exactly its first `h` p-power layers are nonzero. -/
theorem nsmul_pow_ne_zero_iff {p h e : Nat} (hp : p.Prime)
    {A : Type*} [AddCommGroup A] (x : A) (horder : addOrderOf x = p ^ h) :
    p ^ e • x ≠ 0 ↔ e < h := by
  have hzero : p ^ e • x = 0 ↔ h ≤ e := by
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, horder,
      Nat.pow_dvd_pow_iff_le_right hp.one_lt]
  exact not_congr hzero |>.trans (Nat.not_le)

/-- A one-generator `ZMod N` submodule is the same additive cyclic subgroup. -/
theorem span_singleton_toAddSubgroup {N : Nat} {A : Type*} [AddCommGroup A]
    [Module (ZMod N) A] (x : A) :
    (Submodule.span (ZMod N) {x}).toAddSubgroup = AddSubgroup.zmultiples x := by
  apply le_antisymm
  · change Submodule.span (ZMod N) {x} ≤
      AddSubgroup.toZModSubmodule N (AddSubgroup.zmultiples x)
    apply Submodule.span_le.2
    simp
  · rw [AddSubgroup.zmultiples_le]
    exact Submodule.mem_span_singleton_self x

/-- Therefore its cardinality is exactly the additive order of the generator. -/
theorem card_span_singleton_zmod {N : Nat} {A : Type*} [AddCommGroup A]
    [Module (ZMod N) A] (x : A) :
    Nat.card (Submodule.span (ZMod N) {x}) = addOrderOf x := by
  rw [← Nat.card_zmultiples x, ← span_singleton_toAddSubgroup (N := N) x]
  exact Nat.card_congr {
    toFun := fun value => ⟨value, value.property⟩
    invFun := fun value => ⟨value, value.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }

/-- Adding one generator multiplies cardinality by the order of its quotient coset. -/
theorem card_sup_span_singleton {N : Nat} {A : Type*} [AddCommGroup A]
    [Module (ZMod N) A] (submodule : Submodule (ZMod N) A) (x : A) :
    Nat.card ↥(submodule ⊔ Submodule.span (ZMod N) {x}) =
      Nat.card submodule * addOrderOf (submodule.mkQ x) := by
  let extended := submodule ⊔ Submodule.span (ZMod N) {x}
  have hsub : submodule ≤ extended := le_sup_left
  let inside : Submodule (ZMod N) extended := submodule.comap extended.subtype
  let quotientMap : extended →ₗ[ZMod N] A ⧸ submodule :=
    submodule.mkQ.domRestrict extended
  let insideEquiv : inside ≃ₗ[ZMod N] submodule := {
    toFun := fun value => ⟨value.1.1, value.2⟩
    invFun := fun value => ⟨⟨value.1, hsub value.2⟩, value.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }
  have hker : quotientMap.ker = inside := by
    dsimp only [quotientMap, inside]
    rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ]
  let quotientEquivRange : (extended ⧸ inside) ≃ₗ[ZMod N] quotientMap.range :=
    Submodule.quotEquivOfEq inside quotientMap.ker hker.symm ≪≫ₗ
      quotientMap.quotKerEquivRange
  have hquotientCard : Nat.card (extended ⧸ inside) = Nat.card quotientMap.range :=
    Nat.card_congr quotientEquivRange.toEquiv
  have hrange : quotientMap.range =
      Submodule.span (ZMod N) {submodule.mkQ x} := by
    dsimp only [quotientMap]
    rw [LinearMap.range_domRestrict]
    dsimp [extended]
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span]
    simp
  calc
    Nat.card ↥(submodule ⊔ Submodule.span (ZMod N) {x}) = Nat.card extended := rfl
    _ = Nat.card inside * Nat.card (extended ⧸ inside) :=
      Submodule.card_eq_card_quotient_mul_card inside
    _ = Nat.card submodule * addOrderOf (submodule.mkQ x) := by
      rw [Nat.card_congr insideEquiv.toEquiv, hquotientCard, hrange,
        card_span_singleton_zmod]

end CompositeModulusBasis.CyclicQuotient
