import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic

/-!
# Componentwise span membership under the Chinese remainder theorem

The reverse implication is the subtle one: every prime-power component may
use different coefficients.  CRT is applied independently at each generator
index to combine those coefficient families into coefficients modulo the full
modulus.
-/

namespace CompositeModulusBasis.CRT

open scoped BigOperators

noncomputable def linearCombination {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : Nat}
    (generators : Fin n → M) (coefficients : Fin n → R) : M :=
  ∑ index, coefficients index • generators index

theorem mem_span_range_iff_coefficients {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : Nat}
    (generators : Fin n → M) (x : M) :
    x ∈ Submodule.span R (Set.range generators) ↔
      ∃ coefficients : Fin n → R,
        x = linearCombination generators coefficients := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem value hvalue =>
        rcases hvalue with ⟨index, rfl⟩
        let coefficients : Fin n → R := fun other => if other = index then 1 else 0
        refine ⟨coefficients, ?_⟩
        simp [linearCombination, coefficients]
    | zero =>
        refine ⟨0, ?_⟩
        simp [linearCombination]
    | add x y hx hy ihx ihy =>
        rcases ihx with ⟨left, rfl⟩
        rcases ihy with ⟨right, rfl⟩
        refine ⟨left + right, ?_⟩
        simp [linearCombination, add_smul, Finset.sum_add_distrib]
    | smul scalar x hx ih =>
        rcases ih with ⟨coefficients, rfl⟩
        refine ⟨scalar • coefficients, ?_⟩
        simp [linearCombination, Finset.smul_sum, smul_smul]
  · rintro ⟨coefficients, rfl⟩
    apply Submodule.sum_mem
    intro index hindex
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self index))

variable {ι : Type*}
variable {R : Type*} [CommRing R]
variable {S : ι → Type*} [∀ i, CommRing (S i)]

def componentVector {d : Nat} (equiv : R ≃+* (∀ i, S i))
    (component : ι) (x : Fin d → R) : Fin d → S component :=
  fun coordinate => equiv (x coordinate) component

theorem component_linearCombination {n d : Nat}
    (equiv : R ≃+* (∀ i, S i)) (component : ι)
    (generators : Fin n → Fin d → R) (coefficients : Fin n → R) :
    componentVector equiv component (linearCombination generators coefficients) =
      linearCombination (fun index => componentVector equiv component (generators index))
        (fun index => equiv (coefficients index) component) := by
  ext coordinate
  simp [componentVector, linearCombination, map_sum, map_mul]

/-- Span membership over a finite product ring is exactly componentwise span
membership, with no requirement that the initially chosen component
coefficients agree. -/
theorem mem_span_iff_components {n d : Nat}
    (equiv : R ≃+* (∀ i, S i))
    (generators : Fin n → Fin d → R) (x : Fin d → R) :
    x ∈ Submodule.span R (Set.range generators) ↔
      ∀ component : ι,
        componentVector equiv component x ∈
          Submodule.span (S component)
            (Set.range fun index => componentVector equiv component (generators index)) := by
  classical
  constructor
  · intro hx component
    rcases (mem_span_range_iff_coefficients generators x).1 hx with
      ⟨coefficients, rfl⟩
    rw [component_linearCombination]
    exact (mem_span_range_iff_coefficients _ _).2 ⟨_, rfl⟩
  · intro hcomponents
    have hcoefficients : ∀ component : ι,
        ∃ coefficients : Fin n → S component,
          componentVector equiv component x =
            linearCombination
              (fun index => componentVector equiv component (generators index))
              coefficients := by
      intro component
      exact (mem_span_range_iff_coefficients _ _).1 (hcomponents component)
    choose coefficients hcoefficientsEq using hcoefficients
    let combined : Fin n → R := fun index =>
      equiv.symm (fun component => coefficients component index)
    apply (mem_span_range_iff_coefficients generators x).2
    refine ⟨combined, ?_⟩
    ext coordinate
    apply equiv.injective
    funext component
    have hcomponent := congrFun (hcoefficientsEq component) coordinate
    have hcombined := congrFun
      (component_linearCombination equiv component generators combined) coordinate
    change equiv (x coordinate) component = _ at hcomponent
    change equiv (linearCombination generators combined coordinate) component = _ at hcombined
    rw [hcomponent, hcombined]
    simp [linearCombination, combined]

/-- List-generator form used by timestamp-filtered source prefixes. -/
theorem mem_span_list_iff_components {d : Nat}
    (equiv : R ≃+* (∀ i, S i))
    (generators : List (Fin d → R)) (x : Fin d → R) :
    x ∈ Submodule.span R {row | row ∈ generators} ↔
      ∀ component : ι,
        componentVector equiv component x ∈
          Submodule.span (S component)
            {row | row ∈ generators.map (componentVector equiv component)} := by
  let indexed : Fin generators.length → Fin d → R := fun index => generators.get index
  have hfull : Set.range indexed = {row | row ∈ generators} := by
    ext row
    change (∃ index, indexed index = row) ↔ row ∈ generators
    simpa [indexed] using (List.mem_iff_get (a := row) (l := generators)).symm
  have hcomponent : ∀ component : ι,
      Set.range (fun index => componentVector equiv component (indexed index)) =
        {row | row ∈ generators.map (componentVector equiv component)} := by
    intro component
    ext row
    simp only [Set.mem_range, Set.mem_setOf_eq, List.mem_map]
    change (∃ index,
        componentVector equiv component (indexed index) = row) ↔
      ∃ value ∈ generators, componentVector equiv component value = row
    constructor
    · rintro ⟨index, rfl⟩
      exact ⟨generators.get index, generators.get_mem index, rfl⟩
    · rintro ⟨value, hvalue, hrow⟩
      rcases List.get_of_mem hvalue with ⟨index, hindex⟩
      refine ⟨index, ?_⟩
      change componentVector equiv component (generators.get index) = row
      rw [hindex, hrow]
  rw [← hfull, mem_span_iff_components equiv indexed x]
  apply forall_congr'
  intro component
  rw [hcomponent component]

/-- General finite Chinese-remainder specialization for pairwise coprime
moduli. -/
theorem zmod_span_iff_coprime_components {ι : Type*} [Fintype ι]
    (moduli : ι → Nat)
    (coprime : Pairwise (Function.onFun Nat.Coprime moduli))
    {n d : Nat}
    (generators : Fin n → Fin d → ZMod (∏ i, moduli i))
    (x : Fin d → ZMod (∏ i, moduli i)) :
    x ∈ Submodule.span (ZMod (∏ i, moduli i)) (Set.range generators) ↔
      ∀ component : ι,
        componentVector (ZMod.prodEquivPi moduli coprime) component x ∈
          Submodule.span (ZMod (moduli component))
            (Set.range fun index =>
              componentVector (ZMod.prodEquivPi moduli coprime) component
                (generators index)) :=
  mem_span_iff_components (ZMod.prodEquivPi moduli coprime) generators x

end CompositeModulusBasis.CRT
