import LeanVerification.CRT
import LeanVerification.PrefixAlgorithm
import Mathlib.Tactic

/-!
# Combining all prime-power components

The algebraic theorem combines independently obtained component answers by
CRT.  The arithmetic theorems sum the exact prime-power counters and expose
the bounds in terms of `K = ∑ kᵢ` and the number of components.

Factorization itself is deliberately an input certificate here.  Its running
time is therefore not hidden inside the linear-basis bounds.
-/

namespace CompositeModulusBasis.CompositeAlgorithm

open scoped BigOperators
open CRT PadicEchelon PrefixAlgorithm TimestampedBasis TimestampLayerInvariant

abbrev FullModulus {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat) : Nat :=
  ∏ component, primes component ^ exponents component

/-- Distinct prime bases automatically give the pairwise-coprime
prime-power certificate required by CRT. -/
theorem primePowers_pairwise_coprime {ι : Type*}
    (primes exponents : ι → Nat)
    (hprime : ∀ component, (primes component).Prime)
    (hdistinct : Function.Injective primes) :
    Pairwise (Function.onFun Nat.Coprime fun component =>
      primes component ^ exponents component) := by
  intro left right hne
  exact Nat.coprime_pow_primes (exponents left) (exponents right)
    (hprime left) (hprime right) (hdistinct.ne hne)

structure CompositeSourceVector {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat) (d : Nat) where
  timestamp : Nat
  row : Fin d → ZMod (FullModulus primes exponents)

def CompositeSourceStrict {ι : Type*} [Fintype ι]
    {primes exponents : ι → Nat} {d : Nat}
    (source : List (CompositeSourceVector primes exponents d)) : Prop :=
  source.Pairwise fun earlier later => earlier.timestamp < later.timestamp

noncomputable def componentEquiv {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component)) :
    ZMod (FullModulus primes exponents) ≃+*
      (∀ component, ZMod (primes component ^ exponents component)) :=
  ZMod.prodEquivPi (fun component => primes component ^ exponents component) coprime

noncomputable def componentSource {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component))
    {d : Nat} (component : ι)
    (source : List (CompositeSourceVector primes exponents d)) :
    List (SourceVector (primes component) (exponents component) d) :=
  source.map fun item =>
    { timestamp := item.timestamp
      row := componentVector (componentEquiv primes exponents coprime) component item.row }

theorem componentSource_strict {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component))
    {d : Nat} {source : List (CompositeSourceVector primes exponents d)}
    (hstrict : CompositeSourceStrict source) (component : ι) :
    SourceStrict (componentSource primes exponents coprime component source) := by
  rw [CompositeSourceStrict] at hstrict
  rw [SourceStrict, componentSource]
  induction source with
  | nil => simp
  | cons head tail ih =>
      rw [List.map_cons, List.pairwise_cons]
      rw [List.pairwise_cons] at hstrict
      constructor
      · intro later hlater
        rcases List.mem_map.mp hlater with ⟨item, hitem, rfl⟩
        exact hstrict.1 item hitem
      · exact ih hstrict.2

def fullRowsAt {ι : Type*} [Fintype ι]
    {primes exponents : ι → Nat} {d : Nat}
    (source : List (CompositeSourceVector primes exponents d)) (left : Nat) :
    List (Fin d → ZMod (FullModulus primes exponents)) :=
  (source.filter fun item => left ≤ item.timestamp).map CompositeSourceVector.row

def compositeSubmodule {ι : Type*} [Fintype ι]
    {primes exponents : ι → Nat} {d : Nat}
    (source : List (CompositeSourceVector primes exponents d)) (left : Nat) :
    Submodule (ZMod (FullModulus primes exponents))
      (Fin d → ZMod (FullModulus primes exponents)) :=
  Submodule.span _ {row | row ∈ fullRowsAt source left}

theorem component_sourceSubmodule_eq {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component))
    {d : Nat} (component : ι)
    (source : List (CompositeSourceVector primes exponents d)) (left : Nat) :
    sourceSubmodule (componentSource primes exponents coprime component source) left =
      Submodule.span (ZMod (primes component ^ exponents component))
        {row | row ∈ (fullRowsAt source left).map
          (componentVector (componentEquiv primes exponents coprime) component)} := by
  unfold sourceSubmodule
  congr 1
  ext row
  simp [sourceSet, componentSource, fullRowsAt, eq_comm, and_assoc,
    and_left_comm, and_comm]

/-- CRT specialized to timestamp-filtered source rows. -/
theorem composite_mem_iff_components {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component))
    {d : Nat} (source : List (CompositeSourceVector primes exponents d))
    (left : Nat) (target : Fin d → ZMod (FullModulus primes exponents)) :
    target ∈ compositeSubmodule source left ↔
      ∀ component : ι,
        componentVector (componentEquiv primes exponents coprime) component target ∈
          sourceSubmodule
            (componentSource primes exponents coprime component source) left := by
  rw [compositeSubmodule,
    mem_span_list_iff_components (componentEquiv primes exponents coprime)
      (fullRowsAt source left) target]
  apply forall_congr'
  intro component
  rw [component_sourceSubmodule_eq primes exponents coprime component source left]

noncomputable def componentBuild {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat) (hprime : ∀ component, (primes component).Prime)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component))
    {d : Nat} (source : List (CompositeSourceVector primes exponents d))
    (hstrict : CompositeSourceStrict source) (component : ι) :
    BuildResult (hprime component)
      (componentSource primes exponents coprime component source) :=
  build (hprime component) _
    (componentSource_strict primes exponents coprime hstrict component)

/-- Fully combined interval-query theorem.  It constructs every component
table, obtains a terminating query derivation in each one, and proves that
conjunction of the answers is equivalent to membership over the original
composite modulus. -/
theorem composite_query_complete {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat) (hprime : ∀ component, (primes component).Prime)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component))
    {d : Nat} (source : List (CompositeSourceVector primes exponents d))
    (hstrict : CompositeSourceStrict source) (left : Nat)
    (target : Fin d → ZMod (FullModulus primes exponents)) :
    ∃ answers : ι → Bool,
      ((∀ component, answers component = true) ↔
        target ∈ compositeSubmodule source left) ∧
      ∀ component : ι,
        ∃ derivation : BasisQuery.Derivation
          (basisAt (componentBuild primes exponents hprime coprime source hstrict component).correct
            left)
          (componentVector (componentEquiv primes exponents coprime) component target)
          (answers component),
          derivation.reductions ≤ d ∧ derivation.reductions * d ≤ d * d := by
  have hquery : ∀ component : ι,
      ∃ answer : Bool,
        ∃ derivation : BasisQuery.Derivation
          (basisAt (componentBuild primes exponents hprime coprime source hstrict component).correct
            left)
          (componentVector (componentEquiv primes exponents coprime) component target)
          answer,
          (answer = true ↔
            componentVector (componentEquiv primes exponents coprime) component target ∈
              sourceSubmodule
                (componentSource primes exponents coprime component source) left) ∧
          derivation.reductions ≤ d ∧ derivation.reductions * d ≤ d * d := by
    intro component
    exact (componentBuild primes exponents hprime coprime source hstrict component).query_complete
      left (componentVector (componentEquiv primes exponents coprime) component target)
  choose answers derivations hspec using hquery
  refine ⟨answers, ?_, ?_⟩
  · constructor
    · intro hall
      apply (composite_mem_iff_components primes exponents coprime source left target).2
      intro component
      exact (hspec component).1.1 (hall component)
    · intro hmember component
      exact (hspec component).1.2
        ((composite_mem_iff_components primes exponents coprime source left target).1
          hmember component)
  · intro component
    exact ⟨derivations component, (hspec component).2⟩

/-- If every component query is correct, conjunction of its Boolean answers
is correct over the original composite modulus.  Component coefficient
vectors may be unrelated; `zmod_span_iff_coprime_components` performs the CRT
combination separately at each generator index. -/
theorem component_answers_iff {ι : Type*} [Fintype ι]
    (moduli : ι → Nat)
    (coprime : Pairwise (Function.onFun Nat.Coprime moduli))
    {n d : Nat}
    (generators : Fin n → Fin d → ZMod (∏ i, moduli i))
    (target : Fin d → ZMod (∏ i, moduli i))
    (answers : ι → Bool)
    (hanswers : ∀ component : ι,
      answers component = true ↔
        componentVector (ZMod.prodEquivPi moduli coprime) component target ∈
          Submodule.span (ZMod (moduli component))
            (Set.range fun index =>
              componentVector (ZMod.prodEquivPi moduli coprime) component
                (generators index))) :
    (∀ component, answers component = true) ↔
      target ∈ Submodule.span (ZMod (∏ i, moduli i)) (Set.range generators) := by
  rw [zmod_span_iff_coprime_components moduli coprime generators target]
  constructor
  · intro hall component
    exact (hanswers component).1 (hall component)
  · intro hall component
    exact (hanswers component).2 (hall component)

/-- Summing the prime-power preprocessing counters gives `n K d²`, where
`K = ∑ kᵢ`. -/
theorem preprocessing_cellOps_le {ι : Type*} [Fintype ι]
    (n d : Nat) (exponent cellOps : ι → Nat)
    (hcomponent : ∀ component,
      cellOps component ≤ 2 * n * exponent component * d * d) :
    (∑ component, cellOps component) ≤
      2 * n * (∑ component, exponent component) * d * d := by
  calc
    (∑ component, cellOps component) ≤
        ∑ component, 2 * n * exponent component * d * d :=
      Finset.sum_le_sum fun component _ => hcomponent component
    _ = ∑ component, (2 * n * d * d) * exponent component := by
      apply Finset.sum_congr rfl
      intro component _
      ring
    _ = (2 * n * d * d) * ∑ component, exponent component := by
      rw [Finset.mul_sum]
    _ = 2 * n * (∑ component, exponent component) * d * d := by ring

/-- Generic summation lemma for valuations, inversions, writes, or heap pops. -/
theorem preprocessing_events_le {ι : Type*} [Fintype ι]
    (n perExponent : Nat) (exponent events : ι → Nat)
    (hcomponent : ∀ component,
      events component ≤ n * exponent component * perExponent) :
    (∑ component, events component) ≤
      n * (∑ component, exponent component) * perExponent := by
  calc
    (∑ component, events component) ≤
        ∑ component, n * exponent component * perExponent :=
      Finset.sum_le_sum fun component _ => hcomponent component
    _ = ∑ component, (n * perExponent) * exponent component := by
      apply Finset.sum_congr rfl
      intro component _
      ring
    _ = (n * perExponent) * ∑ component, exponent component := by
      rw [Finset.mul_sum]
    _ = n * (∑ component, exponent component) * perExponent := by ring

/-- Total preprocessing work of the actually constructed component tables. -/
theorem componentBuilds_cellOps_le {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat) (hprime : ∀ component, (primes component).Prime)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component))
    {d : Nat} (source : List (CompositeSourceVector primes exponents d))
    (hstrict : CompositeSourceStrict source) :
    (∑ component,
      (componentBuild primes exponents hprime coprime source hstrict component).vectorPasses * d) ≤
      2 * source.length * (∑ component, exponents component) * d * d := by
  apply preprocessing_cellOps_le source.length d exponents
  intro component
  simpa [componentSource, Nat.mul_assoc] using
    (componentBuild primes exponents hprime coprime source hstrict component).cellOps_le

theorem componentBuilds_valuations_le {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat) (hprime : ∀ component, (primes component).Prime)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component))
    {d : Nat} (source : List (CompositeSourceVector primes exponents d))
    (hstrict : CompositeSourceStrict source) :
    (∑ component,
      (componentBuild primes exponents hprime coprime source hstrict component).valuations) ≤
      source.length * (∑ component, exponents component) * d := by
  apply preprocessing_events_le source.length d exponents
  intro component
  simpa [componentSource, Nat.mul_assoc] using
    (componentBuild primes exponents hprime coprime source hstrict component).valuations_le

theorem componentBuilds_normalizations_le {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat) (hprime : ∀ component, (primes component).Prime)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component))
    {d : Nat} (source : List (CompositeSourceVector primes exponents d))
    (hstrict : CompositeSourceStrict source) :
    (∑ component,
      (componentBuild primes exponents hprime coprime source hstrict component).normalizations) ≤
      source.length * (∑ component, exponents component) * d := by
  apply preprocessing_events_le source.length d exponents
  intro component
  simpa [componentSource, Nat.mul_assoc] using
    (componentBuild primes exponents hprime coprime source hstrict component).normalizations_le

/-- Total core coordinate updates, including initial power-row generation,
across all prime-power components.  Factorization and scalar subroutines
remain separate from this count. -/
theorem componentBuilds_core_cellOps_le {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat) (hprime : ∀ component, (primes component).Prime)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component))
    {d : Nat} (source : List (CompositeSourceVector primes exponents d))
    (hstrict : CompositeSourceStrict source) (hd : 0 < d) :
    (∑ component, (source.length * exponents component * d +
      (componentBuild primes exponents hprime coprime source hstrict component).vectorPasses * d)) ≤
      3 * source.length * (∑ component, exponents component) * d * d := by
  calc
    _ ≤ ∑ component, 3 * source.length * exponents component * d * d := by
      apply Finset.sum_le_sum
      intro component _
      simpa [componentSource] using
        (componentBuild primes exponents hprime coprime source hstrict component).core_cellOps_le hd
    _ = 3 * source.length * (∑ component, exponents component) * d * d := by
      simp only [Finset.sum_mul, Finset.mul_sum]

/-- Across `w` components, a query performs at most `w d²` coordinate
operations. -/
theorem query_cellOps_le {ι : Type*} [Fintype ι]
    (d : Nat) (reductions : ι → Nat)
    (hcomponent : ∀ component, reductions component ≤ d) :
    (∑ component, reductions component * d) ≤
      Fintype.card ι * d * d := by
  calc
    (∑ component, reductions component * d) ≤ ∑ _component : ι, d * d :=
      Finset.sum_le_sum fun component _ => Nat.mul_le_mul_right d (hcomponent component)
    _ = Fintype.card ι * d * d := by simp [Nat.mul_assoc]

/-- The combined query theorem with its summed `w d²` operation bound. -/
theorem composite_query_cost {ι : Type*} [Fintype ι]
    (primes exponents : ι → Nat) (hprime : ∀ component, (primes component).Prime)
    (coprime : Pairwise
      (Function.onFun Nat.Coprime fun component =>
        primes component ^ exponents component))
    {d : Nat} (source : List (CompositeSourceVector primes exponents d))
    (hstrict : CompositeSourceStrict source) (left : Nat)
    (target : Fin d → ZMod (FullModulus primes exponents)) :
    ∃ answers : ι → Bool, ∃ reductions : ι → Nat,
      ((∀ component, answers component = true) ↔
        target ∈ compositeSubmodule source left) ∧
      (∀ component, reductions component ≤ d) ∧
      (∑ component, reductions component * d) ≤ Fintype.card ι * d * d := by
  rcases composite_query_complete primes exponents hprime coprime source hstrict left target with
    ⟨answers, hcorrect, hderivations⟩
  choose derivations hderivationsSpec using hderivations
  let reductions : ι → Nat := fun component => (derivations component).reductions
  have hreductions : ∀ component, reductions component ≤ d := by
    intro component
    exact (hderivationsSpec component).1
  exact ⟨answers, reductions, hcorrect, hreductions,
    query_cellOps_le d reductions hreductions⟩

/-- The fixed current table contains at most `d K` slots across all
prime-power components. -/
theorem current_table_slots_le {ι : Type*} [Fintype ι]
    (d : Nat) (exponent entries : ι → Nat)
    (hcomponent : ∀ component, entries component ≤ d * exponent component) :
    (∑ component, entries component) ≤ d * ∑ component, exponent component := by
  calc
    (∑ component, entries component) ≤ ∑ component, d * exponent component :=
      Finset.sum_le_sum fun component _ => hcomponent component
    _ = d * ∑ component, exponent component := by rw [Finset.mul_sum]

/-- Copying all fixed-size slot arrays for all `n` prefixes uses exactly
`n d K` references. -/
theorem snapshot_reference_count (n d totalExponent : Nat) :
    n * (d * totalExponent) = n * d * totalExponent := by ring

/-- At most `n K d` materialized rows of length `d` use `n K d²` coordinate
cells. -/
theorem persistent_row_cell_count (n d totalExponent : Nat) :
    n * (totalExponent * d) * d = n * totalExponent * d * d := by ring

end CompositeModulusBasis.CompositeAlgorithm
