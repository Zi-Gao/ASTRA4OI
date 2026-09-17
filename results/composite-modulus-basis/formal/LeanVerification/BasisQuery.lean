import LeanVerification.DigitCardinality
import Mathlib.Tactic

/-!
# Correctness and totality of membership queries on a p-digit echelon basis

The cardinal-basis invariant maintained by insertion records normalized,
strictly ordered pivot slots, their generated submodule, and its cardinality.
It implies complete digit representations.  From this invariant we prove both
YES and NO branches and construct a finite query derivation for every target.  The construction clears an entire coordinate at
each successful step, yielding at most `d` reductions.
-/

namespace CompositeModulusBasis.BasisQuery

open DigitClosure PadicEchelon DigitCardinality

abbrev Basis (p k d : Nat) := CardinalBasis p k d

def Basis.submodule {p k d : Nat} (basis : Basis p k d) :
    Submodule (Ring p k) (Vector p k d) := basis.generated

theorem Basis.mem_iff_digitRep {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (x : Vector p k d) :
    x ∈ basis.submodule ↔ DigitRep p (rowsOf basis.pivots) x :=
  CardinalBasis.mem_iff_digitRep basis hp x

theorem Basis.eq_span {p k d : Nat} (basis : Basis p k d) :
    basis.submodule = Submodule.span (Ring p k) {row | row ∈ rowsOf basis.pivots} :=
  basis.generated_eq_span

theorem Basis.pivot_mem {p k d : Nat} (basis : Basis p k d)
    {pivot : PivotRow p k d} (hpivot : pivot ∈ basis.pivots) :
    pivot.row ∈ basis.submodule := by
  rw [basis.eq_span]
  apply Submodule.subset_span
  exact List.mem_map.mpr ⟨pivot, hpivot, rfl⟩

/-- A missing slot is a complete NO certificate, not merely a failed heuristic. -/
theorem Basis.not_mem_of_missing_lead {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    {x : Vector p k d} {slot : Slot d k} (hlead : HasLead x slot)
    (missing : ∀ pivot ∈ basis.pivots, pivot.slot ≠ slot) :
    x ∉ basis.submodule := by
  intro hx
  have hrep : DigitRep p (rowsOf basis.pivots) x := (basis.mem_iff_digitRep hp x).1 hx
  rcases nonzero_digitRep_hasLead basis.ordered hrep (hlead.vector_ne_zero hp) with
    ⟨pivot, hpivot, hpivotLead⟩
  exact missing pivot hpivot (hpivotLead.unique hp hlead)

/-- Two representatives of the same quotient coset whose leading slots are
absent from the basis must have the same leading slot.  Otherwise their
difference retains the earlier missing lead, contradicting membership in the
basis submodule. -/
theorem Basis.missing_coset_lead_unique {p k d : Nat}
    (basis : Basis p k d) (hp : 1 < p)
    {x y : Vector p k d} {xSlot ySlot : Slot d k}
    (xLead : HasLead x xSlot) (yLead : HasLead y ySlot)
    (xMissing : ∀ pivot ∈ basis.pivots, pivot.slot ≠ xSlot)
    (yMissing : ∀ pivot ∈ basis.pivots, pivot.slot ≠ ySlot)
    (sameCoset : x - y ∈ basis.submodule) :
    xSlot = ySlot := by
  rcases Slot.lt_or_eq_or_lt xSlot ySlot with hxy | heq | hyx
  · have hlead : HasLead (x - y) xSlot := xLead.sub_of_lt hp yLead hxy
    exact False.elim ((basis.not_mem_of_missing_lead hp hlead xMissing) sameCoset)
  · exact heq
  · have hreverse : y - x ∈ basis.submodule := by
      have hneg := basis.submodule.neg_mem sameCoset
      convert hneg using 1
      abel
    have hlead : HasLead (y - x) ySlot := yLead.sub_of_lt hp xLead hyx
    exact False.elim ((basis.not_mem_of_missing_lead hp hlead yMissing) hreverse)

/-- One legal pivot subtraction preserves membership in both directions. -/
theorem Basis.reduce_mem_iff {p k d : Nat} (basis : Basis p k d)
    {x : Vector p k d} {pivot : PivotRow p k d} (hpivot : pivot ∈ basis.pivots)
    (factor : Ring p k) :
    x - factor • pivot.row ∈ basis.submodule ↔ x ∈ basis.submodule := by
  exact basis.submodule.sub_mem_iff_left
    (basis.submodule.smul_mem factor (basis.pivot_mem hpivot))

/-- A proof-relevant execution of the query loop. -/
inductive Derivation {p k d : Nat} (basis : Basis p k d) :
    Vector p k d → Bool → Type where
  | zero {x : Vector p k d} (isZero : x = 0) : Derivation basis x true
  | missing {x : Vector p k d} {slot : Slot d k}
      (lead : HasLead x slot)
      (slotMissing : ∀ pivot ∈ basis.pivots, pivot.slot ≠ slot) :
      Derivation basis x false
  | reduce {x residual : Vector p k d} {answer : Bool}
      (pivot : PivotRow p k d) (pivotMem : pivot ∈ basis.pivots)
      (lead : HasLead x pivot.slot)
      (factor : Ring p k) (residualEq : residual = x - factor • pivot.row)
      (clearsThrough : ∀ column : Fin d, column ≤ pivot.slot.1 → residual column = 0)
      (tail : Derivation basis residual answer) : Derivation basis x answer

def Derivation.reductions {p k d : Nat} {basis : Basis p k d}
    {x : Vector p k d} {answer : Bool} : Derivation basis x answer → Nat
  | .zero _ => 0
  | .missing _ _ => 0
  | .reduce _ _ _ _ _ _ tail => tail.reductions + 1

def Derivation.finalResidual {p k d : Nat} {basis : Basis p k d}
    {x : Vector p k d} {answer : Bool} : Derivation basis x answer → Vector p k d
  | .zero _ => 0
  | .missing _ _ => x
  | .reduce _ _ _ _ _ _ tail => tail.finalResidual

theorem Derivation.final_zero_or_missing {p k d : Nat} {basis : Basis p k d}
    {x : Vector p k d} {answer : Bool} (derivation : Derivation basis x answer) :
    derivation.finalResidual = 0 ∨
      ∃ slot : Slot d k, HasLead derivation.finalResidual slot ∧
        ∀ pivot ∈ basis.pivots, pivot.slot ≠ slot := by
  induction derivation with
  | zero isZero => exact Or.inl rfl
  | missing lead slotMissing => exact Or.inr ⟨_, lead, slotMissing⟩
  | reduce pivot pivotMem lead factor residualEq clearsThrough tail ih => exact ih

/-- All reductions stay in the same coset of the represented submodule. -/
theorem Derivation.input_sub_final_mem {p k d : Nat} {basis : Basis p k d}
    {x : Vector p k d} {answer : Bool} (derivation : Derivation basis x answer) :
    x - derivation.finalResidual ∈ basis.submodule := by
  induction derivation with
  | zero isZero => simp [isZero, Derivation.finalResidual]
  | missing lead slotMissing => simp [Derivation.finalResidual]
  | @reduce x residual answer pivot pivotMem lead factor residualEq clearsThrough tail ih =>
      have hstep : x - residual ∈ basis.submodule := by
        rw [residualEq]
        simpa using basis.submodule.smul_mem factor (basis.pivot_mem pivotMem)
      have heq : x - tail.finalResidual =
          (x - residual) + (residual - tail.finalResidual) := by abel
      change x - tail.finalResidual ∈ basis.submodule
      rw [heq]
      exact basis.submodule.add_mem hstep ih

theorem Derivation.answer_true_iff_final_zero {p k d : Nat} {basis : Basis p k d}
    (hp : 1 < p) {x : Vector p k d} {answer : Bool}
    (derivation : Derivation basis x answer) :
    answer = true ↔ derivation.finalResidual = 0 := by
  induction derivation with
  | zero isZero => simp [Derivation.finalResidual]
  | missing lead slotMissing => simp [Derivation.finalResidual, lead.vector_ne_zero hp]
  | reduce pivot pivotMem lead factor residualEq clearsThrough tail ih => exact ih

/-- The final residual represents the same quotient coset as the input. -/
theorem Derivation.mkQ_final_eq_input {p k d : Nat} {basis : Basis p k d}
    {x : Vector p k d} {answer : Bool} (derivation : Derivation basis x answer) :
    basis.submodule.mkQ derivation.finalResidual = basis.submodule.mkQ x := by
  rw [← sub_eq_zero]
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero basis.submodule).2
  have hneg := basis.submodule.neg_mem derivation.input_sub_final_mem
  convert hneg using 1
  abel

/-- Zeros in a processed prefix remain zero in the final residual. -/
theorem Derivation.final_zero_through {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    {x : Vector p k d} {answer : Bool} (derivation : Derivation basis x answer)
    (base : Fin d) (hzero : ∀ column : Fin d, column ≤ base → x column = 0) :
    ∀ column : Fin d, column ≤ base → derivation.finalResidual column = 0 := by
  induction derivation with
  | zero isZero => simp [Derivation.finalResidual]
  | missing lead slotMissing => exact hzero
  | @reduce x residual answer pivot pivotMem lead factor residualEq clearsThrough tail ih =>
      have hbaseLt : base < pivot.slot.1 := by
        by_contra hnot
        have hpivotLe : pivot.slot.1 ≤ base := le_of_not_gt hnot
        exact lead.exactAt.ne_zero hp pivot.slot.2.isLt (hzero pivot.slot.1 hpivotLe)
      have hresidualZero : ∀ column : Fin d, column ≤ base → residual column = 0 := by
        intro column hcolumn
        have hcolumnLt : column < pivot.slot.1 := lt_of_le_of_lt hcolumn hbaseLt
        rw [residualEq]
        change x column - factor * pivot.row column = 0
        rw [hzero column hcolumn, pivot.zerosBefore column hcolumnLt]
        simp
      exact ih hresidualZero

/-- A query either leaves its original missing lead or clears that entire coordinate. -/
theorem Derivation.final_lead_eq_or_later_column {p k d : Nat}
    (basis : Basis p k d) (hp : 1 < p)
    {x : Vector p k d} {answer : Bool} (derivation : Derivation basis x answer)
    {slot : Slot d k} (inputLead : HasLead x slot) :
    derivation.finalResidual = 0 ∨
      ∃ finalSlot : Slot d k, HasLead derivation.finalResidual finalSlot ∧
        (finalSlot = slot ∨ slot.1 < finalSlot.1) := by
  cases derivation with
  | zero isZero => exact Or.inl rfl
  | missing lead slotMissing =>
      exact Or.inr ⟨slot, inputLead, Or.inl rfl⟩
  | @reduce x residual answer pivot pivotMem lead factor residualEq clearsThrough tail =>
      have hpivotSlot : pivot.slot = slot := lead.unique hp inputLead
      rcases tail.final_zero_or_missing with hzero | ⟨finalSlot, finalLead, finalMissing⟩
      · exact Or.inl hzero
      · right
        refine ⟨finalSlot, finalLead, Or.inr ?_⟩
        have hfinalZero := tail.final_zero_through basis hp pivot.slot.1 clearsThrough
          finalSlot.1
        have hpivotLt : pivot.slot.1 < finalSlot.1 := by
          by_contra hnot
          have hle : finalSlot.1 ≤ pivot.slot.1 := le_of_not_gt hnot
          exact finalLead.exactAt.ne_zero hp finalSlot.2.isLt (hfinalZero hle)
        simpa [hpivotSlot] using hpivotLt

/-- Multiplication by `p` either raises the p-level or clears the whole leading coordinate. -/
theorem p_nsmul_lead_or_zero_through {p k d : Nat}
    {x : Vector p k d} {slot : Slot d k} (hlead : HasLead x slot) :
    (∃ nextSlot : Slot d k, Slot.lt slot nextSlot ∧ HasLead (p • x) nextSlot) ∨
      (∀ column : Fin d, column ≤ slot.1 → (p • x) column = 0) := by
  by_cases hnext : (slot.2 : Nat) + 1 < k
  · let nextLevel : Fin k := ⟨(slot.2 : Nat) + 1, hnext⟩
    let nextSlot : Slot d k := (slot.1, nextLevel)
    left
    refine ⟨nextSlot, ?_, ?_⟩
    · refine Or.inr ⟨rfl, ?_⟩
      exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self _)
    · constructor
      · intro column hcolumn
        change p • x column = 0
        rw [hlead.zerosBefore column hcolumn]
        simp
      · rcases hlead.exactAt with ⟨digit, hdigitPos, hdigitLt, tail, hx⟩
        refine ⟨digit, hdigitPos, hdigitLt, tail, ?_⟩
        change p • x slot.1 = _
        rw [hx]
        push_cast
        rw [pow_succ]
        ring
  · right
    have hlast : (slot.2 : Nat) + 1 = k := by omega
    intro column hcolumn
    rcases hcolumn.eq_or_lt with rfl | hlt
    · rcases hlead.exactAt with ⟨digit, hdigitPos, hdigitLt, tail, hx⟩
      change p • x slot.1 = 0
      rw [hx]
      rw [← Nat.cast_smul_eq_nsmul (Ring p k)]
      rw [smul_eq_mul]
      push_cast
      have hpow : (p : Ring p k) * (p : Ring p k) ^ (slot.2 : Nat) =
          ((p ^ ((slot.2 : Nat) + 1) : Nat) : Ring p k) := by
        push_cast
        rw [pow_succ]
        ring
      rw [← mul_assoc, hpow, hlast]
      simp
    · change p • x column = 0
      rw [hlead.zerosBefore column hlt]
      simp

/-- Normalizing the next p-power coset can only move to a strictly later slot. -/
theorem Derivation.p_nsmul_final_strictly_later {p k d : Nat}
    (basis : Basis p k d) (hp : 1 < p)
    {x : Vector p k d} {slot : Slot d k} (hlead : HasLead x slot)
    {answer : Bool} (derivation : Derivation basis (p • x) answer) :
    derivation.finalResidual = 0 ∨
      ∃ finalSlot : Slot d k,
        HasLead derivation.finalResidual finalSlot ∧ Slot.lt slot finalSlot := by
  rcases p_nsmul_lead_or_zero_through hlead with
    ⟨nextSlot, hslotNext, hnextLead⟩ | hzeroThrough
  · rcases derivation.final_lead_eq_or_later_column basis hp hnextLead with
      hzero | ⟨finalSlot, hfinalLead, hposition⟩
    · exact Or.inl hzero
    · right
      refine ⟨finalSlot, hfinalLead, ?_⟩
      rcases hposition with rfl | hcolumn
      · exact hslotNext
      · exact Slot.lt_trans hslotNext (Or.inl hcolumn)
  · rcases derivation.final_zero_or_missing with hzero | ⟨finalSlot, hfinalLead, hmissing⟩
    · exact Or.inl hzero
    · right
      refine ⟨finalSlot, hfinalLead, Or.inl ?_⟩
      by_contra hnot
      have hle : finalSlot.1 ≤ slot.1 := le_of_not_gt hnot
      have hfinalZero := derivation.final_zero_through basis hp slot.1 hzeroThrough
        finalSlot.1 hle
      exact hfinalLead.exactAt.ne_zero hp finalSlot.2.isLt hfinalZero

/-- Every proof-relevant execution returns YES exactly for submodule members. -/
theorem Derivation.correct {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    {x : Vector p k d} {answer : Bool} (derivation : Derivation basis x answer) :
    answer = true ↔ x ∈ basis.submodule := by
  induction derivation with
  | zero isZero => simp [isZero]
  | missing lead slotMissing =>
      have hnot := basis.not_mem_of_missing_lead hp lead slotMissing
      simp [hnot]
  | @reduce x residual answer pivot pivotMem lead factor residualEq clearsThrough tail ih =>
      rw [ih, residualEq, basis.reduce_mem_iff pivotMem factor]

theorem Derivation.final_zero_iff_mem {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    {x : Vector p k d} {answer : Bool} (derivation : Derivation basis x answer) :
    derivation.finalResidual = 0 ↔ x ∈ basis.submodule := by
  rw [← derivation.answer_true_iff_final_zero hp]
  exact derivation.correct basis hp

/-- The coordinate-clearing factor exposed by `ExactAt`. -/
theorem clear_pivot_coordinate {p k d : Nat}
    (pivot : PivotRow p k d) {x : Vector p k d}
    (hlead : HasLead x pivot.slot) :
    ∃ factor : Ring p k,
      (x - factor • pivot.row) pivot.slot.1 = 0 := by
  rcases hlead.exactAt with ⟨digit, hdigitPos, hdigitLt, tail, hx⟩
  refine ⟨(digit + p * tail : Nat), ?_⟩
  change x pivot.slot.1 - ((digit + p * tail : Nat) : Ring p k) *
    pivot.row pivot.slot.1 = 0
  rw [hx, pivot.pivot]
  push_cast
  ring

/-- Clearing a pivot also preserves all zeros before that pivot column. -/
theorem zero_through_pivot {p k d : Nat}
    (pivot : PivotRow p k d) {x : Vector p k d}
    (hlead : HasLead x pivot.slot) :
    ∃ factor : Ring p k, ∀ column : Fin d, column ≤ pivot.slot.1 →
      (x - factor • pivot.row) column = 0 := by
  rcases hlead.exactAt with ⟨digit, hdigitPos, hdigitLt, tail, hx⟩
  refine ⟨(digit + p * tail : Nat), ?_⟩
  intro column hcolumn
  rcases hcolumn.eq_or_lt with rfl | hlt
  · change x pivot.slot.1 - ((digit + p * tail : Nat) : Ring p k) *
      pivot.row pivot.slot.1 = 0
    rw [hx, pivot.pivot]
    push_cast
    ring
  · change x column - ((digit + p * tail : Nat) : Ring p k) * pivot.row column = 0
    rw [hlead.zerosBefore column hlt, pivot.zerosBefore column hlt]
    simp

/-- Strong induction on the number of columns still available to the query. -/
private theorem derivation_exists_from {p k d : Nat} (basis : Basis p k d) (hp : 1 < p) :
    ∀ budget start : Nat, ∀ x : Vector p k d,
      d - start = budget →
      (∀ column : Fin d, (column : Nat) < start → x column = 0) →
      ∃ answer : Bool, ∃ derivation : Derivation basis x answer,
        derivation.reductions ≤ budget := by
  classical
  intro budget
  induction budget using Nat.strong_induction_on with
  | h budget ih =>
      intro start x hbudget hbefore
      by_cases hxzero : x = 0
      · exact ⟨true, .zero hxzero, by simp [Derivation.reductions]⟩
      · rcases exists_hasLead hp hxzero with ⟨slot, hlead⟩
        have hstart : start ≤ (slot.1 : Nat) := by
          by_contra hnot
          have hlt : (slot.1 : Nat) < start := Nat.lt_of_not_ge hnot
          exact hlead.exactAt.ne_zero hp slot.2.isLt (hbefore slot.1 hlt)
        by_cases hpivot : ∃ pivot ∈ basis.pivots, pivot.slot = slot
        · rcases hpivot with ⟨pivot, hpivotMem, hpivotSlot⟩
          subst slot
          rcases zero_through_pivot pivot hlead with ⟨factor, hzeroThrough⟩
          let residual := x - factor • pivot.row
          let nextStart := (pivot.slot.1 : Nat) + 1
          let nextBudget := d - nextStart
          have hbudgetLt : nextBudget < budget := by
            have hpivotLt : (pivot.slot.1 : Nat) < d := pivot.slot.1.isLt
            dsimp [nextBudget, nextStart]
            omega
          have hresidualBefore : ∀ column : Fin d,
              (column : Nat) < nextStart → residual column = 0 := by
            intro column hcolumn
            apply hzeroThrough column
            dsimp [nextStart] at hcolumn
            omega
          rcases ih nextBudget hbudgetLt nextStart residual rfl hresidualBefore with
            ⟨answer, tail, htailCount⟩
          refine ⟨answer, .reduce pivot hpivotMem hlead factor rfl hzeroThrough tail, ?_⟩
          simp only [Derivation.reductions]
          dsimp [nextBudget, nextStart] at htailCount
          omega
        · refine ⟨false, .missing hlead ?_, ?_⟩
          · intro pivot hpivotMem hpivotSlot
            exact hpivot ⟨pivot, hpivotMem, hpivotSlot⟩
          · exact Nat.zero_le _

/-- Every target has a finite query derivation. -/
theorem derivation_exists {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (x : Vector p k d) : ∃ answer : Bool, ∃ derivation : Derivation basis x answer,
      derivation.reductions ≤ d := by
  apply derivation_exists_from basis hp d 0 x rfl
  simp

/-- Total, correct membership decision for every p-digit echelon basis. -/
theorem exists_correct_answer {p k d : Nat} (basis : Basis p k d) (hp : 1 < p)
    (x : Vector p k d) :
    ∃ answer : Bool, ∃ derivation : Derivation basis x answer,
      (answer = true ↔ x ∈ basis.submodule) ∧
      derivation.reductions ≤ d := by
  rcases derivation_exists basis hp x with ⟨answer, derivation, hcount⟩
  exact ⟨answer, derivation, derivation.correct basis hp, hcount⟩

end CompositeModulusBasis.BasisQuery
