import LeanVerification.CyclicExtension
import Mathlib.Tactic

/-!
# Timestamp-filtered p-adic tables

This module formalizes the semantic view shared by the priority queue and the
stored table.  Every active row has a conservative timestamp.  The key local
lemmas prove that reduction by a newer row and replacement of an older row
preserve the span seen at *every* left endpoint simultaneously.
-/

namespace CompositeModulusBasis.TimestampedBasis

open BasisQuery CyclicExtension DigitCardinality PadicEchelon

structure TaggedVector (p k d : Nat) where
  timestamp : Nat
  layer : Nat
  row : Vector p k d

def TaggedVector.withRow {p k d : Nat} (entry : TaggedVector p k d)
    (row : Vector p k d) : TaggedVector p k d :=
  { entry with row := row }

def activeSet {p k d : Nat} (entries : List (TaggedVector p k d))
    (left : Nat) : Set (Vector p k d) :=
  {row | ∃ entry ∈ entries, left ≤ entry.timestamp ∧ row = entry.row}

def activeSpan {p k d : Nat} (entries : List (TaggedVector p k d))
    (left : Nat) : Submodule (Ring p k) (Vector p k d) :=
  Submodule.span (Ring p k) (activeSet entries left)

@[simp] theorem mem_activeSet_cons {p k d : Nat}
    (entry : TaggedVector p k d) (rest : List (TaggedVector p k d))
    (left : Nat) (row : Vector p k d) :
    row ∈ activeSet (entry :: rest) left ↔
      (left ≤ entry.timestamp ∧ row = entry.row) ∨ row ∈ activeSet rest left := by
  simp only [activeSet, Set.mem_setOf_eq, List.mem_cons]
  aesop

theorem activeSet_cons_of_le {p k d : Nat}
    (entry : TaggedVector p k d) (rest : List (TaggedVector p k d))
    (left : Nat) (hle : left ≤ entry.timestamp) :
    activeSet (entry :: rest) left = insert entry.row (activeSet rest left) := by
  ext row
  simp [mem_activeSet_cons, hle]

theorem activeSet_cons_of_not_le {p k d : Nat}
    (entry : TaggedVector p k d) (rest : List (TaggedVector p k d))
    (left : Nat) (hle : ¬left ≤ entry.timestamp) :
    activeSet (entry :: rest) left = activeSet rest left := by
  ext row
  simp [mem_activeSet_cons, hle]

private theorem left_mem_span_sub_pair {p k d : Nat}
    (x y : Vector p k d) (factor : Ring p k) (tail : Set (Vector p k d)) :
    x ∈ Submodule.span (Ring p k) (insert (x - factor • y) (insert y tail)) := by
  let target := Submodule.span (Ring p k) (insert (x - factor • y) (insert y tail))
  have hresidual : x - factor • y ∈ target :=
    Submodule.subset_span (by simp)
  have hy : y ∈ target := Submodule.subset_span (by simp)
  have hsum : (x - factor • y) + factor • y ∈ target :=
    Submodule.add_mem _ hresidual (Submodule.smul_mem _ factor hy)
  change x ∈ target
  have heq : x = (x - factor • y) + factor • y := by module
  rw [heq]
  exact hsum

private theorem left_mem_span_unit_pair {p k d : Nat}
    (x : Vector p k d) (unit : (Ring p k)ˣ) (tail : Set (Vector p k d)) :
    x ∈ Submodule.span (Ring p k) (insert ((unit : Ring p k) • x) tail) := by
  let target := Submodule.span (Ring p k) (insert ((unit : Ring p k) • x) tail)
  have hscaled : (unit : Ring p k) • x ∈ target :=
    Submodule.subset_span (by simp)
  have hback := Submodule.smul_mem _ ((unit⁻¹ : (Ring p k)ˣ) : Ring p k) hscaled
  change x ∈ target
  simpa [← mul_smul] using hback

/-- An elementary row subtraction preserves the span of the two rows together
with any common tail set. -/
theorem span_insert_sub_eq {p k d : Nat}
    (x y : Vector p k d) (factor : Ring p k) (tail : Set (Vector p k d)) :
    Submodule.span (Ring p k) (insert x (insert y tail)) =
      Submodule.span (Ring p k) (insert (x - factor • y) (insert y tail)) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    intro row hrow
    rcases hrow with hrow | hrow
    · subst row
      change x ∈ Submodule.span (Ring p k) (insert (x - factor • y) (insert y tail))
      exact left_mem_span_sub_pair x y factor tail
    · exact Submodule.subset_span (Or.inr hrow)
  · apply Submodule.span_le.2
    intro row hrow
    rcases hrow with hrow | hrow
    · subst row
      exact Submodule.sub_mem _
        (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ factor (Submodule.subset_span (by simp)))
    · exact Submodule.subset_span (Or.inr hrow)

/-- Scaling one generator by a unit does not change the surrounding span. -/
theorem span_insert_unit_eq {p k d : Nat}
    (x : Vector p k d) (unit : (Ring p k)ˣ) (tail : Set (Vector p k d)) :
    Submodule.span (Ring p k) (insert x tail) =
      Submodule.span (Ring p k) (insert ((unit : Ring p k) • x) tail) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    intro row hrow
    rcases hrow with hrow | hrow
    · subst row
      change x ∈ Submodule.span (Ring p k) (insert ((unit : Ring p k) • x) tail)
      exact left_mem_span_unit_pair x unit tail
    · exact Submodule.subset_span (Or.inr hrow)
  · apply Submodule.span_le.2
    intro row hrow
    rcases hrow with hrow | hrow
    · subst row
      exact Submodule.smul_mem _ (unit : Ring p k)
        (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (Or.inr hrow)

def ThresholdEquivalent {p k d : Nat}
    (before after : List (TaggedVector p k d)) : Prop :=
  ∀ left, activeSpan before left = activeSpan after left

theorem ThresholdEquivalent.refl {p k d : Nat}
    (entries : List (TaggedVector p k d)) : ThresholdEquivalent entries entries :=
  fun _ => rfl

theorem ThresholdEquivalent.symm {p k d : Nat}
    {a b : List (TaggedVector p k d)} (h : ThresholdEquivalent a b) :
    ThresholdEquivalent b a := fun left => (h left).symm

theorem ThresholdEquivalent.trans {p k d : Nat}
    {a b c : List (TaggedVector p k d)}
    (hab : ThresholdEquivalent a b) (hbc : ThresholdEquivalent b c) :
    ThresholdEquivalent a c := fun left => (hab left).trans (hbc left)

theorem activeSet_append {p k d : Nat}
    (a b : List (TaggedVector p k d)) (left : Nat) :
    activeSet (a ++ b) left = activeSet a left ∪ activeSet b left := by
  ext row
  simp only [activeSet, Set.mem_setOf_eq, List.mem_append, Set.mem_union]
  aesop

theorem activeSpan_append {p k d : Nat}
    (a b : List (TaggedVector p k d)) (left : Nat) :
    activeSpan (a ++ b) left = activeSpan a left ⊔ activeSpan b left := by
  rw [activeSpan, activeSet_append, Submodule.span_union]
  rfl

theorem ThresholdEquivalent.append_right {p k d : Nat}
    {a b : List (TaggedVector p k d)} (h : ThresholdEquivalent a b)
    (tail : List (TaggedVector p k d)) :
    ThresholdEquivalent (a ++ tail) (b ++ tail) := by
  intro left
  rw [activeSpan_append, activeSpan_append, h left]

theorem ThresholdEquivalent.append_left {p k d : Nat}
    {a b : List (TaggedVector p k d)} (h : ThresholdEquivalent a b)
    (front : List (TaggedVector p k d)) :
    ThresholdEquivalent (front ++ a) (front ++ b) := by
  intro left
  rw [activeSpan_append, activeSpan_append, h left]

theorem activeSet_eq_of_perm {p k d : Nat}
    {a b : List (TaggedVector p k d)} (h : a.Perm b) (left : Nat) :
    activeSet a left = activeSet b left := by
  ext row
  simp only [activeSet, Set.mem_setOf_eq]
  constructor <;> rintro ⟨entry, hentry, htime, rfl⟩
  · exact ⟨entry, h.mem_iff.mp hentry, htime, rfl⟩
  · exact ⟨entry, h.mem_iff.mpr hentry, htime, rfl⟩

theorem ThresholdEquivalent.of_perm {p k d : Nat}
    {a b : List (TaggedVector p k d)} (h : a.Perm b) :
    ThresholdEquivalent a b := by
  intro left
  rw [activeSpan, activeSpan, activeSet_eq_of_perm h left]

theorem zero_entry_equivalent {p k d : Nat} (entry : TaggedVector p k d)
    (hzero : entry.row = 0) : ThresholdEquivalent [entry] [] := by
  intro left
  by_cases htime : left ≤ entry.timestamp
  · rw [activeSpan, activeSpan, activeSet_cons_of_le entry [] left htime]
    simp [activeSet, hzero]
  · rw [activeSpan, activeSpan, activeSet_cons_of_not_le entry [] left htime]

theorem unit_scale_equivalent {p k d : Nat} (entry : TaggedVector p k d)
    (unit : (Ring p k)ˣ) (rest : List (TaggedVector p k d)) :
    ThresholdEquivalent (entry :: rest)
      (entry.withRow ((unit : Ring p k) • entry.row) :: rest) := by
  intro left
  by_cases htime : left ≤ entry.timestamp
  · rw [activeSpan, activeSpan,
      activeSet_cons_of_le entry rest left htime,
      activeSet_cons_of_le
        (entry.withRow ((unit : Ring p k) • entry.row)) rest left htime]
    exact span_insert_unit_eq entry.row unit (activeSet rest left)
  · rw [activeSpan, activeSpan,
      activeSet_cons_of_not_le entry rest left htime,
      activeSet_cons_of_not_le
        (entry.withRow ((unit : Ring p k) • entry.row)) rest left htime]

/-- Reducing an older task by a row with at least its timestamp preserves every
threshold-filtered span. -/
theorem reduce_by_newer_equivalent {p k d : Nat}
    (task pivot : TaggedVector p k d) (rest : List (TaggedVector p k d))
    (factor : Ring p k) (htime : task.timestamp ≤ pivot.timestamp) :
    ThresholdEquivalent (task :: pivot :: rest)
      (task.withRow (task.row - factor • pivot.row) :: pivot :: rest) := by
  intro left
  by_cases htask : left ≤ task.timestamp
  · have hpivot : left ≤ pivot.timestamp := le_trans htask htime
    rw [activeSpan, activeSpan, activeSet_cons_of_le _ _ _ htask,
      activeSet_cons_of_le _ _ _ hpivot,
      activeSet_cons_of_le (task.withRow (task.row - factor • pivot.row)) _ _ htask,
      activeSet_cons_of_le _ _ _ hpivot]
    exact span_insert_sub_eq task.row pivot.row factor (activeSet rest left)
  · rw [activeSpan, activeSpan, activeSet_cons_of_not_le _ _ _ htask,
      activeSet_cons_of_not_le
        (task.withRow (task.row - factor • pivot.row)) _ _ htask]

/-- Replacing an older stored row by a unit-normalized newer task and requeueing
the old residual preserves every threshold-filtered span. -/
theorem replace_older_equivalent {p k d : Nat}
    (task old : TaggedVector p k d) (rest : List (TaggedVector p k d))
    (unit : (Ring p k)ˣ) (factor : Ring p k)
    (htime : old.timestamp ≤ task.timestamp) :
    ThresholdEquivalent (task :: old :: rest)
      (task.withRow ((unit : Ring p k) • task.row) ::
        old.withRow (old.row - factor • ((unit : Ring p k) • task.row)) :: rest) := by
  intro left
  by_cases hold : left ≤ old.timestamp
  · have htask : left ≤ task.timestamp := le_trans hold htime
    rw [activeSpan, activeSpan,
      activeSet_cons_of_le _ _ _ htask, activeSet_cons_of_le _ _ _ hold,
      activeSet_cons_of_le (task.withRow ((unit : Ring p k) • task.row)) _ _ htask,
      activeSet_cons_of_le
        (old.withRow (old.row - factor • ((unit : Ring p k) • task.row))) _ _ hold]
    calc
      Submodule.span (Ring p k) (insert task.row (insert old.row (activeSet rest left))) =
          Submodule.span (Ring p k)
            (insert ((unit : Ring p k) • task.row) (insert old.row (activeSet rest left))) := by
              rw [span_insert_unit_eq]
      _ = Submodule.span (Ring p k)
            (insert ((unit : Ring p k) • task.row)
              (insert (old.row - factor • ((unit : Ring p k) • task.row))
                (activeSet rest left))) := by
              calc
                Submodule.span (Ring p k)
                    (insert ((unit : Ring p k) • task.row)
                      (insert old.row (activeSet rest left))) =
                    Submodule.span (Ring p k)
                      (insert old.row
                        (insert ((unit : Ring p k) • task.row) (activeSet rest left))) := by
                          rw [Set.insert_comm]
                _ = Submodule.span (Ring p k)
                      (insert (old.row - factor • ((unit : Ring p k) • task.row))
                        (insert ((unit : Ring p k) • task.row) (activeSet rest left))) :=
                          span_insert_sub_eq old.row
                            ((unit : Ring p k) • task.row) factor (activeSet rest left)
                _ = Submodule.span (Ring p k)
                      (insert ((unit : Ring p k) • task.row)
                        (insert (old.row - factor • ((unit : Ring p k) • task.row))
                          (activeSet rest left))) := by rw [Set.insert_comm]
  · by_cases htask : left ≤ task.timestamp
    · rw [activeSpan, activeSpan,
        activeSet_cons_of_le _ _ _ htask, activeSet_cons_of_not_le _ _ _ hold,
        activeSet_cons_of_le (task.withRow ((unit : Ring p k) • task.row)) _ _ htask,
        activeSet_cons_of_not_le
          (old.withRow (old.row - factor • ((unit : Ring p k) • task.row))) _ _ hold]
      exact span_insert_unit_eq task.row unit (activeSet rest left)
    · rw [activeSpan, activeSpan,
        activeSet_cons_of_not_le _ _ _ htask, activeSet_cons_of_not_le _ _ _ hold,
        activeSet_cons_of_not_le
          (task.withRow ((unit : Ring p k) • task.row)) _ _ htask,
        activeSet_cons_of_not_le
          (old.withRow (old.row - factor • ((unit : Ring p k) • task.row))) _ _ hold]

/-- If the requeued residual is zero, dropping it is also semantics-preserving. -/
theorem replace_older_zero_equivalent {p k d : Nat}
    (task old : TaggedVector p k d) (rest : List (TaggedVector p k d))
    (unit : (Ring p k)ˣ) (factor : Ring p k)
    (htime : old.timestamp ≤ task.timestamp)
    (hzero : old.row - factor • ((unit : Ring p k) • task.row) = 0) :
    ThresholdEquivalent (task :: old :: rest)
      (task.withRow ((unit : Ring p k) • task.row) :: rest) := by
  have hreplace := replace_older_equivalent task old rest unit factor htime
  intro left
  rw [hreplace left]
  by_cases hold : left ≤ old.timestamp
  · have htask : left ≤ task.timestamp := le_trans hold htime
    rw [activeSpan, activeSpan,
      activeSet_cons_of_le (task.withRow ((unit : Ring p k) • task.row)) _ _ htask,
      activeSet_cons_of_le
        (old.withRow (old.row - factor • ((unit : Ring p k) • task.row))) _ _ hold,
      activeSet_cons_of_le (task.withRow ((unit : Ring p k) • task.row)) _ _ htask]
    simp only [TaggedVector.withRow]
    rw [hzero, Set.insert_comm ((unit : Ring p k) • task.row) 0,
      Submodule.span_insert_zero]
  · by_cases htask : left ≤ task.timestamp
    · rw [activeSpan, activeSpan,
        activeSet_cons_of_le (task.withRow ((unit : Ring p k) • task.row)) _ _ htask,
        activeSet_cons_of_not_le
          (old.withRow (old.row - factor • ((unit : Ring p k) • task.row))) _ _ hold,
        activeSet_cons_of_le (task.withRow ((unit : Ring p k) • task.row)) _ _ htask]
    · rw [activeSpan, activeSpan,
        activeSet_cons_of_not_le
          (task.withRow ((unit : Ring p k) • task.row)) _ _ htask,
        activeSet_cons_of_not_le
          (old.withRow (old.row - factor • ((unit : Ring p k) • task.row))) _ _ hold,
        activeSet_cons_of_not_le
          (task.withRow ((unit : Ring p k) • task.row)) _ _ htask]

structure TaggedPivot (p k d : Nat) where
  timestamp : Nat
  layer : Nat
  pivot : PivotRow p k d

def TaggedPivot.asVector {p k d : Nat} (entry : TaggedPivot p k d) :
    TaggedVector p k d :=
  { timestamp := entry.timestamp, layer := entry.layer, row := entry.pivot.row }

@[simp] theorem TaggedPivot.asVector_timestamp {p k d : Nat}
    (entry : TaggedPivot p k d) : entry.asVector.timestamp = entry.timestamp := rfl

@[simp] theorem TaggedPivot.asVector_layer {p k d : Nat}
    (entry : TaggedPivot p k d) : entry.asVector.layer = entry.layer := rfl

@[simp] theorem TaggedPivot.asVector_row {p k d : Nat}
    (entry : TaggedPivot p k d) : entry.asVector.row = entry.pivot.row := rfl

def pivotsAt {p k d : Nat} (entries : List (TaggedPivot p k d))
    (left : Nat) : List (PivotRow p k d) :=
  (entries.filter fun entry => left ≤ entry.timestamp).map TaggedPivot.pivot

structure SourceVector (p k d : Nat) where
  timestamp : Nat
  row : Vector p k d

def sourceSet {p k d : Nat} (source : List (SourceVector p k d))
    (left : Nat) : Set (Vector p k d) :=
  {row | ∃ entry ∈ source, left ≤ entry.timestamp ∧ row = entry.row}

def sourceSubmodule {p k d : Nat} (source : List (SourceVector p k d))
    (left : Nat) : Submodule (Ring p k) (Vector p k d) :=
  Submodule.span (Ring p k) (sourceSet source left)

theorem sourceSet_cons_of_le {p k d : Nat}
    (head : SourceVector p k d) (tail : List (SourceVector p k d))
    (left : Nat) (hle : left ≤ head.timestamp) :
    sourceSet (head :: tail) left = insert head.row (sourceSet tail left) := by
  ext row
  simp only [sourceSet, Set.mem_setOf_eq, List.mem_cons]
  constructor
  · rintro ⟨entry, rfl | hentry, htime, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨entry, hentry, htime, rfl⟩
  · rintro (rfl | ⟨entry, hentry, htime, rfl⟩)
    · exact ⟨head, by simp, hle, rfl⟩
    · exact ⟨entry, by simp [hentry], htime, rfl⟩

theorem sourceSet_cons_of_not_le {p k d : Nat}
    (head : SourceVector p k d) (tail : List (SourceVector p k d))
    (left : Nat) (hle : ¬left ≤ head.timestamp) :
    sourceSet (head :: tail) left = sourceSet tail left := by
  ext row
  simp only [sourceSet, Set.mem_setOf_eq, List.mem_cons]
  constructor
  · rintro ⟨entry, rfl | hentry, htime, rfl⟩
    · exact False.elim (hle htime)
    · exact ⟨entry, hentry, htime, rfl⟩
  · rintro ⟨entry, hentry, htime, rfl⟩
    exact ⟨entry, by simp [hentry], htime, rfl⟩

theorem sourceSet_eq_zero_of_all {p k d : Nat}
    (source : List (SourceVector p k d)) (left : Nat)
    (hall : ∀ entry ∈ source, left ≤ entry.timestamp) :
    sourceSet source left = sourceSet source 0 := by
  ext row
  simp only [sourceSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨entry, hentry, htime, rfl⟩
    exact ⟨entry, hentry, Nat.zero_le _, rfl⟩
  · rintro ⟨entry, hentry, htime, rfl⟩
    exact ⟨entry, hentry, hall entry hentry, rfl⟩

theorem sourceSubmodule_antitone {p k d : Nat}
    (source : List (SourceVector p k d)) {smallLeft largeLeft : Nat}
    (hle : smallLeft ≤ largeLeft) :
    sourceSubmodule source largeLeft ≤ sourceSubmodule source smallLeft := by
  apply Submodule.span_mono
  rintro row ⟨entry, hentry, htime, rfl⟩
  exact ⟨entry, hentry, le_trans hle htime, rfl⟩

theorem sourceSubmodule_mono_source {p k d : Nat}
    {small large : List (SourceVector p k d)} (hsource : ∀ item ∈ small, item ∈ large)
    (left : Nat) : sourceSubmodule small left ≤ sourceSubmodule large left := by
  apply Submodule.span_mono
  rintro row ⟨entry, hentry, htime, rfl⟩
  exact ⟨entry, hsource entry hentry, htime, rfl⟩

theorem pivotsAt_zero {p k d : Nat} (entries : List (TaggedPivot p k d)) :
    pivotsAt entries 0 = entries.map TaggedPivot.pivot := by
  simp [pivotsAt]

theorem pivotsAt_eq_map_of_all {p k d : Nat}
    (entries : List (TaggedPivot p k d)) (left : Nat)
    (hall : ∀ entry ∈ entries, left ≤ entry.timestamp) :
    pivotsAt entries left = entries.map TaggedPivot.pivot := by
  unfold pivotsAt
  congr 1
  apply List.filter_eq_self.2
  intro entry hentry
  simpa using hall entry hentry

structure CorrectTable {p k d : Nat} (source : List (SourceVector p k d))
    (entries : List (TaggedPivot p k d)) : Prop where
  ordered : Ordered (entries.map TaggedPivot.pivot)
  span_at : ∀ left,
    sourceSubmodule source left =
      Submodule.span (Ring p k) {row | row ∈ rowsOf (pivotsAt entries left)}
  card_at : ∀ left,
    Nat.card (sourceSubmodule source left) = p ^ (pivotsAt entries left).length

theorem ordered_pivotsAt {p k d : Nat} {entries : List (TaggedPivot p k d)}
    (hordered : Ordered (entries.map TaggedPivot.pivot)) (left : Nat) :
    Ordered (pivotsAt entries left) := by
  induction entries with
  | nil => simp [pivotsAt, Ordered]
  | cons head tail ih =>
      rw [List.map_cons, Ordered] at hordered
      cases hordered with
      | cons hhead htail =>
        simp only [pivotsAt, List.filter_cons]
        split_ifs with hkeep
        · rw [List.map_cons, Ordered]
          constructor
          · intro pivot hpivot
            simp only [List.mem_map, List.mem_filter] at hpivot
            rcases hpivot with ⟨entry, ⟨hentry, _⟩, rfl⟩
            exact hhead entry.pivot (List.mem_map.mpr ⟨entry, hentry, rfl⟩)
          · exact ih htail
        · exact ih htail

noncomputable def basisAt {p k d : Nat} {source : List (SourceVector p k d)}
    {entries : List (TaggedPivot p k d)}
    (correct : CorrectTable source entries) (left : Nat) : Basis p k d where
  pivots := pivotsAt entries left
  ordered := ordered_pivotsAt correct.ordered left
  generated := sourceSubmodule source left
  generated_eq_span := correct.span_at left
  card_generated := correct.card_at left

/-- Once insertion supplies a correct timestamp table, the existing complete
query derivation gives a certified answer for every interval endpoint. -/
theorem query_complete {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)}
    {entries : List (TaggedPivot p k d)}
    (correct : CorrectTable source entries) (left : Nat)
    (target : Vector p k d) :
    ∃ answer : Bool, ∃ derivation : Derivation (basisAt correct left) target answer,
      (answer = true ↔ target ∈ sourceSubmodule source left) ∧
      derivation.reductions ≤ d := by
  exact exists_correct_answer (basisAt correct left) hp.one_lt target

end CompositeModulusBasis.TimestampedBasis
