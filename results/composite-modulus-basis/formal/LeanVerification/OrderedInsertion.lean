import LeanVerification.PadicEchelon
import Mathlib.Tactic

/-!
# Inserting normalized pivots into slot order

The Python table is an array indexed by `(column, level)`.  For mathematical
reasoning we use the equivalent strictly ordered list.  These lemmas verify the
one-slot insertion operation used to assemble such a list.
-/

namespace CompositeModulusBasis.OrderedInsertion

open PadicEchelon

instance {d k : Nat} (a b : Slot d k) : Decidable (Slot.lt a b) := by
  unfold Slot.lt
  infer_instance

theorem Slot.lt_asymm {d k : Nat} {a b : Slot d k} : Slot.lt a b → ¬Slot.lt b a := by
  simp only [Slot.lt]
  omega

theorem Slot.lt_or_eq_or_lt {d k : Nat} (a b : Slot d k) :
    Slot.lt a b ∨ a = b ∨ Slot.lt b a := by
  rcases lt_trichotomy a.1 b.1 with hcol | hcol | hcol
  · exact Or.inl (Or.inl hcol)
  · rcases lt_trichotomy a.2 b.2 with hlevel | hlevel | hlevel
    · exact Or.inl (Or.inr ⟨hcol, hlevel⟩)
    · exact Or.inr (Or.inl (Prod.ext hcol hlevel))
    · exact Or.inr (Or.inr (Or.inr ⟨hcol.symm, hlevel⟩))
  · exact Or.inr (Or.inr (Or.inl hcol))

def insertPivot {p k d : Nat} (pivot : PivotRow p k d) :
    List (PivotRow p k d) → List (PivotRow p k d)
  | [] => [pivot]
  | current :: rest =>
      if Slot.lt pivot.slot current.slot then pivot :: current :: rest
      else current :: insertPivot pivot rest

@[simp] theorem mem_insertPivot {p k d : Nat} (pivot value : PivotRow p k d)
    (rows : List (PivotRow p k d)) :
    value ∈ insertPivot pivot rows ↔ value = pivot ∨ value ∈ rows := by
  induction rows with
  | nil => simp [insertPivot]
  | cons current rest ih =>
      simp only [insertPivot]
      split <;> simp [ih, or_left_comm]

@[simp] theorem length_insertPivot {p k d : Nat} (pivot : PivotRow p k d)
    (rows : List (PivotRow p k d)) :
    (insertPivot pivot rows).length = rows.length + 1 := by
  induction rows with
  | nil => simp [insertPivot]
  | cons current rest ih =>
      simp only [insertPivot]
      split <;> simp [ih]

theorem ordered_insertPivot {p k d : Nat} (pivot : PivotRow p k d)
    (rows : List (PivotRow p k d)) (hordered : Ordered rows)
    (hfresh : ∀ current ∈ rows, current.slot ≠ pivot.slot) :
    Ordered (insertPivot pivot rows) := by
  induction rows with
  | nil => simp [insertPivot, Ordered]
  | cons current rest ih =>
      rw [Ordered] at hordered ⊢
      cases hordered with
      | cons hcurrent hrest =>
        simp only [insertPivot]
        split_ifs with hbefore
        · constructor
          · intro value hvalue
            rcases List.mem_cons.mp hvalue with rfl | hvalue
            · exact hbefore
            · exact Slot.lt_trans hbefore (hcurrent _ hvalue)
          · exact List.pairwise_cons.2 ⟨hcurrent, hrest⟩
        · constructor
          · intro value hvalue
            have hcurrentPivot : Slot.lt current.slot pivot.slot := by
              rcases Slot.lt_or_eq_or_lt current.slot pivot.slot with hlt | heq | hgt
              · exact hlt
              · exact False.elim (hfresh current (by simp) heq)
              · exact False.elim (hbefore hgt)
            rw [mem_insertPivot] at hvalue
            rcases hvalue with rfl | hvalue
            · exact hcurrentPivot
            · exact hcurrent _ hvalue
          · apply ih hrest
            intro value hvalue
            exact hfresh value (by simp [hvalue])

def insertAll {p k d : Nat} :
    List (PivotRow p k d) → List (PivotRow p k d) → List (PivotRow p k d)
  | [], rows => rows
  | pivot :: rest, rows => insertAll rest (insertPivot pivot rows)

@[simp] theorem mem_insertAll {p k d : Nat} (value : PivotRow p k d)
    (additions rows : List (PivotRow p k d)) :
    value ∈ insertAll additions rows ↔ value ∈ additions ∨ value ∈ rows := by
  induction additions generalizing rows with
  | nil => simp [insertAll]
  | cons pivot rest ih =>
      rw [insertAll, ih, mem_insertPivot]
      aesop

@[simp] theorem length_insertAll {p k d : Nat}
    (additions rows : List (PivotRow p k d)) :
    (insertAll additions rows).length = rows.length + additions.length := by
  induction additions generalizing rows with
  | nil => simp [insertAll]
  | cons pivot rest ih =>
      rw [insertAll, ih, length_insertPivot]
      simp only [List.length_cons]
      omega

theorem ordered_insertAll {p k d : Nat}
    (additions rows : List (PivotRow p k d))
    (hadditions : Ordered additions) (hrows : Ordered rows)
    (hcross : ∀ added ∈ additions, ∀ current ∈ rows, current.slot ≠ added.slot) :
    Ordered (insertAll additions rows) := by
  induction additions generalizing rows with
  | nil => simpa [insertAll] using hrows
  | cons pivot rest ih =>
      rw [Ordered] at hadditions
      cases hadditions with
      | cons hpivot hrest =>
        rw [insertAll]
        apply ih (insertPivot pivot rows) hrest (ordered_insertPivot pivot rows hrows ?_) ?_
        · intro current hcurrent
          exact hcross pivot (by simp) current hcurrent
        · intro added hadded current hcurrent
          rw [mem_insertPivot] at hcurrent
          rcases hcurrent with rfl | hcurrent
          · intro heq
            have hlt := hpivot added hadded
            rw [heq] at hlt
            exact Slot.lt_irrefl _ hlt
          · exact hcross added (by simp [hadded]) current hcurrent

end CompositeModulusBasis.OrderedInsertion
