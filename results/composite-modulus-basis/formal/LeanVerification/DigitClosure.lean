import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic

/-!
# Triangular p-digit systems

Rows in a p-digit echelon table are used with digits `0, ..., p-1`, not with
arbitrary ring coefficients.  The crucial closure condition is triangular:
`p • head` already has a digit representation by later rows.  This file proves
that condition is sufficient for digit representations to form an additive
subgroup, including carry and borrow.  Consequently, over `ZMod N`, they form
a submodule and equal the ordinary submodule span of the rows.
-/

namespace CompositeModulusBasis.DigitClosure

variable {A : Type*} [AddCommGroup A]

/-- `DigitRep p rows x` means `x` is represented using one base-`p` digit per row. -/
inductive DigitRep (p : Nat) : List A → A → Prop where
  | nil : DigitRep p [] 0
  | cons {head : A} {tail : List A} {x : A} (digit : Nat)
      (digit_lt : digit < p) (tail_rep : DigitRep p tail x) :
      DigitRep p (head :: tail) (digit • head + x)

/-- Every carry from a row is representable strictly to its right. -/
inductive Triangular (p : Nat) : List A → Prop where
  | nil : Triangular p []
  | cons {head : A} {tail : List A}
      (carry : DigitRep p tail (p • head))
      (tail_triangular : Triangular p tail) : Triangular p (head :: tail)

theorem DigitRep.eq_zero_of_nil {p : Nat} {x : A} (h : DigitRep p [] x) : x = 0 := by
  cases h
  rfl

theorem DigitRep.zero (p : Nat) (hp : 0 < p) : ∀ rows : List A, DigitRep p rows 0
  | [] => .nil
  | _ :: tail => by
      simpa using DigitRep.cons 0 hp (DigitRep.zero p hp tail)

private theorem quotient_of_two_digits_lt_two {p a b : Nat}
    (hp : 0 < p) (ha : a < p) (hb : b < p) : (a + b) / p < 2 := by
  rw [Nat.div_lt_iff_lt_mul hp]
  omega

private theorem digit_remainder_lt {p total : Nat} (hp : 0 < p) : total % p < p :=
  Nat.mod_lt _ hp

/-- Base-`p` addition, including the carry into the triangular tail. -/
theorem DigitRep.add (hp : 0 < p) {rows : List A} (triangular : Triangular p rows)
    {x y : A} (hx : DigitRep p rows x) (hy : DigitRep p rows y) :
    DigitRep p rows (x + y) := by
  induction triangular generalizing x y with
  | nil =>
      have hx0 := hx.eq_zero_of_nil
      have hy0 := hy.eq_zero_of_nil
      subst x
      subst y
      simpa using (DigitRep.nil : DigitRep p [] (0 : A))
  | @cons head tail carry tail_triangular ih =>
      cases hx with
      | cons a ha hxt =>
        rename_i tailX
        cases hy with
        | cons b hb hyt =>
          rename_i tailY
          let total := a + b
          let digit := total % p
          let quotient := total / p
          have hdigit : digit < p := digit_remainder_lt hp
          have hquot : quotient < 2 := quotient_of_two_digits_lt_two hp ha hb
          have hdecomp : total = digit + p * quotient := by
            dsimp [digit, quotient]
            exact (Nat.mod_add_div _ _).symm
          have htails : DigitRep p tail (_ + _) := ih hxt hyt
          have htail : DigitRep p tail (quotient • (p • head) + (tailX + tailY)) := by
            interval_cases quotient
            · simpa using htails
            · have hcarrysum := ih carry htails
              simpa [one_nsmul] using hcarrysum
          have hresult : DigitRep p (head :: tail)
              (digit • head + (quotient • (p • head) + (tailX + tailY))) :=
            DigitRep.cons digit hdigit htail
          have hcomm : (p * quotient) • head = quotient • (p • head) := by
            rw [← mul_nsmul, Nat.mul_comm]
          have hnsmul : total • head =
              digit • head + quotient • (p • head) := by
            calc
              total • head = (digit + p * quotient) • head := by rw [hdecomp]
              _ = digit • head + (p * quotient) • head := by rw [add_nsmul]
              _ = digit • head + quotient • (p • head) := by rw [hcomm]
          convert hresult using 1
          calc
            a • head + tailX + (b • head + tailY) =
                (a • head + b • head) + (tailX + tailY) := by abel
            _ = total • head + (tailX + tailY) := by
              rw [← add_nsmul]
            _ = digit • head + quotient • (p • head) + (tailX + tailY) := by
              rw [hnsmul]
            _ = digit • head + (quotient • (p • head) + (tailX + tailY)) := by abel

/-- Base-`p` negation, including borrow into the triangular tail. -/
theorem DigitRep.neg (hp : 0 < p) {rows : List A} (triangular : Triangular p rows)
    {x : A} (hx : DigitRep p rows x) : DigitRep p rows (-x) := by
  induction triangular generalizing x with
  | nil =>
      have hx0 := hx.eq_zero_of_nil
      subst x
      simpa using (DigitRep.nil : DigitRep p [] (0 : A))
  | @cons head tail carry tail_triangular ih =>
      cases hx with
      | cons digit hdigit htail =>
        rename_i tailValue
        by_cases hzero : digit = 0
        · subst digit
          have hneg := ih htail
          simpa using DigitRep.cons 0 hp hneg
        · have hpos : 0 < digit := Nat.pos_of_ne_zero hzero
          have hle : digit ≤ p := Nat.le_of_lt hdigit
          have hborrowDigit : p - digit < p := by omega
          have hnegCarry := ih carry
          have hnegTail := ih htail
          have hborrowTail := DigitRep.add hp tail_triangular hnegCarry hnegTail
          have hresult : DigitRep p (head :: tail)
              ((p - digit) • head + (-(p • head) + -tailValue)) :=
            DigitRep.cons (p - digit) hborrowDigit hborrowTail
          have hsplit : digit + (p - digit) = p := Nat.add_sub_of_le hle
          have hnsmul : p • head = digit • head + (p - digit) • head := by
            calc
              p • head = (digit + (p - digit)) • head := by rw [hsplit]
              _ = digit • head + (p - digit) • head := by rw [add_nsmul]
          convert hresult using 1
          rw [hnsmul]
          abel

/-- Every listed row has the representation with digit one at its position. -/
theorem DigitRep.of_mem (p : Nat) (hp : 1 < p) {rows : List A} {row : A}
    (hrow : row ∈ rows) : DigitRep p rows row := by
  induction rows with
  | nil => simp at hrow
  | cons head tail ih =>
      rcases List.mem_cons.mp hrow with rfl | htail
      · simpa using DigitRep.cons 1 hp (DigitRep.zero p (Nat.zero_lt_of_lt hp) tail)
      · simpa using DigitRep.cons 0 (Nat.zero_lt_of_lt hp) (ih htail)

/-- A digit representation is, in particular, an ordinary additive-span representation. -/
theorem DigitRep.mem_zmod_span (N p : Nat) [Module (ZMod N) A]
    {rows : List A} {x : A} (hx : DigitRep p rows x) :
    x ∈ Submodule.span (ZMod N) {row | row ∈ rows} := by
  induction hx with
  | nil => exact Submodule.zero_mem _
  | @cons head tail x digit digit_lt tail_rep ih =>
      apply Submodule.add_mem
      · simpa [Nat.cast_smul_eq_nsmul] using
          (Submodule.smul_mem (Submodule.span (ZMod N) {row | row ∈ head :: tail})
            (digit : ZMod N) (Submodule.subset_span (by simp)))
      · exact Submodule.span_mono (by simp +contextual) ih

/-- A triangular digit system is an additive subgroup. -/
def digitAddSubgroup (p : Nat) (hp : 0 < p) (rows : List A)
    (triangular : Triangular p rows) : AddSubgroup A where
  carrier := {x | DigitRep p rows x}
  zero_mem' := DigitRep.zero p hp rows
  add_mem' hx hy := hx.add hp triangular hy
  neg_mem' hx := hx.neg hp triangular

@[simp] theorem mem_digitAddSubgroup_iff (p : Nat) (hp : 0 < p) (rows : List A)
    (triangular : Triangular p rows) (x : A) :
    x ∈ digitAddSubgroup p hp rows triangular ↔ DigitRep p rows x := Iff.rfl

section ZMod

variable (N : Nat) [Module (ZMod N) A]

/-- Over `ZMod N`, every additive subgroup is automatically a `ZMod N` submodule. -/
def digitSubmodule (p : Nat) (hp : 0 < p) (rows : List A)
    (triangular : Triangular p rows) : Submodule (ZMod N) A :=
  AddSubgroup.toZModSubmodule N (digitAddSubgroup p hp rows triangular)

@[simp] theorem mem_digitSubmodule_iff (p : Nat) (hp : 0 < p) (rows : List A)
    (triangular : Triangular p rows) (x : A) :
    x ∈ digitSubmodule N p hp rows triangular ↔ DigitRep p rows x := Iff.rfl

/-- Every listed row has its obvious digit representation. -/
theorem row_mem_digitSubmodule (p : Nat) (hp : 1 < p) (rows : List A)
    (triangular : Triangular p rows) {row : A} (hrow : row ∈ rows) :
    row ∈ digitSubmodule N p (Nat.zero_lt_of_lt hp) rows triangular :=
  DigitRep.of_mem p hp hrow

/-- The triangular digit submodule is exactly the ordinary span of its rows. -/
theorem digitSubmodule_eq_span (p : Nat) (hp : 1 < p) (rows : List A)
    (triangular : Triangular p rows) :
    digitSubmodule N p (Nat.zero_lt_of_lt hp) rows triangular =
      Submodule.span (ZMod N) {row | row ∈ rows} := by
  apply le_antisymm
  · intro x hx
    change DigitRep p rows x at hx
    exact hx.mem_zmod_span N p
  · apply Submodule.span_le.2
    intro row hrow
    exact row_mem_digitSubmodule N p hp rows triangular hrow

end ZMod

end CompositeModulusBasis.DigitClosure
