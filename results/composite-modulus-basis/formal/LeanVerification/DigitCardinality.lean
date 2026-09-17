import LeanVerification.PadicEchelon
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Injectivity and cardinality of normalized p-adic echelon digits

An ordered list of normalized pivots has `p^s` distinct digit combinations,
where `s` is its length. This does not assume that the combinations are
already closed under arbitrary coefficients. The result is the cardinality
half of the p-digit-basis invariant used by insertion.
-/

namespace CompositeModulusBasis.DigitCardinality

open DigitClosure PadicArithmetic PadicEchelon

abbrev Digits (p : Nat) {k d : Nat} (pivots : List (PivotRow p k d)) :=
  List.Vector (Fin p) pivots.length

@[simp] theorem card_digits (p : Nat) {k d : Nat} (pivots : List (PivotRow p k d)) :
    Fintype.card (Digits p pivots) = p ^ pivots.length := by
  simp

def encodeList {p k d : Nat} :
    List (PivotRow p k d) → List (Fin p) → Vector p k d
  | [], _ => 0
  | _, [] => 0
  | head :: tail, digit :: digits => digit.val • head.row + encodeList tail digits

def encode {p k d : Nat} {pivots : List (PivotRow p k d)}
    (digits : Digits p pivots) : Vector p k d :=
  encodeList pivots digits.toList

theorem encodeList_digitRep {p k d : Nat} {pivots : List (PivotRow p k d)}
    {digits : List (Fin p)} (hlength : digits.length = pivots.length) :
    DigitRep p (rowsOf pivots) (encodeList pivots digits) := by
  induction pivots generalizing digits with
  | nil =>
      have : digits = [] := List.length_eq_zero_iff.mp hlength
      subst digits
      exact DigitRep.nil
  | cons head tail ih =>
      cases digits with
      | nil => simp at hlength
      | cons digit rest =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          exact DigitRep.cons digit.val digit.isLt (ih hlength)

theorem encode_digitRep {p k d : Nat} {pivots : List (PivotRow p k d)}
    (digits : Digits p pivots) : DigitRep p (rowsOf pivots) (encode digits) :=
  encodeList_digitRep digits.toList_length

/-- The normalized leading coordinate recovers the head digit. -/
private theorem head_digit_eq {p k d : Nat} (hp : 1 < p)
    (head : PivotRow p k d) {tail : List (PivotRow p k d)}
    (hlater : ∀ pivot ∈ tail, Slot.lt head.slot pivot.slot)
    (leftHead rightHead : Fin p) (leftTail rightTail : List (Fin p))
    (hleftLength : leftTail.length = tail.length)
    (hrightLength : rightTail.length = tail.length)
    (heq : encodeList (head :: tail) (leftHead :: leftTail) =
      encodeList (head :: tail) (rightHead :: rightTail)) :
    leftHead = rightHead := by
  have hleftHigher := tailRep_higherAt head hlater (encodeList_digitRep hleftLength)
  have hrightHigher := tailRep_higherAt head hlater (encodeList_digitRep hrightLength)
  rcases hleftHigher with ⟨leftCarry, hleftCarry⟩
  rcases hrightHigher with ⟨rightCarry, hrightCarry⟩
  have hcoordinate := congrFun heq head.slot.1
  change leftHead.val • head.row head.slot.1 + encodeList tail leftTail head.slot.1 =
    rightHead.val • head.row head.slot.1 + encodeList tail rightTail head.slot.1 at hcoordinate
  rw [head.pivot, hleftCarry, hrightCarry] at hcoordinate
  have hfactored :
      ((p ^ (head.slot.2 : Nat) * (leftHead.val + p * leftCarry) : Nat) : Ring p k) =
      ((p ^ (head.slot.2 : Nat) * (rightHead.val + p * rightCarry) : Nat) : Ring p k) := by
    convert hcoordinate using 1 <;> push_cast <;> rw [pow_succ] <;> ring
  apply Fin.ext
  exact digit_eq_of_zmod_eq hp head.slot.2.isLt leftHead.isLt rightHead.isLt hfactored

private theorem encodeList_injective {p k d : Nat} (hp : 1 < p)
    {pivots : List (PivotRow p k d)} (ordered : Ordered pivots)
    {left right : List (Fin p)}
    (hleftLength : left.length = pivots.length)
    (hrightLength : right.length = pivots.length)
    (heq : encodeList pivots left = encodeList pivots right) : left = right := by
  induction pivots generalizing left right with
  | nil =>
      exact (List.length_eq_zero_iff.mp hleftLength).trans
        (List.length_eq_zero_iff.mp hrightLength).symm
  | cons head tail ih =>
      cases left with
      | nil => simp at hleftLength
      | cons leftHead leftTail =>
        cases right with
        | nil => simp at hrightLength
        | cons rightHead rightTail =>
          simp only [List.length_cons, Nat.succ.injEq] at hleftLength hrightLength
          rw [Ordered] at ordered
          cases ordered with
          | cons hlater tailOrdered =>
            have hhead := head_digit_eq hp head hlater leftHead rightHead leftTail rightTail
              hleftLength hrightLength heq
            subst rightHead
            have htailEncode : encodeList tail leftTail = encodeList tail rightTail := by
              exact add_left_cancel heq
            have htail := ih tailOrdered hleftLength hrightLength htailEncode
            subst rightTail
            rfl

/-- Distinct digit vectors encode distinct module vectors. -/
theorem encode_injective {p k d : Nat} (hp : 1 < p)
    {pivots : List (PivotRow p k d)} (ordered : Ordered pivots) :
    Function.Injective (encode (pivots := pivots)) := by
  intro left right heq
  apply Subtype.ext
  exact encodeList_injective hp ordered left.toList_length right.toList_length heq

/-- The image of `encode` has exactly `p^s` elements. -/
theorem card_range_encode {p k d : Nat} (hp : 1 < p)
    {pivots : List (PivotRow p k d)} (ordered : Ordered pivots) :
    Nat.card (Set.range (encode (pivots := pivots))) = p ^ pivots.length := by
  let equivalence : Digits p pivots ≃ Set.range (encode (pivots := pivots)) :=
    Equiv.ofInjective (encode (pivots := pivots)) (encode_injective hp ordered)
  calc
    Nat.card (Set.range (encode (pivots := pivots))) = Nat.card (Digits p pivots) :=
      (Nat.card_congr equivalence).symm
    _ = Fintype.card (Digits p pivots) := Nat.card_eq_fintype_card
    _ = p ^ pivots.length := card_digits p pivots

/-- Cardinal form of a complete p-digit basis. -/
structure CardinalBasis (p k d : Nat) where
  pivots : List (PivotRow p k d)
  ordered : Ordered pivots
  generated : Submodule (Ring p k) (Vector p k d)
  generated_eq_span : generated =
    Submodule.span (Ring p k) {row | row ∈ rowsOf pivots}
  card_generated : Nat.card generated = p ^ pivots.length

def CardinalBasis.encodeInto {p k d : Nat} (basis : CardinalBasis p k d)
    (digits : Digits p basis.pivots) : basis.generated := by
  refine ⟨encode digits, ?_⟩
  rw [basis.generated_eq_span]
  exact (encode_digitRep digits).mem_zmod_span (p ^ k) p

theorem CardinalBasis.encodeInto_injective {p k d : Nat} (basis : CardinalBasis p k d)
    (hp : 1 < p) : Function.Injective basis.encodeInto := by
  intro left right heq
  apply encode_injective hp basis.ordered
  exact congrArg Subtype.val heq

theorem CardinalBasis.encodeInto_surjective {p k d : Nat} (basis : CardinalBasis p k d)
    (hp : 1 < p) : Function.Surjective basis.encodeInto := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Nat.ne_of_gt (Nat.zero_lt_of_lt hp))⟩
  letI : Finite basis.generated := Finite.of_injective Subtype.val Subtype.val_injective
  have hcard : Nat.card (Digits p basis.pivots) = Nat.card basis.generated := by
    calc
      Nat.card (Digits p basis.pivots) = Fintype.card (Digits p basis.pivots) :=
        Nat.card_eq_fintype_card
      _ = p ^ basis.pivots.length := card_digits p basis.pivots
      _ = Nat.card basis.generated := basis.card_generated.symm
  exact ((Nat.bijective_iff_injective_and_card basis.encodeInto).2
    ⟨basis.encodeInto_injective hp, hcard⟩).2

/-- Cardinality plus normalized ordered pivots gives existence of p-digit expansions. -/
theorem CardinalBasis.mem_iff_digitRep {p k d : Nat} (basis : CardinalBasis p k d)
    (hp : 1 < p) (x : Vector p k d) :
    x ∈ basis.generated ↔ DigitRep p (rowsOf basis.pivots) x := by
  constructor
  · intro hx
    rcases basis.encodeInto_surjective hp ⟨x, hx⟩ with ⟨digits, hdigits⟩
    have hvalue : encode digits = x := congrArg Subtype.val hdigits
    rw [← hvalue]
    exact encode_digitRep digits
  · intro hx
    rw [basis.generated_eq_span]
    exact hx.mem_zmod_span (p ^ k) p

end CompositeModulusBasis.DigitCardinality
