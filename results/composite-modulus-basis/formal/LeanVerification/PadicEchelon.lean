import LeanVerification.DigitClosure
import LeanVerification.PadicArithmetic
import Mathlib.Tactic

/-!
# Concrete p-adic echelon rows over `ZMod (p^k)`

This file connects the abstract digit-carry theorem to the actual slot order
`(column, p-adic level)`.  It proves that a nonzero leading digit remains
visible modulo `p^k` despite every later row, and hence that every nonzero
element represented by an echelon table has the leading slot of one of its
pivots.
-/

namespace CompositeModulusBasis.PadicEchelon

open DigitClosure PadicArithmetic

abbrev Ring (p k : Nat) := ZMod (p ^ k)
abbrev Vector (p k d : Nat) := Fin d → Ring p k
abbrev Slot (d k : Nat) := Fin d × Fin k

def Slot.lt {d k : Nat} (a b : Slot d k) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

theorem Slot.lt_irrefl {d k : Nat} (a : Slot d k) : ¬ Slot.lt a a := by
  simp [Slot.lt]

theorem Slot.lt_trans {d k : Nat} {a b c : Slot d k} :
    Slot.lt a b → Slot.lt b c → Slot.lt a c := by
  simp only [Slot.lt]
  omega

/-- Lexicographic slots are linearly ordered, stated without installing a global
`LT` instance for the product type. -/
theorem Slot.lt_or_eq_or_lt {d k : Nat} (a b : Slot d k) :
    Slot.lt a b ∨ a = b ∨ Slot.lt b a := by
  rcases lt_trichotomy a.1 b.1 with hcolumn | hcolumn | hcolumn
  · exact Or.inl (Or.inl hcolumn)
  · rcases lt_trichotomy a.2 b.2 with hlevel | hlevel | hlevel
    · exact Or.inl (Or.inr ⟨hcolumn, hlevel⟩)
    · exact Or.inr (Or.inl (Prod.ext hcolumn hlevel))
    · exact Or.inr (Or.inr (Or.inr ⟨hcolumn.symm, hlevel⟩))
  · exact Or.inr (Or.inr (Or.inl hcolumn))

/-- A coordinate is divisible by the next p-adic power. -/
def HigherAt (p k v : Nat) (x : Ring p k) : Prop :=
  ∃ tail : Nat, x = ((p ^ (v + 1) * tail : Nat) : Ring p k)

/-- A coordinate has a nonzero digit at exactly p-adic level `v`. -/
def ExactAt (p k v : Nat) (x : Ring p k) : Prop :=
  ∃ digit : Nat, 0 < digit ∧ digit < p ∧
    ∃ tail : Nat, x = ((p ^ v * (digit + p * tail) : Nat) : Ring p k)

theorem ExactAt.ne_zero {p k v : Nat} (hp : 1 < p) (hv : v < k)
    {x : Ring p k} (hx : ExactAt p k v x) : x ≠ 0 := by
  rcases hx with ⟨digit, hdpos, hdlt, tail, rfl⟩
  exact digit_head_ne_zero hp hv hdpos hdlt

structure PivotRow (p k d : Nat) where
  slot : Slot d k
  row : Vector p k d
  zerosBefore : ∀ column : Fin d, column < slot.1 → row column = 0
  pivot : row slot.1 = ((p ^ (slot.2 : Nat) : Nat) : Ring p k)

def rowsOf {p k d : Nat} (rows : List (PivotRow p k d)) : List (Vector p k d) :=
  rows.map PivotRow.row

def Ordered {p k d : Nat} (rows : List (PivotRow p k d)) : Prop :=
  rows.Pairwise fun a b => Slot.lt a.slot b.slot

theorem ordered_slots_nodup {p k d : Nat} {rows : List (PivotRow p k d)}
    (hordered : Ordered rows) : (rows.map PivotRow.slot).Nodup := by
  induction rows with
  | nil => simp
  | cons head tail ih =>
      rw [Ordered] at hordered
      cases hordered with
      | cons hhead htail =>
        rw [List.map_cons, List.nodup_cons]
        constructor
        · intro hmem
          rcases List.mem_map.mp hmem with ⟨pivot, hpivot, heq⟩
          have hlt := hhead pivot hpivot
          rw [heq] at hlt
          exact Slot.lt_irrefl _ hlt
        · exact ih htail

theorem laterPivot_higherAt {p k d : Nat} (head later : PivotRow p k d)
    (hlater : Slot.lt head.slot later.slot) :
    HigherAt p k head.slot.2 (later.row head.slot.1) := by
  rcases hlater with hcolumn | ⟨hcolumn, hlevel⟩
  · refine ⟨0, ?_⟩
    rw [later.zerosBefore head.slot.1 hcolumn]
    simp
  · have hcolumn' : later.slot.1 = head.slot.1 := hcolumn.symm
    have hpow : p ^ (later.slot.2 : Nat) =
        p ^ ((head.slot.2 : Nat) + 1) *
          p ^ ((later.slot.2 : Nat) - ((head.slot.2 : Nat) + 1)) :=
      pow_split (by omega)
    refine ⟨p ^ ((later.slot.2 : Nat) - ((head.slot.2 : Nat) + 1)), ?_⟩
    rw [← hcolumn', later.pivot, hpow]

/-- Every digit combination of rows strictly after `head` is higher-order at its pivot coordinate. -/
theorem tailRep_higherAt {p k d : Nat} (head : PivotRow p k d)
    {tail : List (PivotRow p k d)}
    (hlater : ∀ row ∈ tail, Slot.lt head.slot row.slot)
    {x : Vector p k d} (hx : DigitRep p (rowsOf tail) x) :
    HigherAt p k head.slot.2 (x head.slot.1) := by
  induction tail generalizing x with
  | nil =>
      have hx0 := hx.eq_zero_of_nil
      subst x
      exact ⟨0, by simp⟩
  | cons current rest ih =>
      cases hx with
      | cons digit hdigit hrest =>
        rename_i restValue
        have hcurrent := laterPivot_higherAt head current (hlater current (by simp))
        have hrestHigher := ih
          (fun row hrow => hlater row (by simp [hrow])) hrest
        rcases hcurrent with ⟨currentTail, hcurrent⟩
        rcases hrestHigher with ⟨restTail, hrest⟩
        refine ⟨digit * currentTail + restTail, ?_⟩
        change digit • current.row head.slot.1 + restValue head.slot.1 = _
        rw [hcurrent, hrest]
        push_cast
        ring

/-- A full vector has leading slot `(column, level)`. -/
structure HasLead {p k d : Nat} (x : Vector p k d) (slot : Slot d k) : Prop where
  zerosBefore : ∀ column : Fin d, column < slot.1 → x column = 0
  exactAt : ExactAt p k slot.2 (x slot.1)

theorem ExactAt.not_higherAt {p k v : Nat} (hp : 1 < p) (hv : v < k)
    {x : Ring p k} (hexact : ExactAt p k v x) (hhigher : HigherAt p k v x) : False := by
  rcases hexact with ⟨digit, hdpos, hdlt, exactTail, hexact⟩
  rcases hhigher with ⟨higherTail, hhigher⟩
  have heq : ((p ^ v * (digit + p * exactTail) : Nat) : Ring p k) =
      ((p ^ v * (0 + p * higherTail) : Nat) : Ring p k) := by
    rw [← hexact, hhigher]
    push_cast
    rw [pow_succ]
    ring
  have hdigitZero := digit_eq_of_zmod_eq hp hv hdlt (Nat.zero_lt_of_lt hp) heq
  omega

theorem ExactAt.higherAt_of_lt {p k v w : Nat} (hvw : v < w)
    {x : Ring p k} (hexact : ExactAt p k w x) : HigherAt p k v x := by
  rcases hexact with ⟨digit, hdpos, hdlt, tail, rfl⟩
  have hpow : p ^ w = p ^ (v + 1) * p ^ (w - (v + 1)) := pow_split (by omega)
  refine ⟨p ^ (w - (v + 1)) * (digit + p * tail), ?_⟩
  rw [hpow]
  push_cast
  ring

theorem higherAt_iff_ring_multiple {p k v : Nat} (hp : 1 < p) {x : Ring p k} :
    HigherAt p k v x ↔
      ∃ coefficient : Ring p k,
        x = ((p ^ (v + 1) : Nat) : Ring p k) * coefficient := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Nat.ne_of_gt (Nat.zero_lt_of_lt hp))⟩
  constructor
  · rintro ⟨tail, rfl⟩
    refine ⟨(tail : Ring p k), ?_⟩
    push_cast
    rfl
  · rintro ⟨coefficient, rfl⟩
    refine ⟨coefficient.val, ?_⟩
    push_cast
    rw [ZMod.natCast_zmod_val]

/-- Multiplying a higher-order coordinate by any scalar leaves it higher-order. -/
theorem HigherAt.mul_left {p k v : Nat} (hp : 1 < p)
    (coefficient : Ring p k) {x : Ring p k} (hx : HigherAt p k v x) :
    HigherAt p k v (coefficient * x) := by
  rcases (higherAt_iff_ring_multiple hp).1 hx with ⟨tail, htail⟩
  apply (higherAt_iff_ring_multiple hp).2
  refine ⟨coefficient * tail, ?_⟩
  rw [htail]
  ring

/-- Subtracting a higher-order coordinate preserves the exact visible digit. -/
theorem ExactAt.sub_higherAt {p k v : Nat} (hp : 1 < p)
    {x y : Ring p k} (hx : ExactAt p k v x) (hy : HigherAt p k v y) :
    ExactAt p k v (x - y) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Nat.ne_of_gt (Nat.zero_lt_of_lt hp))⟩
  rcases hx with ⟨digit, hdigitPos, hdigitLt, tail, hx⟩
  rcases (higherAt_iff_ring_multiple hp).1 hy with ⟨coefficient, hy⟩
  let newTail : Nat := ((tail : Ring p k) - coefficient).val
  refine ⟨digit, hdigitPos, hdigitLt, newTail, ?_⟩
  rw [hx, hy]
  have hnewTail : (newTail : Ring p k) = (tail : Ring p k) - coefficient := by
    exact ZMod.natCast_zmod_val _
  push_cast
  rw [hnewTail]
  rw [pow_succ]
  ring

/-- A larger exact p-level is higher-order relative to every smaller level. -/
theorem ExactAt.higherAt_of_level_lt {p k v w : Nat} (hvw : v < w)
    {x : Ring p k} (hx : ExactAt p k w x) : HigherAt p k v x :=
  hx.higherAt_of_lt hvw

theorem ExactAt.unique {p k v w : Nat} (hp : 1 < p) (hv : v < k) (hw : w < k)
    {x : Ring p k} (hx : ExactAt p k v x) (hy : ExactAt p k w x) : v = w := by
  rcases lt_trichotomy v w with hvw | rfl | hwv
  · exact False.elim (hx.not_higherAt hp hv (hy.higherAt_of_lt hvw))
  · rfl
  · exact False.elim (hy.not_higherAt hp hw (hx.higherAt_of_lt hwv))

/-- Every nonzero residue modulo `p^k` has a unique visible p-adic level below `k`. -/
theorem exists_exactAt {p k : Nat} (hp : 1 < p) {x : Ring p k} (hx : x ≠ 0) :
    ∃ level : Fin k, ExactAt p k level x := by
  have hmodPos : 0 < p ^ k := pow_pos (Nat.zero_lt_of_lt hp) k
  letI : NeZero (p ^ k) := ⟨Nat.ne_of_gt hmodPos⟩
  let value := x.val
  have hvalue : value ≠ 0 := (ZMod.val_eq_zero x).not.mpr hx
  let level := padicValNat p value
  let unitPart := Nat.divMaxPow value p
  have hfactor : p ^ level * unitPart = value := by
    exact Nat.pow_padicValNat_mul_divMaxPow p value
  have hunit : ¬p ∣ unitPart := Nat.not_dvd_divMaxPow hp hvalue
  have hlevel : level < k := by
    by_contra hnot
    have hklevel : k ≤ level := Nat.le_of_not_gt hnot
    have hdiv : p ^ k ∣ value :=
      (Nat.pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp) hvalue).2 hklevel
    have hle : p ^ k ≤ value := Nat.le_of_dvd (Nat.pos_of_ne_zero hvalue) hdiv
    exact (not_le_of_gt x.val_lt) hle
  let digit := unitPart % p
  let tail := unitPart / p
  have hdigitLt : digit < p := Nat.mod_lt _ (Nat.zero_lt_of_lt hp)
  have hdigitNe : digit ≠ 0 := by
    intro hzero
    apply hunit
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hzero
  refine ⟨⟨level, hlevel⟩, digit, Nat.pos_of_ne_zero hdigitNe, hdigitLt, tail, ?_⟩
  calc
    x = (value : Ring p k) := (ZMod.natCast_zmod_val x).symm
    _ = (p ^ level * unitPart : Nat) := by rw [hfactor]
    _ = (p ^ level * (digit + p * tail) : Nat) := by
      congr 2
      exact (Nat.mod_add_div unitPart p).symm

/-- A unit does not change the exact p-adic level of a coordinate. -/
theorem ExactAt.unit_mul {p k v : Nat} (hp : 1 < p) (hv : v < k)
    (unit : (Ring p k)ˣ) {x : Ring p k} (hx : ExactAt p k v x) :
    ExactAt p k v ((unit : Ring p k) * x) := by
  have hxne : x ≠ 0 := hx.ne_zero hp hv
  have hproductNe : (unit : Ring p k) * x ≠ 0 := by
    intro hzero
    apply hxne
    calc
      x = ((unit⁻¹ : (Ring p k)ˣ) : Ring p k) * ((unit : Ring p k) * x) := by simp
      _ = 0 := by rw [hzero, mul_zero]
  rcases exists_exactAt hp hproductNe with ⟨level, hlevel⟩
  have hlevelEq : (level : Nat) = v := by
    rcases lt_trichotomy (level : Nat) v with hlv | heq | hvl
    · have hxHigher : HigherAt p k level x := hx.higherAt_of_lt hlv
      have hproductHigher := hxHigher.mul_left hp (unit : Ring p k)
      exact False.elim (hlevel.not_higherAt hp level.isLt hproductHigher)
    · exact heq
    · have hproductHigher : HigherAt p k v ((unit : Ring p k) * x) :=
        hlevel.higherAt_of_lt hvl
      have hback := hproductHigher.mul_left hp ((unit⁻¹ : (Ring p k)ˣ) : Ring p k)
      have hxHigher : HigherAt p k v x := by
        simpa [mul_assoc] using hback
      exact False.elim (hx.not_higherAt hp hv hxHigher)
  simpa [hlevelEq] using hlevel

/-- Scaling a vector by a unit preserves its leading slot. -/
theorem HasLead.unit_smul {p k d : Nat} (hp : 1 < p)
    (unit : (Ring p k)ˣ) {x : Vector p k d} {slot : Slot d k}
    (hlead : HasLead x slot) :
    HasLead ((unit : Ring p k) • x) slot := by
  constructor
  · intro column hcolumn
    change (unit : Ring p k) * x column = 0
    rw [hlead.zerosBefore column hcolumn, mul_zero]
  · change ExactAt p k slot.2 ((unit : Ring p k) * x slot.1)
    exact hlead.exactAt.unit_mul hp slot.2.isLt unit

theorem HasLead.unique {p k d : Nat} (hp : 1 < p) {x : Vector p k d}
    {a b : Slot d k} (ha : HasLead x a) (hb : HasLead x b) : a = b := by
  have hcolumn : a.1 = b.1 := by
    rcases lt_trichotomy a.1 b.1 with hab | heq | hba
    · exact False.elim (ha.exactAt.ne_zero hp a.2.isLt (hb.zerosBefore a.1 hab))
    · exact heq
    · exact False.elim (hb.exactAt.ne_zero hp b.2.isLt (ha.zerosBefore b.1 hba))
  have hlevel : a.2 = b.2 := by
    apply Fin.ext
    apply ha.exactAt.unique hp a.2.isLt b.2.isLt
    simpa [hcolumn] using hb.exactAt
  exact Prod.ext hcolumn hlevel

/-- Subtracting a vector with a later lead preserves the earlier lead. -/
theorem HasLead.sub_of_lt {p k d : Nat} (hp : 1 < p)
    {x y : Vector p k d} {first second : Slot d k}
    (hx : HasLead x first) (hy : HasLead y second) (hlt : Slot.lt first second) :
    HasLead (x - y) first := by
  rcases hlt with hcolumn | ⟨hcolumn, hlevel⟩
  · constructor
    · intro column hbefore
      change x column - y column = 0
      rw [hx.zerosBefore column hbefore,
        hy.zerosBefore column (lt_trans hbefore hcolumn)]
      simp
    · change ExactAt p k first.2 (x first.1 - y first.1)
      rw [hy.zerosBefore first.1 hcolumn, sub_zero]
      exact hx.exactAt
  · constructor
    · intro column hbefore
      change x column - y column = 0
      have hyBefore : column < second.1 := by simpa [← hcolumn] using hbefore
      rw [hx.zerosBefore column hbefore, hy.zerosBefore column hyBefore]
      simp
    · change ExactAt p k first.2 (x first.1 - y first.1)
      have hyHigher : HigherAt p k first.2 (y first.1) := by
        apply ExactAt.higherAt_of_lt hlevel
        simpa [hcolumn] using hy.exactAt
      exact hx.exactAt.sub_higherAt hp hyHigher

theorem PivotRow.hasLead {p k d : Nat} (hp : 1 < p) (pivot : PivotRow p k d) :
    HasLead pivot.row pivot.slot := by
  constructor
  · exact pivot.zerosBefore
  · refine ⟨1, Nat.zero_lt_one, hp, 0, ?_⟩
    rw [pivot.pivot]
    congr 1
    omega

theorem HasLead.vector_ne_zero {p k d : Nat} (hp : 1 < p)
    {x : Vector p k d} {slot : Slot d k} (hlead : HasLead x slot) : x ≠ 0 := by
  intro hzero
  have hcoordinate : x slot.1 = 0 := by rw [hzero]; rfl
  exact hlead.exactAt.ne_zero hp slot.2.isLt hcoordinate

/-- Every nonzero vector has a concrete first nonzero column and p-adic level. -/
theorem exists_hasLead {p k d : Nat} (hp : 1 < p)
    {x : Vector p k d} (hx : x ≠ 0) : ∃ slot : Slot d k, HasLead x slot := by
  classical
  let support : Finset (Fin d) := Finset.univ.filter fun column => x column ≠ 0
  have hexists : ∃ column : Fin d, x column ≠ 0 := by
    by_contra hnot
    apply hx
    funext column
    by_contra hcolumn
    exact hnot ⟨column, hcolumn⟩
  have hsupport : support.Nonempty := by
    rcases hexists with ⟨column, hcolumn⟩
    exact ⟨column, by simp [support, hcolumn]⟩
  let column := support.min' hsupport
  have hcolumnMem : column ∈ support := Finset.min'_mem _ _
  have hcolumnNe : x column ≠ 0 := by simpa [support] using hcolumnMem
  rcases exists_exactAt hp hcolumnNe with ⟨level, hlevel⟩
  refine ⟨(column, level), ?_, hlevel⟩
  intro earlier hearlier
  by_contra hearlierNe
  have hearlierMem : earlier ∈ support := by simp [support, hearlierNe]
  have hmin : column ≤ earlier := Finset.min'_le _ _ hearlierMem
  exact (not_le_of_gt hearlier) hmin

/-- Unit normalization produces exactly the pivot record stored by the algorithm. -/
theorem exists_normalized_pivot {p k d : Nat} (hp : p.Prime)
    {x : Vector p k d} {slot : Slot d k} (hlead : HasLead x slot) :
    ∃ pivot : PivotRow p k d, pivot.slot = slot ∧
      ∃ unit : (Ring p k)ˣ, pivot.row = (unit : Ring p k) • x := by
  rcases hlead.exactAt with ⟨digit, hdigitPos, hdigitLt, tail, hx⟩
  let unitNat := digit + p * tail
  have hnotDvd : ¬p ∣ unitNat := by
    intro hdiv
    have hmodZero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    have hmod : unitNat % p = digit := by
      dsimp [unitNat]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hdigitLt]
    rw [hmod] at hmodZero
    omega
  have hcoprime : Nat.Coprime unitNat (p ^ k) := hp.coprime_pow_of_not_dvd hnotDvd
  have hisUnit : IsUnit ((unitNat : Nat) : Ring p k) :=
    (ZMod.isUnit_iff_coprime unitNat (p ^ k)).2 hcoprime
  rcases hisUnit with ⟨unit, hunit⟩
  let normalizedRow : Vector p k d := (↑(unit⁻¹) : Ring p k) • x
  let pivot : PivotRow p k d := {
    slot := slot
    row := normalizedRow
    zerosBefore := by
      intro column hcolumn
      change (↑(unit⁻¹) : Ring p k) * x column = 0
      rw [hlead.zerosBefore column hcolumn]
      simp
    pivot := by
      change (↑(unit⁻¹) : Ring p k) * x slot.1 =
        ((p ^ (slot.2 : Nat) : Nat) : Ring p k)
      rw [hx]
      have hunitCast : ((unitNat : Nat) : Ring p k) = (unit : Ring p k) := hunit.symm
      rw [Nat.cast_mul, hunitCast]
      calc
        (↑(unit⁻¹) : Ring p k) *
            (((p ^ (slot.2 : Nat) : Nat) : Ring p k) * (unit : Ring p k)) =
            (((p ^ (slot.2 : Nat) : Nat) : Ring p k) *
              ((↑(unit⁻¹) : Ring p k) * (unit : Ring p k))) := by ring
        _ = ((p ^ (slot.2 : Nat) : Nat) : Ring p k) := by simp
  }
  exact ⟨pivot, rfl, unit⁻¹, rfl⟩

/-- Later digit combinations vanish in every column before the head pivot. -/
theorem tailRep_zero_before {p k d : Nat} (head : PivotRow p k d)
    {tail : List (PivotRow p k d)}
    (hlater : ∀ row ∈ tail, Slot.lt head.slot row.slot)
    {x : Vector p k d} (hx : DigitRep p (rowsOf tail) x)
    (column : Fin d) (hcolumn : column < head.slot.1) : x column = 0 := by
  induction tail generalizing x with
  | nil =>
      have hx0 := hx.eq_zero_of_nil
      subst x
      simp
  | cons current rest ih =>
      cases hx with
      | cons digit hdigit hrest =>
        rename_i restValue
        have hslot := hlater current (by simp)
        have hcurrentColumn : column < current.slot.1 := by
          rcases hslot with hcol | ⟨hcol, hlevel⟩
          · exact lt_trans hcolumn hcol
          · simpa [hcol] using hcolumn
        have hcurrentZero := current.zerosBefore column hcurrentColumn
        have hrestZero := ih (fun row hrow => hlater row (by simp [hrow])) hrest
        change digit • current.row column + restValue column = 0
        rw [hcurrentZero, hrestZero]
        simp

/-- A nonzero head digit fixes the leading slot despite all later rows. -/
theorem cons_hasLead {p k d : Nat} (head : PivotRow p k d) {tail : List (PivotRow p k d)}
    (hlater : ∀ row ∈ tail, Slot.lt head.slot row.slot)
    {tailValue : Vector p k d} (tailRep : DigitRep p (rowsOf tail) tailValue)
    (digit : Nat) (hdigitPos : 0 < digit) (hdigitLt : digit < p) :
    HasLead (digit • head.row + tailValue) head.slot := by
  constructor
  · intro column hcolumn
    change digit • head.row column + tailValue column = 0
    rw [head.zerosBefore column hcolumn,
      tailRep_zero_before head hlater tailRep column hcolumn]
    simp
  · rcases tailRep_higherAt head hlater tailRep with ⟨tail, htail⟩
    refine ⟨digit, hdigitPos, hdigitLt, tail, ?_⟩
    change digit • head.row head.slot.1 + tailValue head.slot.1 = _
    rw [head.pivot, htail]
    push_cast
    rw [pow_succ]
    ring

/-- Every nonzero digit-represented row has the slot of an actual pivot as its lead. -/
theorem nonzero_digitRep_hasLead {p k d : Nat}
    {pivots : List (PivotRow p k d)} (ordered : Ordered pivots)
    {x : Vector p k d} (hx : DigitRep p (rowsOf pivots) x) (hne : x ≠ 0) :
    ∃ pivot ∈ pivots, HasLead x pivot.slot := by
  induction pivots generalizing x with
  | nil => exact False.elim (hne hx.eq_zero_of_nil)
  | cons head tail ih =>
      rw [Ordered] at ordered
      cases ordered with
      | cons hlater tailOrdered =>
        cases hx with
        | cons digit hdigit htail =>
          rename_i tailValue
          by_cases hzero : digit = 0
          · subst digit
            have htailNe : tailValue ≠ 0 := by simpa using hne
            rcases ih tailOrdered htail htailNe with ⟨pivot, hpivot, hlead⟩
            exact ⟨pivot, by simp [hpivot], by simpa using hlead⟩
          · have hpos := Nat.pos_of_ne_zero hzero
            exact ⟨head, by simp, cons_hasLead head hlater htail digit hpos hdigit⟩

end CompositeModulusBasis.PadicEchelon
