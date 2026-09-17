import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The p-adic digit visible in one echelon slot

The key fact is cancellation in a congruence modulo `p^k`: after factoring
`p^v`, with `v < k`, equality still exposes the coefficient modulo `p`.
Coefficients in `[0,p)` are therefore equal.  This is the arithmetic core of
both uniqueness of p-digit expansions and missing-slot rejection.
-/

namespace CompositeModulusBasis.PadicArithmetic

theorem pow_split {p v k : Nat} (hv : v ≤ k) :
    p ^ k = p ^ v * p ^ (k - v) := by
  conv_lhs => rw [← Nat.add_sub_of_le hv]
  rw [pow_add]

theorem prime_dvd_remaining_pow {p v k : Nat} (hv : v < k) :
    p ∣ p ^ (k - v) := by
  exact dvd_pow_self p (by omega)

/-- Cancel `p^v` and read the surviving base-`p` digit. -/
theorem digit_eq_of_scaled_modEq {p k v a b leftTail rightTail : Nat}
    (hp : 1 < p) (hv : v < k) (ha : a < p) (hb : b < p)
    (hcongr : p ^ v * (a + p * leftTail) ≡
      p ^ v * (b + p * rightTail) [MOD p ^ k]) : a = b := by
  have hp0 : p ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hp)
  have hpv0 : p ^ v ≠ 0 := pow_ne_zero _ hp0
  have hsplit := pow_split (p := p) (v := v) (k := k) (Nat.le_of_lt hv)
  have hcancel : a + p * leftTail ≡ b + p * rightTail [MOD p ^ (k - v)] := by
    apply Nat.ModEq.mul_left_cancel' hpv0
    simpa [hsplit] using hcongr
  have hmodp : a + p * leftTail ≡ b + p * rightTail [MOD p] :=
    hcancel.of_dvd (prime_dvd_remaining_pow hv)
  change (a + p * leftTail) % p = (b + p * rightTail) % p at hmodp
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hmodp

/-- The same cancellation theorem phrased as equality in `ZMod (p^k)`. -/
theorem digit_eq_of_zmod_eq {p k v a b leftTail rightTail : Nat}
    (hp : 1 < p) (hv : v < k) (ha : a < p) (hb : b < p)
    (heq : ((p ^ v * (a + p * leftTail) : Nat) : ZMod (p ^ k)) =
      ((p ^ v * (b + p * rightTail) : Nat) : ZMod (p ^ k))) : a = b := by
  apply digit_eq_of_scaled_modEq hp hv ha hb
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp heq

/-- A nonzero digit times `p^v`, plus arbitrary higher-order terms, is nonzero mod `p^k`. -/
theorem digit_head_ne_zero {p k v digit tail : Nat}
    (hp : 1 < p) (hv : v < k) (hdigit_pos : 0 < digit) (hdigit_lt : digit < p) :
    ((p ^ v * (digit + p * tail) : Nat) : ZMod (p ^ k)) ≠ 0 := by
  intro hzero
  have heq : ((p ^ v * (digit + p * tail) : Nat) : ZMod (p ^ k)) =
      ((p ^ v * (0 + p * 0) : Nat) : ZMod (p ^ k)) := by simpa using hzero
  have := digit_eq_of_zmod_eq hp hv hdigit_lt (Nat.zero_lt_of_lt hp) heq
  omega

end CompositeModulusBasis.PadicArithmetic
