import IRLean.Int

/-! # Facts about bitvectors at every width, for the rewrites

What `IRLean.Generic.Arith` and `IRLean.Generic.Bitwise` need about `BitVec w` for a variable `w`, which `bv_decide`
can't check: when a shift left by `k` can be undone, and how the overflow checks of `mul` and `add` read as one. -/

namespace IRLean.Generic

variable {w : Nat}

/-- A shift amount is in range when it's less than the width. -/
theorem shiftOk_iff (y : BitVec w) : Val.shiftOk y = decide (y.toNat < w) := by
  have h : (BitVec.ofNat w w).toNat = w := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt Nat.lt_two_pow_self
  simp [Val.shiftOk, BitVec.lt_def, h]

theorem toNat_ofNat_of_lt {k : Nat} (hk : k < w) : (BitVec.ofNat w k).toNat = k := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_trans hk Nat.lt_two_pow_self)

/-- A shift left by `k` and back loses nothing exactly when the value times `2 ^ k` fits: `shl nuw`'s rule. -/
theorem shl_lshr_eq_iff (x : BitVec w) {k : Nat} (hk : k ≤ w) :
    (x <<< k) >>> k = x ↔ x.toNat * 2 ^ k < 2 ^ w := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have hw : 2 ^ w = 2 ^ k * 2 ^ (w - k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hw, Nat.mod_mul_right_div_self, Nat.mul_div_cancel _ (Nat.two_pow_pos k),
    Nat.mod_eq_iff_lt (Nat.ne_of_gt (Nat.two_pow_pos _)), Nat.mul_comm (2 ^ k),
    Nat.mul_lt_mul_right (Nat.two_pow_pos k)]

/-- A shift left by `k` and arithmetically back loses nothing exactly when the signed value times `2 ^ k` fits:
`shl nsw`'s rule. -/
theorem shl_sshr_eq_iff (x : BitVec w) {k : Nat} (hk : k < w) :
    (x <<< k).sshiftRight k = x ↔ -2 ^ (w - 1) ≤ x.toInt * 2 ^ k ∧ x.toInt * 2 ^ k < 2 ^ (w - 1) := by
  rw [← BitVec.toInt_inj, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  have hN : (2 : Int) ^ w = 2 ^ k * 2 ^ (w - k) := by rw [← Int.pow_add]; congr 1; omega
  have hH : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Int.pow_succ']; congr 1; omega
  have hP : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  have hQ : (0 : Int) < 2 ^ (w - k) := Int.pow_pos (by decide)
  -- The shifted value is `x * 2 ^ k` wrapped into range, so the two differ by a multiple of `2 ^ w`.
  have hr := BitVec.toInt_shiftLeft (x := x) (n := k)
  have hx := BitVec.toInt_eq_toNat_bmod x
  have pos : 0 < 2 ^ w := Nat.two_pow_pos w
  obtain ⟨-, -, d1⟩ := (Int.bmod_eq_iff pos).1 hr.symm
  obtain ⟨-, -, d2⟩ := (Int.bmod_eq_iff pos).1 hx.symm
  have lo := BitVec.le_toInt (x <<< k)
  have hi := BitVec.toInt_lt (x := x <<< k)
  generalize (x <<< k).toInt = r at *
  rw [Nat.shiftLeft_eq] at d1
  push_cast at d1 d2
  obtain ⟨j, hj⟩ : (2 : Int) ^ w ∣ r - x.toInt * 2 ^ k := by
    have : r - x.toInt * 2 ^ k = (r - x.toNat * 2 ^ k) - (x.toInt - x.toNat) * 2 ^ k := by
      rw [Int.sub_mul]; omega
    rw [this]
    exact Int.dvd_sub d1 (Int.dvd_mul_of_dvd_left d2)
  have hrj : r = 2 ^ k * (x.toInt + 2 ^ (w - k) * j) := by
    rw [Int.mul_add, ← Int.mul_assoc, ← hN]
    rw [Int.mul_comm (2 ^ k) x.toInt]; omega
  push_cast
  rw [hrj, Int.mul_ediv_cancel_left _ (Int.ne_of_gt hP)]
  constructor
  · intro h
    have hj0 : 2 ^ (w - k) * j = 0 := by omega
    have : j = 0 := by
      rcases Int.mul_eq_zero.1 hj0 with h | h
      · omega
      · exact h
    subst this
    simp only [Int.mul_zero, Int.add_zero] at hrj
    rw [Int.mul_comm] at hrj
    rw [← hrj]; exact ⟨lo, hi⟩
  · rintro ⟨l, u⟩
    have : j = 0 := by
      rcases Int.lt_trichotomy j 0 with h | h | h
      · have : 2 ^ w * j ≤ 2 ^ w * (-1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        omega
      · exact h
      · have : 2 ^ w * 1 ≤ 2 ^ w * j := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        omega
    subst this
    simp

/-- `mul nuw` by `2 ^ k` overflows exactly when `shl nuw` by `k` does. -/
theorem umulOverflow_twoPow (x : BitVec w) {k : Nat} (hk : k < w) :
    x.umulOverflow (BitVec.twoPow w k) = !decide ((x <<< k) >>> k = x) := by
  have e := shl_lshr_eq_iff x (Nat.le_of_lt hk)
  rw [BitVec.umulOverflow, BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)]
  by_cases h : x.toNat * 2 ^ k < 2 ^ w
  · simp [e.2 h, Nat.not_le.2 h]
  · simp [mt e.1 h, Nat.le_of_not_lt h]

/-- `mul nsw` by `2 ^ k` overflows exactly when `shl nsw` by `k` does, while `2 ^ k` is positive as a signed value:
when `k + 1 < w`. At `k + 1 = w` it's the minimum, and the two differ. -/
theorem smulOverflow_twoPow (x : BitVec w) {k : Nat} (hk : k + 1 < w) :
    x.smulOverflow (BitVec.twoPow w k) = !decide ((x <<< k).sshiftRight k = x) := by
  have e := shl_sshr_eq_iff x (k := k) (by omega)
  rw [BitVec.smulOverflow, BitVec.toInt_twoPow]
  simp only [show ¬ w ≤ k by omega, show k + 1 ≠ w by omega, ite_false]
  push_cast
  by_cases h : -2 ^ (w - 1) ≤ x.toInt * 2 ^ k ∧ x.toInt * 2 ^ k < 2 ^ (w - 1)
  · simp only [e.2 h, decide_true, Bool.not_true, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  · simp only [mt e.1 h, decide_false, Bool.not_false, Bool.or_eq_true, decide_eq_true_eq]; omega

/-- Disjoint values add without carrying, so `add` can't overflow, signed or unsigned, and the sum is their `or`. -/
theorem add_of_and_eq_zero {x y : BitVec w} (h : x &&& y = 0#w) :
    x.uaddOverflow y = false ∧ x.saddOverflow y = false ∧ x + y = x ||| y := by
  have hsum := BitVec.add_eq_or_of_and_eq_zero x y h
  have hnat := BitVec.toNat_add_of_and_eq_zero h
  have hlt := (x + y).isLt
  have hmsb : (x.msb && y.msb) = false := by
    have := congrArg BitVec.msb h
    simpa [BitVec.msb_and] using this
  have hint : (x + y).toInt = x.toInt + y.toInt := by
    rw [BitVec.toInt_eq_msb_cond (x + y), BitVec.toInt_eq_msb_cond x, BitVec.toInt_eq_msb_cond y, hsum,
      BitVec.msb_or, ← hsum, hnat]
    cases hx : x.msb <;> cases hy : y.msb <;> simp_all <;> omega
  have lo := BitVec.le_toInt (x + y)
  have hi := BitVec.toInt_lt (x := x + y)
  refine ⟨?_, ?_, hsum⟩
  · simp only [BitVec.uaddOverflow, decide_eq_false_iff_not]; omega
  · simp only [BitVec.saddOverflow, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-- Shifting left and back logically keeps the low bits: masking with the all-ones value shifted right. -/
theorem shl_lshr_eq_and (x : BitVec w) (n : Nat) : (x <<< n) >>> n = x &&& (BitVec.allOnes w >>> n) := by
  ext i hi
  simp only [BitVec.getElem_ushiftRight, BitVec.getElem_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes]
  by_cases h : n + i < w <;> simp [h, hi] <;> omega

/-- A value shifted left by `n` ends in `n` zeros, so shifting it right and back gives it again. -/
theorem shl_lshr_shl (x : BitVec w) (n : Nat) : ((x <<< n) >>> n) <<< n = x <<< n := by
  rw [BitVec.shiftLeft_ushiftRight, BitVec.and_comm, BitVec.allOnes_shiftLeft_and_shiftLeft]

end IRLean.Generic
