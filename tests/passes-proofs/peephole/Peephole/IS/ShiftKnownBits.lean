import IRLean.Int

/-! # `KnownBits::shl`, and the counts of known bits `simplifyShift` reads

`simplifyShift`'s last rewrite, `IS.simplifyShift.L1364`, asks `KnownBits::shl` from
`llvm/lib/Support/KnownBits.cpp:410-492` at `llvmorg-23.1.3` what a shift's known bits are, given its operands'. That's a
function on known bits, not an analysis of the IR, so the model has it here, as the C++ computes it, with the flags
`simplifyShift` passes: `NUW`, `NSW` and `ShAmtNonZero` all false. `KnownBits.shl_holds` says it's right: whatever value
and amount have the bits their known bits say, and the amount is in range, the shifted value has the bits the result
says.

The counts are `APInt::countr_one` and `APInt::countl_one`, which `KnownBits::countMinTrailingZeros` and
`countMinLeadingZeros` read, and `Log2_32_Ceil` from `llvm/include/llvm/Support/MathExtras.h`.

Widths here are any `Nat`. LLVM's fit in 24 bits, so its `unsigned` arithmetic on them, as in `isPowerOf2_32`, doesn't
wrap, and the model's `Nat` arithmetic is the same. -/

namespace Peephole.IS.Shift

variable {w : Nat}

/-! ### Counting bits -/

/-- How many of `p 0`, `p 1`, ..., `p (n - 1)` hold before the first that doesn't. -/
def countWhile (p : Nat → Bool) (n : Nat) : Nat := go 0
where
  go (i : Nat) : Nat := if i < n then (if p i then go (i + 1) else i) else i
  termination_by n - i

theorem countWhile.go_spec (p : Nat → Bool) (n : Nat) {k : Nat} :
    ∀ i, i ≤ k → k ≤ countWhile.go p n i → ∀ j, i ≤ j → j < k → p j = true := by
  intro i
  induction i using countWhile.go.induct p n with
  | case1 i hi hp ih =>
    intro hik hk j hij hjk
    rw [countWhile.go] at hk
    simp only [hi, hp, ↓reduceIte] at hk
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact hp
    · exact ih (by omega) hk j hlt hjk
  | case2 i hi hp =>
    intro hik hk j hij hjk
    rw [countWhile.go] at hk
    simp only [hi, hp, Bool.false_eq_true, ↓reduceIte] at hk
    omega
  | case3 i hi =>
    intro hik hk j hij hjk
    rw [countWhile.go] at hk
    simp only [hi, ↓reduceIte] at hk
    omega

/-- If at least `k` hold before the first that doesn't, each of the first `k` holds. -/
theorem countWhile_spec {p : Nat → Bool} {n k : Nat} (h : k ≤ countWhile p n) : ∀ j, j < k → p j = true :=
  fun j hj => countWhile.go_spec p n 0 (Nat.zero_le _) h j (Nat.zero_le _) hj

/-- `APInt::countr_one()`: how many of the low bits are 1, from bit 0 up. -/
def countTrailingOnes (z : BitVec w) : Nat := countWhile z.getLsbD w

/-- `APInt::countl_one()`: how many of the high bits are 1, from the sign bit down. -/
def countLeadingOnes (z : BitVec w) : Nat := countWhile z.getMsbD w

/-- `Log2_32_Ceil(n)`: the least `k` with `n ≤ 2 ^ k`, and 32 at 0, which no type's width is. -/
def log2Ceil (n : Nat) : Nat := if n = 0 then 32 else if n = 1 then 0 else (n - 1).log2 + 1

theorem le_two_pow_log2Ceil {n : Nat} (hn : n ≠ 0) : n ≤ 2 ^ log2Ceil n := by
  unfold log2Ceil
  simp only [hn, ↓reduceIte]
  split
  · omega
  · have := Nat.lt_log2_self (n := n - 1)
    omega

/-! ### Known bits -/

/-- `KnownBits`: the bits known to be 0, and those known to be 1. -/
structure KnownBits (w : Nat) where
  zero : BitVec w
  one : BitVec w

namespace KnownBits

/-- `x` has every bit `k` says it has, as `Oracle.Sound` says of `computeKnownBits`. -/
def Holds (k : KnownBits w) (x : BitVec w) : Prop := x &&& k.zero = 0#w ∧ x &&& k.one = k.one

/-- `hasConflict()`: some bit known to be both 0 and 1. -/
def hasConflict (k : KnownBits w) : Bool := k.zero &&& k.one != 0#w

/-- `isUnknown()`: nothing known. -/
def isUnknown (k : KnownBits w) : Bool := k.zero == 0#w && k.one == 0#w

/-- `intersectWith(RHS)`: what both know. -/
def intersectWith (a b : KnownBits w) : KnownBits w := ⟨a.zero &&& b.zero, a.one &&& b.one⟩

/-- `APInt::getLowBitsSet(w, n)`, and what `setLowBits(n)` sets: bits 0 to `n - 1`. -/
def lowBits (w n : Nat) : BitVec w := BitVec.ofNat w (2 ^ n - 1)

/-- `isPowerOf2_32(n)`: exactly one bit set. -/
def isPowerOf2 (n : Nat) : Bool := n != 0 && (n &&& (n - 1)) == 0

/-- `getMaxShiftAmount(MaxValue, BitWidth)`, the helper before `KnownBits::shl`: the low `Log2_32(BitWidth)` bits of
`MaxValue` if the width is a power of two, and `MaxValue` capped at `BitWidth - 1` if not. -/
def maxShiftAmount (maxValue : BitVec w) : Nat :=
  if isPowerOf2 w then maxValue.toNat % 2 ^ min w.log2 w else min maxValue.toNat (w - 1)

/-- `ShiftByConst(LHS, ShiftAmt)`, the lambda in `KnownBits::shl`, with `NSW` false: `ushl_ov` is a shift left, which
gives 0 past the width, as `<<<` does. -/
def shiftByConst (l : KnownBits w) (s : Nat) : KnownBits w := ⟨l.zero <<< s ||| lowBits w s, l.one <<< s⟩

/-- `KnownBits::shl`'s loop over the shift amounts from `s`, `n` of them: skip an amount the known bits of the amount
rule out, else intersect with the shift by it, and stop once nothing is known. -/
def shlLoop (l : KnownBits w) (zeroMask oneMask : Nat) : Nat → Nat → KnownBits w → KnownBits w
  | _, 0, k => k
  | s, n + 1, k =>
    if zeroMask &&& s != 0 || (oneMask ||| s) != s then shlLoop l zeroMask oneMask (s + 1) n k
    else
      let k' := k.intersectWith (shiftByConst l s)
      if k'.isUnknown then k' else shlLoop l zeroMask oneMask (s + 1) n k'

/-- `KnownBits::shl(LHS, RHS)`, with `NUW`, `NSW` and `ShAmtNonZero` false, as `simplifyShift` calls it:

- the least amount is `RHS.getMinValue().getLimitedValue(BitWidth)`, the known ones capped at the width;
- if nothing is known of `LHS`, only the low bits the least amount shifts in are known, to be 0;
- if the amount can be anything from 0 to `BitWidth - 1`, and the width is a power of two, the trailing zeros of `LHS`
  stay, and the sign bit is 1 if `LHS` is all ones;
- else each amount from the least to `getMaxShiftAmount` that the amount's known bits allow, as `unsigned` masks of the
  low 32 bits, contributes what's known of the shift by it, and if none does, the result is 0. -/
def shl (l r : KnownBits w) : KnownBits w :=
  let minAmt := min r.one.toNat w
  if l.isUnknown then ⟨lowBits w minAmt, 0#w⟩
  else
    let maxAmt := maxShiftAmount (~~~r.zero)
    if minAmt = 0 ∧ maxAmt = w - 1 ∧ isPowerOf2 w = true then
      ⟨lowBits w (countTrailingOnes l.zero), if l.one == BitVec.allOnes w then BitVec.intMin w else 0#w⟩
    else
      let k := shlLoop l (r.zero.toNat % 2 ^ 32) (r.one.toNat % 2 ^ 32) minAmt (maxAmt + 1 - minAmt)
        ⟨BitVec.allOnes w, BitVec.allOnes w⟩
      if k.hasConflict then ⟨BitVec.allOnes w, 0#w⟩ else k

/-! ### Why `shl` is right -/

theorem holds_intersect_left {a b : KnownBits w} {v : BitVec w} (h : a.Holds v) : (a.intersectWith b).Holds v := by
  obtain ⟨h0, h1⟩ := h
  constructor
  · simp only [intersectWith]; rw [← BitVec.and_assoc, h0, BitVec.zero_and]
  · simp only [intersectWith]; rw [← BitVec.and_assoc, h1]

theorem holds_intersect_right {a b : KnownBits w} {v : BitVec w} (h : b.Holds v) : (a.intersectWith b).Holds v := by
  obtain ⟨h0, h1⟩ := h
  constructor
  · simp only [intersectWith]
    rw [BitVec.and_comm a.zero, ← BitVec.and_assoc, h0, BitVec.zero_and]
  · simp only [intersectWith]
    rw [BitVec.and_comm a.one, ← BitVec.and_assoc, h1]

theorem holds_of_isUnknown {k : KnownBits w} (h : k.isUnknown = true) (v : BitVec w) : k.Holds v := by
  simp only [isUnknown, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h0, h1⟩ := h
  simp [Holds, h0, h1]

/-- A value that has the bits `k` says has no bit known both ways in `k`. -/
theorem hasConflict_eq_false {k : KnownBits w} {v : BitVec w} (h : k.Holds v) : k.hasConflict = false := by
  obtain ⟨h0, h1⟩ := h
  have : k.zero &&& k.one = 0#w :=
    calc k.zero &&& k.one = k.zero &&& (v &&& k.one) := by rw [h1]
      _ = (v &&& k.zero) &&& k.one := by rw [← BitVec.and_assoc, BitVec.and_comm k.zero v]
      _ = 0#w := by rw [h0, BitVec.zero_and]
  simp [hasConflict, this]

theorem getLsbD_lowBits (n i : Nat) : (lowBits w n).getLsbD i = (decide (i < w) && decide (i < n)) := by
  simp [lowBits, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]

/-- A value whose low `n` bits are 0 has none of `lowBits w n`. -/
theorem and_lowBits {v : BitVec w} {n : Nat} (h : ∀ i, i < n → v.getLsbD i = false) : v &&& lowBits w n = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, getLsbD_lowBits]
  by_cases hn : i < n
  · simp [h i hn]
  · simp [hn]

theorem getLsbD_shiftLeft_of_lt {x : BitVec w} {s i : Nat} (h : i < s) : (x <<< s).getLsbD i = false := by
  simp [BitVec.getLsbD_shiftLeft, h]

theorem holds_shiftByConst {l : KnownBits w} {x : BitVec w} (h : l.Holds x) (s : Nat) :
    (shiftByConst l s).Holds (x <<< s) := by
  obtain ⟨h0, h1⟩ := h
  constructor
  · simp only [shiftByConst]
    rw [BitVec.and_or_distrib_left, ← BitVec.shiftLeft_and_distrib, h0, BitVec.zero_shiftLeft, BitVec.zero_or]
    exact and_lowBits fun i hi => getLsbD_shiftLeft_of_lt hi
  · simp only [shiftByConst]
    rw [← BitVec.shiftLeft_and_distrib, h1]

theorem shlLoop_mono (l : KnownBits w) (zm om : Nat) {v : BitVec w} :
    ∀ (s n : Nat) (k : KnownBits w), k.Holds v → (shlLoop l zm om s n k).Holds v := by
  intro s n
  induction n generalizing s with
  | zero => intro k h; exact h
  | succ n ih =>
    intro k h
    simp only [shlLoop]
    split
    · exact ih _ _ h
    · split
      · exact holds_intersect_left h
      · exact ih _ _ (holds_intersect_left h)

/-- The loop keeps what the shift by each amount it doesn't skip says. -/
theorem shlLoop_holds {l : KnownBits w} {zm om : Nat} {x : BitVec w} (hx : l.Holds x) {y : Nat}
    (hy : (zm &&& y != 0 || (om ||| y) != y) = false) :
    ∀ (s n : Nat) (k : KnownBits w), s ≤ y → y < s + n → (shlLoop l zm om s n k).Holds (x <<< y) := by
  intro s n
  induction n generalizing s with
  | zero => intro k h1 h2; omega
  | succ n ih =>
    intro k h1 h2
    simp only [shlLoop]
    split
    · next hs =>
      have : s ≠ y := by rintro rfl; rw [hy] at hs; cases hs
      exact ih (s + 1) k (by omega) (by omega)
    · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · have hk : (k.intersectWith (shiftByConst l s)).Holds (x <<< s) :=
          holds_intersect_right (holds_shiftByConst hx s)
        split
        · exact hk
        · exact shlLoop_mono l zm om _ _ _ hk
      · split
        · next hu => exact holds_of_isUnknown hu _
        · exact ih (s + 1) _ (by omega) (by omega)

theorem toNat_le_of_and_eq {x m : BitVec w} (h : x &&& m = m) : m.toNat ≤ x.toNat := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_and] at this
  rw [← this]
  exact Nat.and_le_left

/-- The bits of `x` not in `z`, if `x` and `z` share none. -/
theorem toNat_and_not {x z : BitVec w} (h : x &&& z = 0#w) : x.toNat &&& (~~~z).toNat = x.toNat := by
  rw [← BitVec.toNat_and]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (·.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases hx : x.getLsbD i <;> simp_all

theorem mod_le_mod_of_and_eq {a b k : Nat} (h : a &&& b = a) : a % 2 ^ k ≤ b % 2 ^ k := by
  have : a % 2 ^ k = (a % 2 ^ k) &&& (b % 2 ^ k) := by
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (Nat.testBit · i) h
    simp only [Nat.testBit_and] at this
    simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
    cases hi : decide (i < k) <;> cases ha : a.testBit i <;> simp_all
  rw [this]
  exact Nat.and_le_right

/-- `isPowerOf2_32(n)` means `n` is `2 ^ Log2_32(n)`. -/
theorem eq_two_pow_log2 {n : Nat} (h : isPowerOf2 n = true) : n = 2 ^ n.log2 := by
  simp only [isPowerOf2, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨hn, hand⟩ := h
  have lo := Nat.log2_self_le hn
  have hi := Nat.lt_log2_self (n := n)
  apply Nat.le_antisymm _ lo
  false_or_by_contra
  -- `n = 2 ^ k + r` with `0 < r < 2 ^ k`: bit `k` is set in both `n` and `n - 1`.
  rename_i hgt
  have hk : ∀ m, 2 ^ n.log2 ≤ m → m < 2 ^ (n.log2 + 1) → m.testBit n.log2 = true := by
    intro m h1 h2
    have e : m = 2 ^ n.log2 + (m - 2 ^ n.log2) := by omega
    rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by rw [Nat.pow_succ] at h2; omega)]
    rfl
  have := congrArg (Nat.testBit · n.log2) hand
  simp only [Nat.testBit_and, hk n lo hi, hk (n - 1) (by omega) (by omega), Bool.true_and, Nat.zero_testBit] at this
  cases this

/-- An amount in range, with the bits its known bits say, is at most `getMaxShiftAmount` of its known zeros'
complement. -/
theorem le_maxShiftAmount {y z : BitVec w} (h : y &&& z = 0#w) (hy : y.toNat < w) :
    y.toNat ≤ maxShiftAmount (~~~z) := by
  have hsub := toNat_and_not h
  unfold maxShiftAmount
  split
  · next hp =>
    have hw := eq_two_pow_log2 hp
    have hmin : min w.log2 w = w.log2 := Nat.min_eq_left (by have := Nat.lt_two_pow_self (n := w.log2); omega)
    rw [hmin]
    have := mod_le_mod_of_and_eq (k := w.log2) hsub
    rwa [Nat.mod_eq_of_lt (by omega)] at this
  · have : y.toNat ≤ (~~~z).toNat := by rw [← hsub]; exact Nat.and_le_right
    omega

theorem and_mod_eq_zero {y z : BitVec w} (h : y &&& z = 0#w) (k : Nat) : (z.toNat % 2 ^ k) &&& y.toNat = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (·.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, BitVec.testBit_toNat, Nat.zero_testBit]
  cases hy : y.getLsbD i <;> simp_all

theorem or_mod_eq {y o : BitVec w} (h : y &&& o = o) (k : Nat) : (o.toNat % 2 ^ k) ||| y.toNat = y.toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (·.getLsbD i) h
  simp only [BitVec.getLsbD_and] at this
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, BitVec.testBit_toNat]
  cases hy : y.getLsbD i <;> simp_all

/-- `KnownBits::shl` is right: if `x` and `y` have the bits `l` and `r` say, and `y` is in range, `x <<< y` has the bits
`shl l r` says. -/
theorem shl_holds {l r : KnownBits w} {x y : BitVec w} (hx : l.Holds x) (hy : r.Holds y) (hyw : y.toNat < w) :
    (shl l r).Holds (x <<< y.toNat) := by
  have hmin : min r.one.toNat w ≤ y.toNat := Nat.le_trans (Nat.min_le_left _ _) (toNat_le_of_and_eq hy.2)
  unfold shl
  simp only
  split
  · -- Nothing known of `LHS`.
    constructor
    · exact and_lowBits fun i hi => getLsbD_shiftLeft_of_lt (by omega)
    · exact BitVec.and_zero
  · split
    · -- The fast path: any amount, at a width that's a power of two.
      constructor
      · apply and_lowBits
        intro i hi
        rw [BitVec.getLsbD_shiftLeft]
        by_cases his : i < y.toNat
        · simp [his]
        · have hz := countWhile_spec hi (i - y.toNat) (by omega)
          have := congrArg (·.getLsbD (i - y.toNat)) hx.1
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
          simp_all
      · split
        · next ha =>
          simp only [beq_iff_eq] at ha
          have hxa : x = BitVec.allOnes w := by rw [← BitVec.and_allOnes (x := x), ← ha]; exact hx.2
          subst hxa
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, BitVec.getLsbD_intMin]
          by_cases h : i + 1 = w
          · simp [h]; omega
          · simp [h]
        · exact BitVec.and_zero
    · -- The loop.
      have hmax := le_maxShiftAmount hy.1 hyw
      have hf : ((r.zero.toNat % 2 ^ 32) &&& y.toNat != 0 || ((r.one.toNat % 2 ^ 32) ||| y.toNat) != y.toNat) =
          false := by
        rw [and_mod_eq_zero hy.1, or_mod_eq hy.2]
        simp
      have hk := shlLoop_holds hx hf (min r.one.toNat w)
        (maxShiftAmount (~~~r.zero) + 1 - min r.one.toNat w) ⟨BitVec.allOnes w, BitVec.allOnes w⟩ hmin (by omega)
      rw [hasConflict_eq_false hk]
      exact hk

end KnownBits

end Peephole.IS.Shift
