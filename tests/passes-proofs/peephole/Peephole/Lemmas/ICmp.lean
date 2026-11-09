import IRLean.Int
import IRLean.Refine

/-! # Facts about comparisons, at every width, that InstSimplify's `icmp` rewrites rest on

Each is about bit vectors, not about LLVM's code: a candidate for the lemma store, which any proof about an `icmp`
can use. The rewrite each one was cut from is named in its docstring. Comparisons are `BitVec`'s own: `ult`, `ule`,
`slt` and `sle`, which `IRLean.Val.icmp` reads, with `>` written by swapping the operands.

For each hypothesis of each lemma, `LemmaStore.Counter.<lemma>.drop_<hypothesis>`, at the end, gives one input where
the lemma without it is false, and `LemmaStore.Counter.<lemma>.sat` one where its hypotheses all hold. -/

namespace Peephole.Lemmas

open IRLean

variable {v w : Nat}

/-! ### A bit vector's signed value, as linear facts about its `toNat` -/

/-- `x.toInt` is `x.toNat` below half the range, and `x.toNat - 2 ^ w` from there. -/
theorem toInt_toNat_cases (x : BitVec w) :
    (2 * x.toNat < 2 ^ w ∧ x.toInt = x.toNat) ∨
      (2 ^ w ≤ 2 * x.toNat ∧ x.toInt = (x.toNat : Int) - ((2 ^ w : Nat) : Int)) := by
  rw [BitVec.toInt_eq_msb_cond]
  cases h : x.msb
  · refine Or.inl ⟨BitVec.msb_eq_false_iff_two_mul_lt.1 h, ?_⟩
    simp only [Bool.false_eq_true, ite_false]
  · refine Or.inr ⟨?_, ?_⟩
    · exact BitVec.msb_eq_true_iff_two_mul_ge.1 h
    · simp only [ite_true]

theorem msb_iff (x : BitVec w) : x.msb = true ↔ 2 ^ w ≤ 2 * x.toNat :=
  BitVec.msb_eq_true_iff_two_mul_ge

/-- `2 ^ w` is twice `2 ^ (w - 1)` at a positive width, and two values at one width differ by less than it. -/
theorem two_pow_pred (hw : 0 < w) : 2 ^ w = 2 * 2 ^ (w - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega

theorem two_pow_le (h : v ≤ w) : 2 ^ v ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) h

theorem two_pow_lt (h : v < w) : 2 * 2 ^ v ≤ 2 ^ w := by
  rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by omega) h

/-! ### `zext x` and `sext x` of one value. `IS.simplifyICmpInst.L3959`, `L3961`, `L4038` and `L4040` -/

theorem toNat_signExtend_cases (x : BitVec v) (w : Nat) :
    (x.msb = false ∧ (x.signExtend w).toNat = x.toNat % 2 ^ w) ∨
      (x.msb = true ∧ (x.signExtend w).toNat = x.toNat % 2 ^ w + (2 ^ w - 2 ^ v)) := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  cases x.msb <;> simp

/-- `zext x ≤u sext x`: sign extension only adds ones. -/
theorem setWidth_ule_signExtend (x : BitVec v) (w : Nat) : (x.setWidth w).ule (x.signExtend w) = true := by
  simp only [BitVec.ule_eq_decide, BitVec.toNat_setWidth, decide_eq_true_eq]
  rcases toNat_signExtend_cases x w with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

/-- `sext x ≤s zext x`: they're equal, unless `x` is negative and widened, when only `sext x` is negative. -/
theorem signExtend_sle_setWidth (x : BitVec v) (w : Nat) : (x.signExtend w).sle (x.setWidth w) = true := by
  by_cases hvw : w ≤ v
  · rw [BitVec.signExtend_eq_setWidth_of_le x hvw]
    simp [BitVec.sle_eq_decide]
  · cases hm : x.msb
    · rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
      simp [BitVec.sle_eq_decide]
    · simp only [BitVec.sle_eq_decide, decide_eq_true_eq]
      have hs : (x.signExtend w).toNat = x.toNat + (2 ^ w - 2 ^ v) := by
        rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, hm,
          Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by omega))]
        simp
      have hz : (x.setWidth w).toNat = x.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by omega))]
      have hx := (msb_iff x).1 hm
      have hlt := two_pow_lt (show v < w by omega)
      have := x.isLt
      have hv : 0 < v := by
        cases v
        · simp at hx; have : (2 : Nat) ^ 0 = 1 := rfl; omega
        · omega
      rcases toInt_toNat_cases (x.signExtend w) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases toInt_toNat_cases (x.setWidth w) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      · rw [h2, h4]; omega

/-! ### `zext x` against a constant that isn't one. `IS.simplifyICmpInst.L4000` to `L4016` -/

/-- A constant that truncating to `v` bits and zero-extending back changes has a bit set at `v` or above. -/
theorem le_toNat_of_setWidth_ne {c : BitVec w} (h : (c.setWidth v).setWidth w ≠ c) : 2 ^ v ≤ c.toNat := by
  refine Nat.le_of_not_lt fun hlt => h (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt c.isLt]

/-- `zext x <u c`, where `c` isn't a zero extension from `x`'s width. -/
theorem setWidth_ult_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).setWidth w ≠ c) :
    (x.setWidth w).ult c = true := by
  have hc := le_toNat_of_setWidth_ne h
  have := x.isLt
  have := Nat.mod_le x.toNat (2 ^ w)
  simp only [BitVec.ult_eq_decide, BitVec.toNat_setWidth, decide_eq_true_eq]
  omega

/-- What a signed comparison of `zext x` with such a `c` says: `zext x` is non-negative, and below `c` unless `c`
is negative. -/
theorem setWidth_signed_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).setWidth w ≠ c) :
    (x.setWidth w).toInt < c.toInt ↔ c.msb = false := by
  have hc := le_toNat_of_setWidth_ne h
  have hcw := c.isLt
  have hx := x.isLt
  have hvw : v < w := by
    refine Nat.lt_of_not_le fun hle => ?_
    have := two_pow_le hle; omega
  have h2 := two_pow_lt hvw
  have hz : (x.setWidth w).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  rw [← Bool.not_eq_true, msb_iff]
  rcases toInt_toNat_cases (x.setWidth w) with ⟨h1, h3⟩ | ⟨h1, h3⟩ <;>
  rcases toInt_toNat_cases c with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;>
  · rw [h3, h5]; omega

/-- `zext x <s c` exactly when `c` is non-negative. -/
theorem setWidth_slt_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).setWidth w ≠ c) :
    (x.setWidth w).slt c = !c.msb := by
  rw [BitVec.slt_eq_decide]
  cases hm : c.msb
  · simp only [Bool.not_false, decide_eq_true_eq]
    exact (setWidth_signed_of_ne x h).2 hm
  · simp only [Bool.not_true, decide_eq_false_iff_not]
    intro hlt
    have := (setWidth_signed_of_ne x h).1 hlt
    rw [hm] at this
    cases this

/-- `zext x ≤s c` exactly when `c` is non-negative: they're never equal. -/
theorem setWidth_sle_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).setWidth w ≠ c) :
    (x.setWidth w).sle c = !c.msb := by
  have hne : x.setWidth w ≠ c := fun he => by
    have := setWidth_ult_of_ne x h; rw [he] at this; simp [BitVec.ult_eq_decide] at this
  rw [BitVec.sle_eq_slt_or_eq, setWidth_slt_of_ne x h]
  simp [hne]

/-- `c <s zext x` exactly when `c` is negative. -/
theorem slt_setWidth_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).setWidth w ≠ c) :
    c.slt (x.setWidth w) = c.msb := by
  have := setWidth_sle_of_ne x h
  rw [BitVec.sle_eq_not_slt] at this
  simpa using this

/-- `c ≤s zext x` exactly when `c` is negative. -/
theorem sle_setWidth_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).setWidth w ≠ c) :
    c.sle (x.setWidth w) = c.msb := by
  rw [BitVec.sle_eq_not_slt, setWidth_slt_of_ne x h, Bool.not_not]

/-! ### `sext x` against a constant that isn't one. `IS.simplifyICmpInst.L4074` to `L4087`, and the two recursive
calls after them -/

/-- `sext x` is in `[-2 ^ v / 2, 2 ^ v / 2)`, as `x` is. -/
theorem toInt_signExtend_range (x : BitVec v) (h : v ≤ w) :
    -((2 ^ v : Nat) : Int) ≤ 2 * (x.signExtend w).toInt ∧ 2 * (x.signExtend w).toInt < ((2 ^ v : Nat) : Int) := by
  rw [BitVec.toInt_signExtend_of_le h]
  have := x.isLt
  rcases toInt_toNat_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> omega

/-- A constant that truncating to `v` bits and sign-extending back changes is outside the range of `v` bits, and
`v` is below its width. -/
theorem outside_of_signExtend_ne {c : BitVec w} (h : (c.setWidth v).signExtend w ≠ c) :
    v < w ∧ (2 * c.toInt < -((2 ^ v : Nat) : Int) ∨ ((2 ^ v : Nat) : Int) ≤ 2 * c.toInt) := by
  have hvw : v < w := by
    refine Nat.lt_of_not_le fun hle => h ?_
    rw [BitVec.signExtend_eq_setWidth_of_le _ hle, BitVec.setWidth_setWidth_of_le _ hle, BitVec.setWidth_eq]
  refine ⟨hvw, ?_⟩
  refine Classical.byContradiction fun hin => h (BitVec.eq_of_toInt_eq ?_)
  rw [BitVec.toInt_signExtend_of_le (Nat.le_of_lt hvw),
    ← BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_of_lt hvw),
    BitVec.toInt_signExtend_eq_toInt_bmod_of_le _ (Nat.le_of_lt hvw)]
  exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)

/-- `sext x ≠ c`, where `c` isn't a sign extension from `x`'s width. -/
theorem signExtend_ne_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).signExtend w ≠ c) :
    x.signExtend w ≠ c := by
  obtain ⟨hvw, hc⟩ := outside_of_signExtend_ne h
  have hx := toInt_signExtend_range x (Nat.le_of_lt hvw)
  intro he
  rw [he] at hx
  omega

/-- `sext x <s c` exactly when `c` is non-negative. -/
theorem signExtend_slt_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).signExtend w ≠ c) :
    (x.signExtend w).slt c = !c.msb := by
  obtain ⟨hvw, hc⟩ := outside_of_signExtend_ne h
  have hx := toInt_signExtend_range x (Nat.le_of_lt hvw)
  have hp := two_pow_lt hvw
  have := c.isLt
  rw [BitVec.slt_eq_decide]
  cases hm : c.msb
  · have := BitVec.msb_eq_false_iff_two_mul_lt.1 hm
    rcases toInt_toNat_cases c with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h2, Bool.not_false, decide_eq_true_eq] <;> omega
  · have := (msb_iff c).1 hm
    rcases toInt_toNat_cases c with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h2, Bool.not_true, decide_eq_false_iff_not] <;>
      omega

/-- `sext x ≤s c` exactly when `c` is non-negative: they're never equal. -/
theorem signExtend_sle_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).signExtend w ≠ c) :
    (x.signExtend w).sle c = !c.msb := by
  rw [BitVec.sle_eq_slt_or_eq, signExtend_slt_of_ne x h]
  simp [signExtend_ne_of_ne x h]

/-- `c <s sext x` exactly when `c` is negative. -/
theorem slt_signExtend_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).signExtend w ≠ c) :
    c.slt (x.signExtend w) = c.msb := by
  have := signExtend_sle_of_ne x h
  rw [BitVec.sle_eq_not_slt] at this
  simpa using this

/-- `c ≤s sext x` exactly when `c` is negative. -/
theorem sle_signExtend_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).signExtend w ≠ c) :
    c.sle (x.signExtend w) = c.msb := by
  rw [BitVec.sle_eq_not_slt, signExtend_slt_of_ne x h, Bool.not_not]

/-- `c <u sext x` exactly when `x` is negative: `c` is between the two blocks `sext` lands in. -/
theorem ult_signExtend_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).signExtend w ≠ c) :
    c.ult (x.signExtend w) = x.msb := by
  obtain ⟨hvw, hc⟩ := outside_of_signExtend_ne h
  have hx := toInt_signExtend_range x (Nat.le_of_lt hvw)
  have hp := two_pow_lt hvw
  have hcl := c.isLt
  have hxl := (x.signExtend w).isLt
  have hm : (x.signExtend w).msb = x.msb := by
    rw [BitVec.msb_signExtend]
    have : 0 < w := by omega
    simp [this, show ¬ (v ≥ w) by omega]
  rw [BitVec.ult_eq_decide, ← hm]
  cases hs : (x.signExtend w).msb
  · have := BitVec.msb_eq_false_iff_two_mul_lt.1 hs
    rcases toInt_toNat_cases c with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases toInt_toNat_cases (x.signExtend w) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    · simp only [decide_eq_false_iff_not]; omega
  · have := (msb_iff (x.signExtend w)).1 hs
    rcases toInt_toNat_cases c with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases toInt_toNat_cases (x.signExtend w) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    · simp only [decide_eq_true_eq]; omega

/-- `c ≤u sext x` exactly when `x` is negative: they're never equal. -/
theorem ule_signExtend_of_ne (x : BitVec v) {c : BitVec w} (h : (c.setWidth v).signExtend w ≠ c) :
    c.ule (x.signExtend w) = x.msb := by
  have hne := signExtend_ne_of_ne x h
  rw [← ult_signExtend_of_ne x h]
  simp only [BitVec.ule_eq_decide, BitVec.ult_eq_decide, decide_eq_decide]
  have : c.toNat ≠ (x.signExtend w).toNat := fun e => hne (BitVec.eq_of_toNat_eq e).symm
  omega

/-! ### Subtraction, successor and the sign bit, on `toNat`s: what `ConstantRange`'s arithmetic comes down to -/

/-- `x - y` on `toNat`s: the difference, or it plus `2 ^ w` if it went below 0. -/
theorem toNat_sub_or (x y : BitVec w) :
    (y.toNat ≤ x.toNat ∧ (x - y).toNat = x.toNat - y.toNat) ∨
      (x.toNat < y.toNat ∧ (x - y).toNat = x.toNat + 2 ^ w - y.toNat) := by
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_sub]
  by_cases h : y.toNat ≤ x.toNat
  · refine Or.inl ⟨h, ?_⟩
    rw [show 2 ^ w - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ w by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · refine Or.inr ⟨by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- `x + 1` on `toNat`s, at a positive width: the successor, or 0 past the maximum. -/
theorem toNat_add_one_or (x : BitVec w) (hw : 0 < w) :
    (x.toNat + 1 < 2 ^ w ∧ (x + 1#w).toNat = x.toNat + 1) ∨ (x.toNat + 1 = 2 ^ w ∧ (x + 1#w).toNat = 0) := by
  have hx := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_one hw]
  by_cases h : x.toNat + 1 < 2 ^ w
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [show x.toNat + 1 = 2 ^ w by omega, Nat.mod_self]

/-- `x - 1` on `toNat`s, at a positive width: the predecessor, or the maximum below 0. -/
theorem toNat_sub_one_or (x : BitVec w) (hw : 0 < w) :
    (0 < x.toNat ∧ (x - 1#w).toNat = x.toNat - 1) ∨ (x.toNat = 0 ∧ (x - 1#w).toNat = 2 ^ w - 1) := by
  have := toNat_sub_or x 1#w
  rw [BitVec.toNat_one hw] at this
  omega

/-- Subtracting `intMin` flips the sign bit. -/
theorem toNat_sub_intMin_or (x : BitVec w) (hw : 0 < w) :
    (2 * x.toNat < 2 ^ w ∧ (x - BitVec.intMin w).toNat = x.toNat + 2 ^ (w - 1)) ∨
      (2 ^ w ≤ 2 * x.toNat ∧ (x - BitVec.intMin w).toNat = x.toNat - 2 ^ (w - 1)) := by
  have hx := x.isLt
  have hp := two_pow_pred hw
  have := toNat_sub_or x (BitVec.intMin w)
  rw [BitVec.toNat_intMin_of_pos hw] at this
  by_cases h : 2 * x.toNat < 2 ^ w
  · exact Or.inl ⟨h, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- Signed order is unsigned order after subtracting `intMin`, which flips the sign bit. -/
theorem slt_eq_sub_intMin (x y : BitVec w) (hw : 0 < w) :
    x.slt y = decide ((x - BitVec.intMin w).toNat < (y - BitVec.intMin w).toNat) := by
  rw [BitVec.slt_eq_decide, decide_eq_decide]
  have := toNat_sub_intMin_or x hw
  have := toNat_sub_intMin_or y hw
  have hp := two_pow_pred hw
  rcases toInt_toNat_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases toInt_toNat_cases y with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

theorem sle_eq_sub_intMin (x y : BitVec w) (hw : 0 < w) :
    x.sle y = decide ((x - BitVec.intMin w).toNat ≤ (y - BitVec.intMin w).toNat) := by
  rw [BitVec.sle_eq_not_slt, slt_eq_sub_intMin y x hw]
  by_cases h : (x - BitVec.intMin w).toNat ≤ (y - BitVec.intMin w).toNat
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

/-! ### Comparing two extensions from one width: what `simplifyICmpInst`'s recursive calls on the operands of casts
rest on -/

theorem toNat_setWidth_of_le (x : BitVec v) (h : v ≤ w) : (x.setWidth w).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h)]

/-- Zero extension keeps unsigned order. -/
theorem setWidth_ult_setWidth (x y : BitVec v) (h : v ≤ w) : (x.setWidth w).ult (y.setWidth w) = x.ult y := by
  simp only [BitVec.ult_eq_decide, toNat_setWidth_of_le _ h]

theorem setWidth_ule_setWidth (x y : BitVec v) (h : v ≤ w) : (x.setWidth w).ule (y.setWidth w) = x.ule y := by
  simp only [BitVec.ule_eq_decide, toNat_setWidth_of_le _ h]

theorem setWidth_beq_setWidth (x y : BitVec v) (h : v ≤ w) : (x.setWidth w == y.setWidth w) = (x == y) := by
  have : x.setWidth w = y.setWidth w ↔ x = y := by
    rw [BitVec.toNat_eq, BitVec.toNat_eq, toNat_setWidth_of_le _ h, toNat_setWidth_of_le _ h]
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact this

/-- A zero extension to a wider type is non-negative, so signed order on it is unsigned order on the operand. -/
theorem toInt_setWidth_of_lt (x : BitVec v) (h : v < w) : (x.setWidth w).toInt = x.toNat := by
  have := two_pow_lt h
  have := x.isLt
  rcases toInt_toNat_cases (x.setWidth w) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [toNat_setWidth_of_le _ (Nat.le_of_lt h)] at h1 h2 <;> omega

theorem setWidth_slt_setWidth (x y : BitVec v) (h : v < w) : (x.setWidth w).slt (y.setWidth w) = x.ult y := by
  simp only [BitVec.slt_eq_decide, BitVec.ult_eq_decide, toInt_setWidth_of_lt _ h, Int.ofNat_lt]

theorem setWidth_sle_setWidth (x y : BitVec v) (h : v < w) : (x.setWidth w).sle (y.setWidth w) = x.ule y := by
  simp only [BitVec.sle_eq_decide, BitVec.ule_eq_decide, toInt_setWidth_of_lt _ h, Int.ofNat_le]

/-- Sign extension keeps signed order. -/
theorem signExtend_slt_signExtend (x y : BitVec v) (h : v ≤ w) :
    (x.signExtend w).slt (y.signExtend w) = x.slt y := by
  simp only [BitVec.slt_eq_decide, BitVec.toInt_signExtend_of_le h]

theorem signExtend_sle_signExtend (x y : BitVec v) (h : v ≤ w) :
    (x.signExtend w).sle (y.signExtend w) = x.sle y := by
  simp only [BitVec.sle_eq_decide, BitVec.toInt_signExtend_of_le h]

theorem signExtend_beq_signExtend (x y : BitVec v) (h : v ≤ w) :
    (x.signExtend w == y.signExtend w) = (x == y) := by
  have : x.signExtend w = y.signExtend w ↔ x = y := by
    rw [← BitVec.toInt_inj, ← BitVec.toInt_inj (x := x), BitVec.toInt_signExtend_of_le h,
      BitVec.toInt_signExtend_of_le h]
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact this

/-- Sign extension keeps unsigned order too: it sends the non-negative values to the bottom of the wider range and
the negative ones to its top, each in order. -/
theorem signExtend_ult_signExtend (x y : BitVec v) (h : v ≤ w) :
    (x.signExtend w).ult (y.signExtend w) = x.ult y := by
  have hx := toInt_signExtend_range x h
  have hy := toInt_signExtend_range y h
  have hx' := BitVec.toInt_signExtend_of_le (x := x) h
  have hy' := BitVec.toInt_signExtend_of_le (x := y) h
  have := two_pow_le h
  have := x.isLt
  have := y.isLt
  have := (x.signExtend w).isLt
  have := (y.signExtend w).isLt
  simp only [BitVec.ult_eq_decide, decide_eq_decide]
  rcases toInt_toNat_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases toInt_toNat_cases y with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  rcases toInt_toNat_cases (x.signExtend w) with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
  rcases toInt_toNat_cases (y.signExtend w) with ⟨h7, h8⟩ | ⟨h7, h8⟩ <;>
  omega

theorem signExtend_ule_signExtend (x y : BitVec v) (h : v ≤ w) :
    (x.signExtend w).ule (y.signExtend w) = x.ule y := by
  rw [BitVec.ule_eq_not_ult, BitVec.ule_eq_not_ult, signExtend_ult_signExtend _ _ h]

/-! ### Constants next to zero. `IS.simplifyICmpWithZero`'s `matchEquivZeroRHS` -/

/-- `x >s -1` is `x >=s 0`. -/
theorem allOnes_slt (x : BitVec w) (hw : 0 < w) : (BitVec.allOnes w).slt x = (0#w).sle x := by
  simp only [BitVec.slt_eq_decide, BitVec.sle_eq_decide, BitVec.toInt_allOnes, hw, ite_true, BitVec.toInt_zero,
    decide_eq_decide]
  omega

/-- `x <=s -1` is `x <s 0`. -/
theorem sle_allOnes (x : BitVec w) (hw : 0 < w) : x.sle (BitVec.allOnes w) = x.slt 0#w := by
  simp only [BitVec.slt_eq_decide, BitVec.sle_eq_decide, BitVec.toInt_allOnes, hw, ite_true, BitVec.toInt_zero,
    decide_eq_decide]
  omega

/-- `x >=s 1` is `x >s 0`. -/
theorem one_sle (x : BitVec w) (hw : 1 < w) : (1#w).sle x = (0#w).slt x := by
  simp only [BitVec.slt_eq_decide, BitVec.sle_eq_decide, BitVec.toInt_one hw, BitVec.toInt_zero, decide_eq_decide]
  omega

/-- `x <s 1` is `x <=s 0`. -/
theorem slt_one (x : BitVec w) (hw : 1 < w) : x.slt 1#w = x.sle 0#w := by
  simp only [BitVec.slt_eq_decide, BitVec.sle_eq_decide, BitVec.toInt_one hw, BitVec.toInt_zero, decide_eq_decide]
  omega

/-- `x >=u 1` is `x >u 0`. -/
theorem one_ule (x : BitVec w) (hw : 0 < w) : (1#w).ule x = (0#w).ult x := by
  simp only [BitVec.ult_eq_decide, BitVec.ule_eq_decide, BitVec.toNat_one hw, BitVec.toNat_ofNat, Nat.zero_mod,
    decide_eq_decide]
  omega

/-- `x <u 1` is `x <=u 0`. -/
theorem ult_one (x : BitVec w) (hw : 0 < w) : x.ult 1#w = x.ule 0#w := by
  simp only [BitVec.ult_eq_decide, BitVec.ule_eq_decide, BitVec.toNat_one hw, BitVec.toNat_ofNat, Nat.zero_mod,
    decide_eq_decide]
  omega

/-! ### Known bits of the sign. `IS.simplifyICmpWithZero` -/

/-- A value with every bit of `k` set has its sign bit set if `k` does. -/
theorem msb_of_and_eq_self {x k : BitVec w} (h : x &&& k = k) (hk : k.msb = true) : x.msb = true := by
  have := congrArg BitVec.msb h
  rw [BitVec.msb_and, hk] at this
  simpa using this

/-- A value with every bit of `k` clear has its sign bit clear if `k` has it set. -/
theorem msb_of_and_eq_zero {x k : BitVec w} (h : x &&& k = 0#w) (hk : k.msb = true) : x.msb = false := by
  have := congrArg BitVec.msb h
  rw [BitVec.msb_and, hk, BitVec.msb_zero] at this
  simpa using this

/-! ### Multiples. `IS.simplifyICmpWithConstant.L3146` -/

/-- A product that doesn't wrap unsigned is a multiple of each factor. -/
theorem mul_ne_of_umod_ne {x m c : BitVec w} (hov : x.umulOverflow m = false) (hc : c % m ≠ 0#w) : x * m ≠ c := by
  intro he
  apply hc
  apply BitVec.eq_of_toNat_eq
  have hlt : x.toNat * m.toNat < 2 ^ w := by
    simp only [BitVec.umulOverflow, ge_iff_le, decide_eq_false_iff_not, Nat.not_le] at hov
    exact hov
  rw [← he, BitVec.toNat_umod, BitVec.toNat_mul_of_lt hlt, Nat.mul_mod_left]
  simp

/-- A product that doesn't wrap signed is a multiple of each factor, in `srem`'s sense. -/
theorem mul_ne_of_srem_ne {x m c : BitVec w} (hov : x.smulOverflow m = false) (hc : c.srem m ≠ 0#w) : x * m ≠ c := by
  intro he
  apply hc
  apply BitVec.eq_of_toInt_eq
  rw [← he, BitVec.toInt_srem, BitVec.toInt_mul_of_not_smulOverflow (by simp [hov]), Int.mul_tmod_left,
    BitVec.toInt_zero]

/-! ### Values a value is known to be at least, or at most. `IS.simplifyICmpUsingMonotonicValues` -/

theorem ule_or_self_left (x y : BitVec w) : x.ule (x ||| y) = true := by
  simp only [BitVec.ule_eq_decide, BitVec.toNat_or, decide_eq_true_eq]
  exact Nat.left_le_or

theorem ule_or_self_right (x y : BitVec w) : y.ule (x ||| y) = true := by
  simp only [BitVec.ule_eq_decide, BitVec.toNat_or, decide_eq_true_eq]
  exact Nat.right_le_or

theorem ule_uaddSat_left (x y : BitVec w) :
    x.ule (if x.uaddOverflow y then BitVec.allOnes w else x + y) = true := by
  have := x.isLt
  simp only [BitVec.uaddOverflow, ge_iff_le]
  split
  · simp only [BitVec.ule_eq_decide, BitVec.toNat_allOnes, decide_eq_true_eq]; omega
  · next h =>
    simp only [decide_eq_true_eq, Nat.not_le] at h
    simp only [BitVec.ule_eq_decide, BitVec.toNat_add, Nat.mod_eq_of_lt h, decide_eq_true_eq]; omega

theorem ule_uaddSat_right (x y : BitVec w) :
    y.ule (if x.uaddOverflow y then BitVec.allOnes w else x + y) = true := by
  have := y.isLt
  simp only [BitVec.uaddOverflow, ge_iff_le]
  split
  · simp only [BitVec.ule_eq_decide, BitVec.toNat_allOnes, decide_eq_true_eq]; omega
  · next h =>
    simp only [decide_eq_true_eq, Nat.not_le] at h
    simp only [BitVec.ule_eq_decide, BitVec.toNat_add, Nat.mod_eq_of_lt h, decide_eq_true_eq]; omega

/-- A product that doesn't wrap is at least each factor whose partner isn't 0. -/
theorem ule_mul_left {x y : BitVec w} (hov : x.umulOverflow y = false) (hy : y ≠ 0#w) : x.ule (x * y) = true := by
  have hlt : x.toNat * y.toNat < 2 ^ w := by
    simp only [BitVec.umulOverflow, ge_iff_le, decide_eq_false_iff_not, Nat.not_le] at hov
    exact hov
  have hy' : 0 < y.toNat := by
    refine Nat.pos_of_ne_zero fun h0 => hy (BitVec.eq_of_toNat_eq ?_)
    simp [h0]
  simp only [BitVec.ule_eq_decide, BitVec.toNat_mul_of_lt hlt, decide_eq_true_eq]
  exact Nat.le_mul_of_pos_right _ hy'

theorem ule_mul_right {x y : BitVec w} (hov : x.umulOverflow y = false) (hx : x ≠ 0#w) : y.ule (x * y) = true := by
  have hlt : x.toNat * y.toNat < 2 ^ w := by
    simp only [BitVec.umulOverflow, ge_iff_le, decide_eq_false_iff_not, Nat.not_le] at hov
    exact hov
  have hx' : 0 < x.toNat := by
    refine Nat.pos_of_ne_zero fun h0 => hx (BitVec.eq_of_toNat_eq ?_)
    simp [h0]
  simp only [BitVec.ule_eq_decide, BitVec.toNat_mul_of_lt hlt, decide_eq_true_eq]
  exact Nat.le_mul_of_pos_left _ hx'

theorem and_ule_left (x y : BitVec w) : (x &&& y).ule x = true := by
  simp only [BitVec.ule_eq_decide, BitVec.toNat_and, decide_eq_true_eq]
  exact Nat.and_le_left

theorem and_ule_right (x y : BitVec w) : (x &&& y).ule y = true := by
  simp only [BitVec.ule_eq_decide, BitVec.toNat_and, decide_eq_true_eq]
  exact Nat.and_le_right

theorem umod_ule (x y : BitVec w) : (x % y).ule x = true := by
  simp only [BitVec.ule_eq_decide, BitVec.toNat_umod, decide_eq_true_eq]
  exact Nat.mod_le _ _

theorem udiv_ule (x y : BitVec w) : (x / y).ule x = true := by
  simp only [BitVec.ule_eq_decide, BitVec.toNat_udiv, decide_eq_true_eq]
  exact Nat.div_le_self _ _

theorem ushiftRight_ule (x y : BitVec w) : (x >>> y).ule x = true := by
  simp only [BitVec.ule_eq_decide, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    decide_eq_true_eq]
  exact Nat.div_le_self _ _

theorem usubSat_ule (x y : BitVec w) : (if BitVec.ult x y then 0#w else x - y).ule x = true := by
  split
  · simp [BitVec.ule_eq_decide]
  · next h =>
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq, Nat.not_lt] at h
    simp only [BitVec.ule_eq_decide, BitVec.toNat_sub_of_le (BitVec.le_def.2 h), decide_eq_true_eq]
    omega

end Peephole.Lemmas
