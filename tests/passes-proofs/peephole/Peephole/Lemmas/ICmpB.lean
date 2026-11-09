import IRLean.Int
import IRLean.Refine

/-! # Facts about values, at every width, that the `icmp-b` family's rewrites rest on

Each is about `BitVec w` or `Val w`, not about LLVM's code: a candidate for the lemma store. The rewrite each one was
cut from is named in its docstring. Every hypothesis has a counterexample at the end of the file, in
`LemmaStore.Counter`, showing the lemma is false without it. -/

namespace Peephole.Lemmas

open IRLean

variable {w : Nat}

/-! ### Orders -/

theorem ule_eq_not_ult (x y : BitVec w) : BitVec.ule x y = !BitVec.ult y x := by
  simp only [BitVec.ule, BitVec.ult]
  cases h : decide (x.toNat ≤ y.toNat) <;> simp_all <;> omega

theorem sle_eq_not_slt (x y : BitVec w) : BitVec.sle x y = !BitVec.slt y x := by
  simp only [BitVec.sle, BitVec.slt]
  cases h : decide (x.toInt ≤ y.toInt) <;> simp_all <;> omega

/-- Two values with the same sign bit are in the same signed order as unsigned. -/
theorem sle_eq_ule_of_msb_eq {x y : BitVec w} (h : x.msb = y.msb) : BitVec.sle x y = BitVec.ule x y := by
  have hx := BitVec.toInt_eq_msb_cond x
  have hy := BitVec.toInt_eq_msb_cond y
  simp only [BitVec.sle, BitVec.ule]
  rw [h] at hx
  cases hm : y.msb <;> simp only [hm] at hx hy <;> rw [hx, hy] <;> simp <;> omega

theorem slt_eq_ult_of_msb_eq {x y : BitVec w} (h : x.msb = y.msb) : BitVec.slt x y = BitVec.ult x y := by
  rw [← Bool.not_not (BitVec.slt x y), ← sle_eq_not_slt, sle_eq_ule_of_msb_eq h.symm, ule_eq_not_ult,
    Bool.not_not]

/-- A negative value is below a non-negative one. `IS.simplifyICmpWithBinOpOnLHS.L3239`. -/
theorem slt_of_msb {x y : BitVec w} (hx : x.msb = true) (hy : y.msb = false) : BitVec.slt x y = true := by
  have h1 := BitVec.toInt_eq_msb_cond x
  have h2 := BitVec.toInt_eq_msb_cond y
  simp only [hx, hy, ite_true, Bool.false_eq_true, ite_false] at h1 h2
  simp only [BitVec.slt, decide_eq_true_eq]
  have := x.isLt
  omega

/-! ### Known bits -/

/-- A value with no bit where `k` has one, where `k` has the sign bit, is non-negative. -/
theorem msb_false_of_and_eq_zero {x k : BitVec w} (h : x &&& k = 0#w) (hk : k.msb = true) : x.msb = false := by
  have := congrArg BitVec.msb h
  simp only [BitVec.msb_and, hk, Bool.and_true, BitVec.msb_zero] at this
  exact this

/-- A value with every bit `k` has, where `k` has the sign bit, is negative. -/
theorem msb_true_of_and_eq {x k : BitVec w} (h : x &&& k = k) (hk : k.msb = true) : x.msb = true := by
  have := congrArg BitVec.msb h
  simp only [BitVec.msb_and, hk, Bool.and_true] at this
  exact this

/-! ### `or`, `urem`, `lshr`, `udiv`: what `simplifyICmpWithBinOpOnLHS` knows -/

theorem ule_or_right (x y : BitVec w) : BitVec.ule y (x ||| y) = true := by
  simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_or]
  exact Nat.right_le_or

/-- `(x | y) >=s y` where `y` is negative or `x` isn't. `IS.simplifyICmpWithBinOpOnLHS.L3241`. -/
theorem sle_or_right {x y : BitVec w} (h : y.msb = true ∨ x.msb = false) : BitVec.sle y (x ||| y) = true := by
  rw [sle_eq_ule_of_msb_eq, ule_or_right]
  rw [BitVec.msb_or]
  rcases h with h | h <;> simp [h]

theorem umod_lt {x y : BitVec w} (hy : y ≠ 0#w) : BitVec.ult (x % y) y = true := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_umod]
  apply Nat.mod_lt
  have : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

/-- `x urem y <s y` where `y` isn't negative. `IS.simplifyICmpWithBinOpOnLHS.L3260`. -/
theorem umod_slt {x y : BitVec w} (hy : y ≠ 0#w) (hm : y.msb = false) : BitVec.slt (x % y) y = true := by
  have hl := umod_lt (x := x) hy
  rw [slt_eq_ult_of_msb_eq, hl]
  rw [hm, BitVec.msb_eq_decide, BitVec.toNat_umod]
  rw [BitVec.msb_eq_decide] at hm
  simp only [decide_eq_false_iff_not, Nat.not_le] at hm ⊢
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_umod] at hl
  omega

/-- `x >>u c <u x` for `x ≠ 0` and `0 < c < w`. `IS.simplifyICmpWithBinOpOnLHS.L3295`. -/
theorem ushiftRight_ult {x c : BitVec w} (hx : x ≠ 0#w) (hc : c.toNat ≠ 0) :
    BitVec.ult (x >>> c) x = true := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have h0 : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simpa using h))
  apply Nat.div_lt_self (by omega)
  exact Nat.one_lt_two_pow hc

/-- `x udiv c <u x` for `x ≠ 0` and `c` not 1 (`BitVec`'s division by 0 is 0). `IS.simplifyICmpWithBinOpOnLHS.L3295`. -/
theorem udiv_ult {x c : BitVec w} (hx : x ≠ 0#w) (hc : c.toNat ≠ 1) : BitVec.ult (x / c) x = true := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_udiv]
  have h0 : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simpa using h))
  by_cases h1 : c.toNat = 0
  · rw [h1, Nat.div_zero]; omega
  · exact Nat.div_lt_self (by omega) (by omega)

/-- `(x * c1) udiv c2 <=u x` for `c1 <=u c2`, even if the product wraps. `IS.simplifyICmpWithBinOpOnLHS.L3321`. -/
theorem mul_udiv_ule {x c1 c2 : BitVec w} (hc : BitVec.ule c1 c2 = true) :
    BitVec.ule (x * c1 / c2) x = true := by
  simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_udiv, BitVec.toNat_mul] at hc ⊢
  apply Nat.div_le_of_le_mul
  calc x.toNat * c1.toNat % 2 ^ w ≤ x.toNat * c1.toNat := Nat.mod_le _ _
    _ ≤ x.toNat * c2.toNat := Nat.mul_le_mul_left _ hc
    _ = c2.toNat * x.toNat := Nat.mul_comm _ _

/-- `(x * c1) >>u c2 <=u x` for `c1 <=u 1 << c2` (`APInt`'s and `BitVec`'s `<<` past the width give 0).
`IS.simplifyICmpWithBinOpOnLHS.L3321`. -/
theorem mul_ushiftRight_ule {x c1 c2 : BitVec w} (hc : BitVec.ule c1 (1#w <<< c2) = true) :
    BitVec.ule ((x * c1) >>> c2) x = true := by
  simp only [BitVec.ule, decide_eq_true_eq, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq] at hc ⊢
  by_cases h2 : c2.toNat < w
  case neg =>
    rw [Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 (by omega)) _)] at hc
    have : c1.toNat = 0 := by omega
    rw [this, Nat.mul_zero, Nat.zero_mod, Nat.zero_div]
    omega
  have hw : 0 < w := by omega
  have h1 : (1#w).toNat = 1 := by simp [Nat.one_mod_two_pow hw]
  rw [h1, Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h2)] at hc
  apply Nat.div_le_of_le_mul
  calc x.toNat * c1.toNat % 2 ^ w ≤ x.toNat * c1.toNat := Nat.mod_le _ _
    _ ≤ x.toNat * 2 ^ c2.toNat := Nat.mul_le_mul_left _ hc
    _ = 2 ^ c2.toNat * x.toNat := Nat.mul_comm _ _

/-- `(x << c1) udiv c2 <=u x` for `1 << c1 <=u c2`. `IS.simplifyICmpWithBinOpOnLHS.L3321`. -/
theorem shiftLeft_udiv_ule {x c1 c2 : BitVec w} (hc : BitVec.ule (1#w <<< c1) c2 = true) :
    BitVec.ule ((x <<< c1) / c2) x = true := by
  simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_udiv, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq] at hc ⊢
  by_cases h1 : c1.toNat < w
  case neg =>
    rw [Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 (by omega)) _), Nat.zero_div]
    omega
  have hw : 0 < w := by omega
  have h1' : (1#w).toNat = 1 := by simp [Nat.one_mod_two_pow hw]
  rw [h1', Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h1)] at hc
  apply Nat.div_le_of_le_mul
  calc x.toNat * 2 ^ c1.toNat % 2 ^ w ≤ x.toNat * 2 ^ c1.toNat := Nat.mod_le _ _
    _ ≤ x.toNat * c2.toNat := Nat.mul_le_mul_left _ hc
    _ = c2.toNat * x.toNat := Nat.mul_comm _ _

/-- `c - x` isn't `x` when `c` is odd. `IS.simplifyICmpWithBinOpOnLHS.L3330`. -/
theorem sub_ne_of_odd {c x : BitVec w} (hc : (c &&& 1#w).toNat = 1) : (c - x == x) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro h
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp at hc
    · exact hw
  have hc' : c = x + x := by
    have := BitVec.sub_add_cancel c x
    rw [h] at this
    exact this.symm
  rw [BitVec.toNat_and, hc', BitVec.toNat_add] at hc
  have h1 : (1#w).toNat = 1 := by simp [Nat.one_mod_two_pow hw]
  have hd : 2 ∣ 2 ^ w := by simpa using Nat.pow_dvd_pow 2 hw
  rw [h1, Nat.and_one_is_mod, Nat.mod_mod_of_dvd _ hd] at hc
  omega

/-! ### What `simplifyICmpWithBinOp` knows -/

/-- `0 - zext x` is `-x` as a signed value, since `x` is less than half the range. -/
theorem toInt_zero_sub_setWidth {v : Nat} (x : BitVec v) (h : v < w) :
    (0#w - x.setWidth w).toInt = -(x.toNat : Int) := by
  have hx := x.isLt
  have hv : 2 ^ v ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hw : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hs : (x.setWidth w).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub, hs]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
  by_cases h0 : x.toNat = 0
  · rw [h0]; simp
  · rw [Nat.mod_eq_of_lt (by omega)]
    split <;> omega

/-- `0 - zext x <=s c` for a non-negative `c`. `IS.simplifyICmpWithBinOp.L3467`. -/
theorem zero_sub_setWidth_sle {v : Nat} (x : BitVec v) (h : v < w) {c : BitVec w} (hc : c.msb = false) :
    BitVec.sle (0#w - x.setWidth w) c = true := by
  simp only [BitVec.sle, decide_eq_true_eq, toInt_zero_sub_setWidth x h, BitVec.toInt_eq_toNat_of_msb hc]
  omega

/-- `0 - zext x <s c` for a positive `c`. `IS.simplifyICmpWithBinOp.L3461`. -/
theorem zero_sub_setWidth_slt {v : Nat} (x : BitVec v) (h : v < w) {c : BitVec w} (hc : c.msb = false)
    (hc0 : c.toNat ≠ 0) : BitVec.slt (0#w - x.setWidth w) c = true := by
  simp only [BitVec.slt, decide_eq_true_eq, toInt_zero_sub_setWidth x h, BitVec.toInt_eq_toNat_of_msb hc]
  omega

/-- A power of two shifted left is a power of two or zero, and no more than the sign bit. -/
theorem shiftLeft_pow2 {c : BitVec w} (s : Nat) (hc : c.toNat.isPowerOfTwo) :
    ((c <<< s).toNat = 0 ∨ (c <<< s).toNat.isPowerOfTwo) ∧ 2 * (c <<< s).toNat ≤ 2 ^ w := by
  obtain ⟨k, hk⟩ := hc
  have hlt := c.isLt
  rw [hk] at hlt
  have hkw : k < w := (Nat.pow_lt_pow_iff_right (by decide)).1 hlt
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hk, ← Nat.pow_add]
  by_cases hks : k + s < w
  · rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hks)]
    refine ⟨Or.inr ⟨k + s, rfl⟩, ?_⟩
    rw [← Nat.pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · rw [Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))]
    exact ⟨Or.inl rfl, by simp⟩

/-- `(c2 << x) != c` for a power of two `c2` and a `c` that isn't one, where the shift can't make zero, or `c` isn't
zero. `IS.simplifyICmpWithBinOp.L3492`. -/
theorem shiftLeft_pow2_ne {c2 c : BitVec w} (s : Nat) (h2 : c2.toNat.isPowerOfTwo) (hc : ¬ c.toNat.isPowerOfTwo)
    (hz : c2 <<< s ≠ 0#w ∨ c ≠ 0#w) : (c2 <<< s == c) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro he
  obtain ⟨h1, -⟩ := shiftLeft_pow2 s h2
  rw [he] at h1 hz
  rcases h1 with h1 | h1
  · have : c = 0#w := BitVec.eq_of_toNat_eq (by simpa using h1)
    rcases hz with hz | hz <;> exact hz this
  · exact hc h1

/-- `c << x <=u signmask` for a power of two `c`. `IS.simplifyICmpWithBinOp.L3505`. -/
theorem shiftLeft_pow2_ule_intMin {c : BitVec w} (s : Nat) (hc : c.toNat.isPowerOfTwo) :
    BitVec.ule (c <<< s) (BitVec.intMin w) = true := by
  obtain ⟨-, h⟩ := shiftLeft_pow2 s hc
  obtain ⟨k, hk⟩ := hc
  have hlt := c.isLt
  rw [hk] at hlt
  have hkw : k < w := (Nat.pow_lt_pow_iff_right (by decide)).1 hlt
  have hw : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_intMin]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- `a &&& ~~~b = 0`, `APInt::isSubsetOf`, makes `a <=u b`. -/
theorem ule_of_subset {a b : BitVec w} (h : a &&& ~~~b = 0#w) : BitVec.ule a b = true := by
  have he : a = a &&& b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun x => x.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
      BitVec.getLsbD_zero] at this
    simp only [BitVec.getLsbD_and]
    cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> simp_all
  simp only [BitVec.ule, decide_eq_true_eq]
  rw [he, BitVec.toNat_and]
  exact Nat.and_le_right

/-- `x & c1` is a subset of `x & c2` where `c1` is of `c2`. `IS.simplifyICmpWithBinOp.L3543`. -/
theorem and_subset {x c1 c2 : BitVec w} (h : c1 &&& ~~~c2 = 0#w) : (x &&& c1) &&& ~~~(x &&& c2) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun x => x.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and, BitVec.getLsbD_zero] at this ⊢
  revert this
  generalize x.getLsbD i = a
  generalize c1.getLsbD i = b
  generalize c2.getLsbD i = c
  cases a <;> cases b <;> cases c <;> decide

/-- `x | c1` is a subset of `x | c2` where `c1` is of `c2`. `IS.simplifyICmpWithBinOp.L3543`. -/
theorem or_subset {x c1 c2 : BitVec w} (h : c1 &&& ~~~c2 = 0#w) : (x ||| c1) &&& ~~~(x ||| c2) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun x => x.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_zero] at this ⊢
  revert this
  generalize x.getLsbD i = a
  generalize c1.getLsbD i = b
  generalize c2.getLsbD i = c
  cases a <;> cases b <;> cases c <;> decide

/-! ### Min and max: what `simplifyICmpWithMinMax` knows -/

/-- `smax(a, b) >=s a`. `IS.simplifyICmpWithMinMax.L3680`. -/
theorem sle_smax (a b : BitVec w) : BitVec.sle a (if a.sle b then b else a) = true := by
  split <;> simp_all [BitVec.sle]

/-- `smax(a, b) == a` exactly when `a >=s b`. `IS.extractEquivalentCondition.L2630`, through
`simplifyICmpWithMinMax`. -/
theorem smax_beq (a b : BitVec w) : ((if a.sle b then b else a) == a) = BitVec.sle b a := by
  simp only [BitVec.sle, decide_eq_true_eq]
  split
  · next h =>
    apply Bool.eq_iff_iff.2
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toInt_inj]
    omega
  · next h => simp only [BEq.rfl]; exact (decide_eq_true (by omega)).symm

/-- `smax(a, b) <=s a` exactly when `a >=s b`. -/
theorem smax_sle (a b : BitVec w) : BitVec.sle (if a.sle b then b else a) a = BitVec.sle b a := by
  split <;> simp_all [BitVec.sle] <;> omega

/-- `a >=s smin(a, b)`. `IS.simplifyICmpWithMinMax.L3680`. -/
theorem smin_sle (a b : BitVec w) : BitVec.sle (if a.sle b then a else b) a = true := by
  split <;> simp_all [BitVec.sle] <;> omega

/-- `a == smin(a, b)` exactly when `a <=s b`. -/
theorem beq_smin (a b : BitVec w) : (a == (if a.sle b then a else b)) = BitVec.sle a b := by
  simp only [BitVec.sle, decide_eq_true_eq]
  split
  · next h => simp only [BEq.rfl]; exact (decide_eq_true (by omega)).symm
  · next h =>
    apply Bool.eq_iff_iff.2
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toInt_inj]
    omega

/-- `a <=s smin(a, b)` exactly when `a <=s b`. -/
theorem sle_smin (a b : BitVec w) : BitVec.sle a (if a.sle b then a else b) = BitVec.sle a b := by
  split <;> simp_all [BitVec.sle]

theorem ule_umax (a b : BitVec w) : BitVec.ule a (if a.ule b then b else a) = true := by
  split <;> simp_all [BitVec.ule]

theorem umax_beq (a b : BitVec w) : ((if a.ule b then b else a) == a) = BitVec.ule b a := by
  simp only [BitVec.ule, decide_eq_true_eq]
  split
  · next h =>
    apply Bool.eq_iff_iff.2
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj]
    omega
  · next h => simp only [BEq.rfl]; exact (decide_eq_true (by omega)).symm

theorem umax_ule (a b : BitVec w) : BitVec.ule (if a.ule b then b else a) a = BitVec.ule b a := by
  split <;> simp_all [BitVec.ule] <;> omega

theorem umin_ule (a b : BitVec w) : BitVec.ule (if a.ule b then a else b) a = true := by
  split <;> simp_all [BitVec.ule] <;> omega

theorem beq_umin (a b : BitVec w) : (a == (if a.ule b then a else b)) = BitVec.ule a b := by
  simp only [BitVec.ule, decide_eq_true_eq]
  split
  · next h => simp only [BEq.rfl]; exact (decide_eq_true (by omega)).symm
  · next h =>
    apply Bool.eq_iff_iff.2
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj]
    omega

theorem ule_umin (a b : BitVec w) : BitVec.ule a (if a.ule b then a else b) = BitVec.ule a b := by
  split <;> simp_all [BitVec.ule]

/-- `smin(c, d) <=s smax(a, b)` where they share an operand. `IS.simplifyICmpWithMinMax.L3773`. -/
theorem smin_sle_smax {a b c d : BitVec w} (h : c = a ∨ d = a ∨ c = b ∨ d = b) :
    BitVec.sle (if c.sle d then c else d) (if a.sle b then b else a) = true := by
  simp only [BitVec.sle, decide_eq_true_eq] at *
  rcases h with rfl | rfl | rfl | rfl <;> split <;> split <;> omega

/-- `umin(c, d) <=u umax(a, b)` where they share an operand. `IS.simplifyICmpWithMinMax.L3782`. -/
theorem umin_ule_umax {a b c d : BitVec w} (h : c = a ∨ d = a ∨ c = b ∨ d = b) :
    BitVec.ule (if c.ule d then c else d) (if a.ule b then b else a) = true := by
  simp only [BitVec.ule, decide_eq_true_eq] at *
  rcases h with rfl | rfl | rfl | rfl <;> split <;> split <;> omega

/-! ### Saturating arithmetic: what `simplifyICmpWithIntrinsicOnLHS` knows -/

/-- `uadd.sat(x, y) >=u x + y`. `IS.simplifyICmpWithIntrinsicOnLHS.L3826`. -/
theorem add_ule_uaddSat (x y : BitVec w) :
    BitVec.ule (x + y) (if x.uaddOverflow y then BitVec.allOnes w else x + y) = true := by
  split
  · simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_allOnes]
    have := (x + y).isLt
    omega
  · simp [BitVec.ule]

/-- `usub.sat(x, y) <=u x - y`. `IS.simplifyICmpWithIntrinsicOnLHS.L3836`. -/
theorem usubSat_ule_sub (x y : BitVec w) :
    BitVec.ule (if BitVec.ult x y then 0#w else x - y) (x - y) = true := by
  split <;> simp [BitVec.ule]

/-! ### Compares of `X + C0` and `X`: what `simplifyAndOfICmpsWithAdd` and `simplifyOrOfICmpsWithAdd` know -/

theorem toInt_cases (x : BitVec w) :
    (x.msb = false ∧ x.toInt = (x.toNat : Int) ∧ 2 * x.toNat < 2 ^ w) ∨
      (x.msb = true ∧ x.toInt = (x.toNat : Int) - ((2 ^ w : Nat) : Int) ∧ 2 ^ w ≤ 2 * x.toNat) := by
  have h := BitVec.toInt_eq_toNat_cond x
  have hm := BitVec.msb_eq_true_iff_two_mul_ge (x := x)
  by_cases hc : 2 * x.toNat < 2 ^ w
  · left
    simp only [hc, ↓reduceIte] at h
    refine ⟨?_, h, hc⟩
    cases hx : x.msb
    · rfl
    · have := hm.1 hx; omega
  · right
    simp only [hc, ↓reduceIte] at h
    exact ⟨hm.2 (by omega), h, by omega⟩

theorem toNat_add_cases (x y : BitVec w) :
    (x.toNat + y.toNat < 2 ^ w ∧ (x + y).toNat = x.toNat + y.toNat) ∨
      (2 ^ w ≤ x.toNat + y.toNat ∧ (x + y).toNat = x.toNat + y.toNat - 2 ^ w) := by
  rw [BitVec.toNat_add]
  have := x.isLt
  have := y.isLt
  by_cases h : x.toNat + y.toNat < 2 ^ w
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem toNat_ofNat_small {k : Nat} (hw : 2 ≤ w) (hk : k ≤ 2) : (BitVec.ofNat w k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have : 4 ≤ 2 ^ w := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  omega

theorem two_le_of_toInt_pos {c : BitVec w} (h : 0 < c.toInt) : 2 ≤ w := by
  rcases toInt_cases c with ⟨-, hi, hb⟩ | ⟨-, hi, hb⟩
  · rcases w with _ | _ | w
    · have : c.toNat = 0 := by have := c.isLt; simp at this; omega
      omega
    · have : c.toNat = 0 := by simp at hb; omega
      omega
    · omega
  · have := c.isLt
    omega

/-- `(v + c0) <u c0 + 2` and `v >s c0` don't both hold for `c0 >s 0`. `IS.simplifyAndOfICmpsWithAdd.L1682`. -/
theorem ult_add_two_and_sgt {v c0 : BitVec w} (hc : 0 < c0.toInt) :
    (BitVec.ult (v + c0) (c0 + 2#w) && BitVec.slt c0 v) = false := by
  have hw := two_le_of_toInt_pos hc
  have h2 := toNat_ofNat_small (k := 2) hw (by omega)
  simp only [Bool.and_eq_false_iff, BitVec.ult, BitVec.slt, decide_eq_false_iff_not, Nat.not_lt, Int.not_lt]
  rcases toInt_cases c0 with ⟨-, hc0, hb0⟩ | ⟨-, hc0, hb0⟩ <;>
  rcases toInt_cases v with ⟨-, hv, hbv⟩ | ⟨-, hv, hbv⟩ <;>
  rcases toNat_add_cases v c0 with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;>
  rcases toNat_add_cases c0 (2#w) with ⟨ha', hs'⟩ | ⟨ha', hs'⟩ <;>
  rw [hs, hs', hc0, hv] <;> omega

/-- `(v + c0) <s c0 + 2` and `v >s c0` don't both hold for `c0 >s 0` where `v + c0` doesn't overflow signed.
`IS.simplifyAndOfICmpsWithAdd.L1684`. -/
theorem slt_add_two_and_sgt {v c0 : BitVec w} (hc : 0 < c0.toInt) (hn : v.saddOverflow c0 = false) :
    (BitVec.slt (v + c0) (c0 + 2#w) && BitVec.slt c0 v) = false := by
  have hw := two_le_of_toInt_pos hc
  have h2 := toNat_ofNat_small (k := 2) hw (by omega)
  have hsum := BitVec.toInt_add_of_not_saddOverflow (x := v) (y := c0) (by simp [hn])
  simp only [Bool.and_eq_false_iff, BitVec.slt, decide_eq_false_iff_not, Int.not_lt]
  rw [hsum]
  rcases toInt_cases c0 with ⟨-, hc0, hb0⟩ | ⟨-, hc0, hb0⟩ <;>
  rcases toInt_cases (c0 + 2#w) with ⟨-, hc2, hb2⟩ | ⟨-, hc2, hb2⟩ <;>
  rcases toNat_add_cases c0 (2#w) with ⟨ha', hs'⟩ | ⟨ha', hs'⟩ <;>
  rw [hc2, hs', hc0] <;> rw [hs'] at hb2 <;> omega

/-- `(v + c0) <=u c0 + 1` and `v >s c0` don't both hold for `c0 >s 0`. `IS.simplifyAndOfICmpsWithAdd.L1688`. -/
theorem ule_add_one_and_sgt {v c0 : BitVec w} (hc : 0 < c0.toInt) :
    (BitVec.ule (v + c0) (c0 + 1#w) && BitVec.slt c0 v) = false := by
  have hw := two_le_of_toInt_pos hc
  have h1 := toNat_ofNat_small (k := 1) hw (by omega)
  simp only [Bool.and_eq_false_iff, BitVec.ule, BitVec.slt, decide_eq_false_iff_not, Nat.not_le, Int.not_lt]
  rcases toInt_cases c0 with ⟨-, hc0, hb0⟩ | ⟨-, hc0, hb0⟩ <;>
  rcases toInt_cases v with ⟨-, hv, hbv⟩ | ⟨-, hv, hbv⟩ <;>
  rcases toNat_add_cases v c0 with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;>
  rcases toNat_add_cases c0 (1#w) with ⟨ha', hs'⟩ | ⟨ha', hs'⟩ <;>
  rw [hs, hs', hc0, hv] <;> omega

/-- `(v + c0) <=s c0 + 1` and `v >s c0` don't both hold for `c0 >s 0` where `v + c0` doesn't overflow signed.
`IS.simplifyAndOfICmpsWithAdd.L1690`. -/
theorem sle_add_one_and_sgt {v c0 : BitVec w} (hc : 0 < c0.toInt) (hn : v.saddOverflow c0 = false) :
    (BitVec.sle (v + c0) (c0 + 1#w) && BitVec.slt c0 v) = false := by
  have hw := two_le_of_toInt_pos hc
  have h1 := toNat_ofNat_small (k := 1) hw (by omega)
  have hsum := BitVec.toInt_add_of_not_saddOverflow (x := v) (y := c0) (by simp [hn])
  simp only [Bool.and_eq_false_iff, BitVec.sle, BitVec.slt, decide_eq_false_iff_not, Int.not_le, Int.not_lt]
  rw [hsum]
  rcases toInt_cases c0 with ⟨-, hc0, hb0⟩ | ⟨-, hc0, hb0⟩ <;>
  rcases toInt_cases (c0 + 1#w) with ⟨-, hc2, hb2⟩ | ⟨-, hc2, hb2⟩ <;>
  rcases toNat_add_cases c0 (1#w) with ⟨ha', hs'⟩ | ⟨ha', hs'⟩ <;>
  rw [hc2, hs', hc0] <;> rw [hs'] at hb2 <;> omega

/-- `(v + c0) <u c0 + 2` and `v >u c0` don't both hold for `c0 != 0` where `v + c0` doesn't overflow unsigned.
`IS.simplifyAndOfICmpsWithAdd.L1696`. -/
theorem ult_add_two_and_ugt {v c0 : BitVec w} (hc : c0 ≠ 0#w) (hn : v.uaddOverflow c0 = false) :
    (BitVec.ult (v + c0) (c0 + 2#w) && BitVec.ult c0 v) = false := by
  have hc' : c0.toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
  have hsum := BitVec.toNat_add_of_not_uaddOverflow (x := v) (y := c0) (by simp [hn])
  simp only [BitVec.uaddOverflow, decide_eq_false_iff_not, Nat.not_le] at hn
  simp only [Bool.and_eq_false_iff, BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]
  rw [hsum]
  rcases toNat_add_cases c0 (2#w) with ⟨ha', hs'⟩ | ⟨ha', hs'⟩ <;> rw [hs'] <;>
  rw [BitVec.toNat_ofNat] at * <;>
  rcases Nat.lt_or_ge w 2 with hw | hw
  · have : 2 ^ w ≤ 2 := by
      calc 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 := rfl
    have := c0.isLt
    omega
  · rw [Nat.mod_eq_of_lt (a := 2) (by have := toNat_ofNat_small (k := 2) hw (by omega); rw [BitVec.toNat_ofNat] at this; have : 4 ≤ 2 ^ w := (by calc 4 = 2 ^ 2 := rfl
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw); omega)] at *
    omega
  · have : 2 ^ w ≤ 2 := by
      calc 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 := rfl
    have := c0.isLt
    omega
  · have : 4 ≤ 2 ^ w := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    rw [Nat.mod_eq_of_lt (a := 2) (by omega)] at *
    have := v.isLt
    omega

/-- `(v + c0) <=u c0 + 1` and `v >u c0` don't both hold for `c0 != 0` where `v + c0` doesn't overflow unsigned.
`IS.simplifyAndOfICmpsWithAdd.L1699`. -/
theorem ule_add_one_and_ugt {v c0 : BitVec w} (hc : c0 ≠ 0#w) (hn : v.uaddOverflow c0 = false) :
    (BitVec.ule (v + c0) (c0 + 1#w) && BitVec.ult c0 v) = false := by
  have hc' : c0.toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
  have hsum := BitVec.toNat_add_of_not_uaddOverflow (x := v) (y := c0) (by simp [hn])
  simp only [BitVec.uaddOverflow, decide_eq_false_iff_not, Nat.not_le] at hn
  simp only [Bool.and_eq_false_iff, BitVec.ule, BitVec.ult, decide_eq_false_iff_not, Nat.not_le, Nat.not_lt]
  rw [hsum]
  have h0 := c0.isLt
  have hv := v.isLt
  have hw : 1 ≤ w := by
    rcases w with _ | w
    · simp at h0; omega
    · omega
  have : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  have h1 : (1#w).toNat = 1 := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rcases toNat_add_cases c0 (1#w) with ⟨ha', hs'⟩ | ⟨ha', hs'⟩ <;> rw [hs'] <;> omega

/-! ### `ctpop`: what `simplifyAndOrOfICmpsWithCtpop` knows -/

/-! ### Casts of `i1`: what `simplifyAndOrOfCmps` knows -/

theorem setWidth_or {v : Nat} (x y : BitVec v) : (x ||| y).setWidth w = x.setWidth w ||| y.setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or]
  cases decide (i < w) <;> simp

theorem signExtend_or {v : Nat} (x y : BitVec v) :
    (x ||| y).signExtend w = x.signExtend w ||| y.signExtend w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_or, BitVec.msb_or]
  by_cases h : i < v <;> simp only [h, ↓reduceIte] <;> cases decide (i < w) <;> rfl

/-! ### A `select` against a min or max: what `simplifyCmpSelOfMaxMin` knows -/

/-- `smax(x, y)` is `x` where `x >=s y`. `IS.simplifyCmpSelOfMaxMin.L4763`. -/
theorem smax_of_sle {x y : BitVec w} (h : BitVec.sle y x = true) : (if x.sle y then y else x) = x := by
  split
  · next h' => apply BitVec.eq_of_toInt_eq; simp only [BitVec.sle, decide_eq_true_eq] at h h'; omega
  · rfl

/-- `smin(x, y)` is `x` where `x <=s y`. -/
theorem smin_of_sle {x y : BitVec w} (h : BitVec.sle x y = true) : (if x.sle y then x else y) = x := by
  simp [h]

/-- `umax(x, y)` is `x` where `x >=u y`. -/
theorem umax_of_ule {x y : BitVec w} (h : BitVec.ule y x = true) : (if x.ule y then y else x) = x := by
  split
  · next h' => apply BitVec.eq_of_toNat_eq; simp only [BitVec.ule, decide_eq_true_eq] at h h'; omega
  · rfl

/-- `umin(x, y)` is `x` where `x <=u y`. -/
theorem umin_of_ule {x y : BitVec w} (h : BitVec.ule x y = true) : (if x.ule y then x else y) = x := by
  simp [h]

end Peephole.Lemmas


/-! ## Counterexamples for the lemmas above

For each hypothesis of a lemma above, the lemma without it is false: `drop_<hypothesis>` gives one input where it
fails. For each lemma with hypotheses, `sat` gives one input where they all hold. `tools/store/store.py check` checks
each states exactly what it has to. -/

namespace LemmaStore.Counter

open IRLean

theorem not_pow2_three : ¬ Nat.isPowerOfTwo 3 := by
  rintro ⟨k, hk⟩
  rcases k with _ | _ | k
  · simp at hk
  · simp at hk
  · have : 4 ≤ 2 ^ (k + 2) := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem not_pow2_zero : ¬ Nat.isPowerOfTwo 0 := by
  rintro ⟨k, hk⟩
  have := Nat.two_pow_pos k
  omega

/-! ### Orders -/

/-- `-1 <=s 0`, and `255 <=u 0` isn't. -/
theorem Peephole.Lemmas.sle_eq_ule_of_msb_eq.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w}, BitVec.sle x y = BitVec.ule x y :=
  fun h => absurd (@h 8 255#8 0#8) (by decide)

theorem Peephole.Lemmas.sle_eq_ule_of_msb_eq.sat : ∃ (w : Nat) (x y : BitVec w), x.msb = y.msb :=
  ⟨8, 0#8, 0#8, rfl⟩

theorem Peephole.Lemmas.slt_eq_ult_of_msb_eq.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w}, BitVec.slt x y = BitVec.ult x y :=
  fun h => absurd (@h 8 255#8 0#8) (by decide)

theorem Peephole.Lemmas.slt_eq_ult_of_msb_eq.sat : ∃ (w : Nat) (x y : BitVec w), x.msb = y.msb :=
  ⟨8, 0#8, 0#8, rfl⟩

theorem Peephole.Lemmas.slt_of_msb.drop_hx :
    ¬ ∀ {w : Nat} {x y : BitVec w}, y.msb = false → BitVec.slt x y = true :=
  fun h => absurd (@h 8 0#8 0#8 (by decide)) (by decide)

theorem Peephole.Lemmas.slt_of_msb.drop_hy :
    ¬ ∀ {w : Nat} {x y : BitVec w}, x.msb = true → BitVec.slt x y = true :=
  fun h => absurd (@h 8 255#8 255#8 (by decide)) (by decide)

theorem Peephole.Lemmas.slt_of_msb.sat : ∃ (w : Nat) (x y : BitVec w), x.msb = true ∧ y.msb = false :=
  ⟨8, 255#8, 0#8, by decide, by decide⟩

/-! ### Known bits -/

theorem Peephole.Lemmas.msb_false_of_and_eq_zero.drop_h :
    ¬ ∀ {w : Nat} {x k : BitVec w}, k.msb = true → x.msb = false :=
  fun h => absurd (@h 8 128#8 128#8 (by decide)) (by decide)

theorem Peephole.Lemmas.msb_false_of_and_eq_zero.drop_hk :
    ¬ ∀ {w : Nat} {x k : BitVec w}, x &&& k = 0#w → x.msb = false :=
  fun h => absurd (@h 8 128#8 0#8 (by decide)) (by decide)

theorem Peephole.Lemmas.msb_false_of_and_eq_zero.sat :
    ∃ (w : Nat) (x k : BitVec w), x &&& k = 0#w ∧ k.msb = true :=
  ⟨8, 0#8, 128#8, by decide, by decide⟩

theorem Peephole.Lemmas.msb_true_of_and_eq.drop_h :
    ¬ ∀ {w : Nat} {x k : BitVec w}, k.msb = true → x.msb = true :=
  fun h => absurd (@h 8 0#8 128#8 (by decide)) (by decide)

theorem Peephole.Lemmas.msb_true_of_and_eq.drop_hk :
    ¬ ∀ {w : Nat} {x k : BitVec w}, x &&& k = k → x.msb = true :=
  fun h => absurd (@h 8 0#8 0#8 (by decide)) (by decide)

theorem Peephole.Lemmas.msb_true_of_and_eq.sat : ∃ (w : Nat) (x k : BitVec w), x &&& k = k ∧ k.msb = true :=
  ⟨8, 128#8, 128#8, by decide, by decide⟩

/-! ### `or`, `urem`, `lshr`, `udiv` -/

/-- `0 <=s (-128 | 0)` doesn't hold. -/
theorem Peephole.Lemmas.sle_or_right.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w}, BitVec.sle y (x ||| y) = true :=
  fun h => absurd (@h 8 128#8 0#8) (by decide)

theorem Peephole.Lemmas.sle_or_right.sat : ∃ (w : Nat) (x y : BitVec w), y.msb = true ∨ x.msb = false :=
  ⟨8, 0#8, 0#8, Or.inr rfl⟩

/-- `BitVec`'s `1 % 0` is `1`, not below `0`. -/
theorem Peephole.Lemmas.umod_lt.drop_hy : ¬ ∀ {w : Nat} {x y : BitVec w}, BitVec.ult (x % y) y = true :=
  fun h => absurd (@h 8 1#8 0#8) (by decide)

theorem Peephole.Lemmas.umod_lt.sat : ∃ (w : Nat) (_ y : BitVec w), y ≠ 0#w := ⟨8, 0#8, 1#8, by decide⟩

theorem Peephole.Lemmas.umod_slt.drop_hy :
    ¬ ∀ {w : Nat} {x y : BitVec w}, y.msb = false → BitVec.slt (x % y) y = true :=
  fun h => absurd (@h 8 0#8 0#8 (by decide)) (by decide)

/-- `0 % -128` is `0`, not below `-128`. -/
theorem Peephole.Lemmas.umod_slt.drop_hm :
    ¬ ∀ {w : Nat} {x y : BitVec w}, y ≠ 0#w → BitVec.slt (x % y) y = true :=
  fun h => absurd (@h 8 0#8 128#8 (by decide)) (by decide)

theorem Peephole.Lemmas.umod_slt.sat : ∃ (w : Nat) (_ y : BitVec w), y ≠ 0#w ∧ y.msb = false :=
  ⟨8, 0#8, 1#8, by decide, by decide⟩

theorem Peephole.Lemmas.ushiftRight_ult.drop_hx :
    ¬ ∀ {w : Nat} {x c : BitVec w}, c.toNat ≠ 0 → BitVec.ult (x >>> c) x = true :=
  fun h => absurd (@h 8 0#8 1#8 (by decide)) (by decide)

theorem Peephole.Lemmas.ushiftRight_ult.drop_hc :
    ¬ ∀ {w : Nat} {x c : BitVec w}, x ≠ 0#w → BitVec.ult (x >>> c) x = true :=
  fun h => absurd (@h 8 1#8 0#8 (by decide)) (by decide)

theorem Peephole.Lemmas.ushiftRight_ult.sat : ∃ (w : Nat) (x c : BitVec w), x ≠ 0#w ∧ c.toNat ≠ 0 :=
  ⟨8, 1#8, 1#8, by decide, by decide⟩

theorem Peephole.Lemmas.udiv_ult.drop_hx :
    ¬ ∀ {w : Nat} {x c : BitVec w}, c.toNat ≠ 1 → BitVec.ult (x / c) x = true :=
  fun h => absurd (@h 8 0#8 2#8 (by decide)) (by decide)

theorem Peephole.Lemmas.udiv_ult.drop_hc :
    ¬ ∀ {w : Nat} {x c : BitVec w}, x ≠ 0#w → BitVec.ult (x / c) x = true :=
  fun h => absurd (@h 8 1#8 1#8 (by decide)) (by decide)

theorem Peephole.Lemmas.udiv_ult.sat : ∃ (w : Nat) (x c : BitVec w), x ≠ 0#w ∧ c.toNat ≠ 1 :=
  ⟨8, 1#8, 2#8, by decide, by decide⟩

/-- `(1 * 2) udiv 1` is `2`. -/
theorem Peephole.Lemmas.mul_udiv_ule.drop_hc :
    ¬ ∀ {w : Nat} {x c1 c2 : BitVec w}, BitVec.ule (x * c1 / c2) x = true :=
  fun h => absurd (@h 8 1#8 2#8 1#8) (by decide)

theorem Peephole.Lemmas.mul_udiv_ule.sat : ∃ (w : Nat) (_ c1 c2 : BitVec w), BitVec.ule c1 c2 = true :=
  ⟨8, 0#8, 0#8, 0#8, by decide⟩

theorem Peephole.Lemmas.mul_ushiftRight_ule.drop_hc :
    ¬ ∀ {w : Nat} {x c1 c2 : BitVec w}, BitVec.ule ((x * c1) >>> c2) x = true :=
  fun h => absurd (@h 8 1#8 2#8 0#8) (by decide)

theorem Peephole.Lemmas.mul_ushiftRight_ule.sat :
    ∃ (w : Nat) (_ c1 c2 : BitVec w), BitVec.ule c1 (1#w <<< c2) = true :=
  ⟨8, 0#8, 0#8, 0#8, by decide⟩

theorem Peephole.Lemmas.shiftLeft_udiv_ule.drop_hc :
    ¬ ∀ {w : Nat} {x c1 c2 : BitVec w}, BitVec.ule ((x <<< c1) / c2) x = true :=
  fun h => absurd (@h 8 1#8 1#8 1#8) (by decide)

theorem Peephole.Lemmas.shiftLeft_udiv_ule.sat :
    ∃ (w : Nat) (_ c1 c2 : BitVec w), BitVec.ule (1#w <<< c1) c2 = true :=
  ⟨8, 0#8, 0#8, 1#8, by decide⟩

/-- `2 - 1` is `1`. -/
theorem Peephole.Lemmas.sub_ne_of_odd.drop_hc : ¬ ∀ {w : Nat} {c x : BitVec w}, (c - x == x) = false :=
  fun h => absurd (@h 8 2#8 1#8) (by decide)

theorem Peephole.Lemmas.sub_ne_of_odd.sat : ∃ (w : Nat) (c _ : BitVec w), (c &&& 1#w).toNat = 1 :=
  ⟨8, 1#8, 0#8, by decide⟩

/-! ### `simplifyICmpWithBinOp` -/

/-- A "zext" that doesn't widen: `0 - 200` is `56` in `i8`. -/
theorem Peephole.Lemmas.toInt_zero_sub_setWidth.drop_h :
    ¬ ∀ {w v : Nat} (x : BitVec v), (0#w - x.setWidth w).toInt = -(x.toNat : Int) :=
  fun h => absurd (@h 8 8 200#8) (by decide)

theorem Peephole.Lemmas.toInt_zero_sub_setWidth.sat : ∃ (w v : Nat) (_ : BitVec v), v < w :=
  ⟨8, 1, 0#1, by decide⟩

theorem Peephole.Lemmas.zero_sub_setWidth_sle.drop_h :
    ¬ ∀ {w v : Nat} (x : BitVec v) {c : BitVec w}, c.msb = false → BitVec.sle (0#w - x.setWidth w) c = true :=
  fun h => absurd (@h 8 8 200#8 0#8 (by decide)) (by decide)

theorem Peephole.Lemmas.zero_sub_setWidth_sle.drop_hc :
    ¬ ∀ {w v : Nat} (x : BitVec v), v < w → ∀ {c : BitVec w}, BitVec.sle (0#w - x.setWidth w) c = true :=
  fun h => absurd (@h 8 1 0#1 (by decide) 128#8) (by decide)

theorem Peephole.Lemmas.zero_sub_setWidth_sle.sat :
    ∃ (w v : Nat) (_ : BitVec v) (c : BitVec w), v < w ∧ c.msb = false :=
  ⟨8, 1, 0#1, 0#8, by decide, by decide⟩

theorem Peephole.Lemmas.zero_sub_setWidth_slt.drop_h :
    ¬ ∀ {w v : Nat} (x : BitVec v) {c : BitVec w}, c.msb = false → c.toNat ≠ 0 →
      BitVec.slt (0#w - x.setWidth w) c = true :=
  fun h => absurd (@h 8 8 200#8 1#8 (by decide) (by decide)) (by decide)

theorem Peephole.Lemmas.zero_sub_setWidth_slt.drop_hc :
    ¬ ∀ {w v : Nat} (x : BitVec v), v < w → ∀ {c : BitVec w}, c.toNat ≠ 0 →
      BitVec.slt (0#w - x.setWidth w) c = true :=
  fun h => absurd (@h 8 1 0#1 (by decide) 128#8 (by decide)) (by decide)

theorem Peephole.Lemmas.zero_sub_setWidth_slt.drop_hc0 :
    ¬ ∀ {w v : Nat} (x : BitVec v), v < w → ∀ {c : BitVec w}, c.msb = false →
      BitVec.slt (0#w - x.setWidth w) c = true :=
  fun h => absurd (@h 8 1 0#1 (by decide) 0#8 (by decide)) (by decide)

theorem Peephole.Lemmas.zero_sub_setWidth_slt.sat :
    ∃ (w v : Nat) (_ : BitVec v) (c : BitVec w), v < w ∧ c.msb = false ∧ c.toNat ≠ 0 :=
  ⟨8, 1, 0#1, 1#8, by decide, by decide, by decide⟩

/-- `3 << 0` is `3`, which is neither a power of two nor zero, and more than half of `256`. -/
theorem Peephole.Lemmas.shiftLeft_pow2.drop_hc :
    ¬ ∀ {w : Nat} {c : BitVec w} (s : Nat),
      ((c <<< s).toNat = 0 ∨ (c <<< s).toNat.isPowerOfTwo) ∧ 2 * (c <<< s).toNat ≤ 2 ^ w :=
  fun h => absurd (@h 8 255#8 0).2 (by decide)

theorem Peephole.Lemmas.shiftLeft_pow2.sat : ∃ (w : Nat) (c : BitVec w) (_ : Nat), c.toNat.isPowerOfTwo :=
  ⟨8, 1#8, 0, ⟨0, rfl⟩⟩

theorem Peephole.Lemmas.shiftLeft_pow2_ne.drop_h2 :
    ¬ ∀ {w : Nat} {c2 c : BitVec w} (s : Nat), ¬ c.toNat.isPowerOfTwo → (c2 <<< s ≠ 0#w ∨ c ≠ 0#w) →
      (c2 <<< s == c) = false :=
  fun h => absurd (@h 8 3#8 3#8 0 not_pow2_three (Or.inr (by decide))) (by decide)

theorem Peephole.Lemmas.shiftLeft_pow2_ne.drop_hc :
    ¬ ∀ {w : Nat} {c2 c : BitVec w} (s : Nat), c2.toNat.isPowerOfTwo → (c2 <<< s ≠ 0#w ∨ c ≠ 0#w) →
      (c2 <<< s == c) = false :=
  fun h => absurd (@h 8 1#8 1#8 0 ⟨0, rfl⟩ (Or.inl (by decide))) (by decide)

/-- `128 << 1` is `0` in `i8`, and so is `c`. -/
theorem Peephole.Lemmas.shiftLeft_pow2_ne.drop_hz :
    ¬ ∀ {w : Nat} {c2 c : BitVec w} (s : Nat), c2.toNat.isPowerOfTwo → ¬ c.toNat.isPowerOfTwo →
      (c2 <<< s == c) = false :=
  fun h => absurd (@h 8 128#8 0#8 1 ⟨7, rfl⟩ not_pow2_zero) (by decide)

theorem Peephole.Lemmas.shiftLeft_pow2_ne.sat :
    ∃ (w : Nat) (c2 c : BitVec w) (s : Nat),
      c2.toNat.isPowerOfTwo ∧ ¬ c.toNat.isPowerOfTwo ∧ (c2 <<< s ≠ 0#w ∨ c ≠ 0#w) :=
  ⟨8, 1#8, 3#8, 0, ⟨0, rfl⟩, not_pow2_three, Or.inl (by decide)⟩

theorem Peephole.Lemmas.shiftLeft_pow2_ule_intMin.drop_hc :
    ¬ ∀ {w : Nat} {c : BitVec w} (s : Nat), BitVec.ule (c <<< s) (BitVec.intMin w) = true :=
  fun h => absurd (@h 8 255#8 0) (by decide)

theorem Peephole.Lemmas.shiftLeft_pow2_ule_intMin.sat :
    ∃ (w : Nat) (c : BitVec w) (_ : Nat), c.toNat.isPowerOfTwo :=
  ⟨8, 1#8, 0, ⟨0, rfl⟩⟩

theorem Peephole.Lemmas.ule_of_subset.drop_h : ¬ ∀ {w : Nat} {a b : BitVec w}, BitVec.ule a b = true :=
  fun h => absurd (@h 8 1#8 0#8) (by decide)

theorem Peephole.Lemmas.ule_of_subset.sat : ∃ (w : Nat) (a b : BitVec w), a &&& ~~~b = 0#w :=
  ⟨8, 0#8, 0#8, by decide⟩

theorem Peephole.Lemmas.and_subset.drop_h :
    ¬ ∀ {w : Nat} {x c1 c2 : BitVec w}, (x &&& c1) &&& ~~~(x &&& c2) = 0#w :=
  fun h => absurd (@h 8 1#8 1#8 0#8) (by decide)

theorem Peephole.Lemmas.and_subset.sat : ∃ (w : Nat) (_ c1 c2 : BitVec w), c1 &&& ~~~c2 = 0#w :=
  ⟨8, 0#8, 0#8, 0#8, by decide⟩

theorem Peephole.Lemmas.or_subset.drop_h :
    ¬ ∀ {w : Nat} {x c1 c2 : BitVec w}, (x ||| c1) &&& ~~~(x ||| c2) = 0#w :=
  fun h => absurd (@h 8 0#8 1#8 0#8) (by decide)

theorem Peephole.Lemmas.or_subset.sat : ∃ (w : Nat) (_ c1 c2 : BitVec w), c1 &&& ~~~c2 = 0#w :=
  ⟨8, 0#8, 0#8, 0#8, by decide⟩

/-! ### Min and max -/

/-- `smin(1, 1)` is above `smax(0, 0)`. -/
theorem Peephole.Lemmas.smin_sle_smax.drop_h :
    ¬ ∀ {w : Nat} {a b c d : BitVec w},
      BitVec.sle (if c.sle d then c else d) (if a.sle b then b else a) = true :=
  fun h => absurd (@h 8 0#8 0#8 1#8 1#8) (by decide)

theorem Peephole.Lemmas.smin_sle_smax.sat :
    ∃ (w : Nat) (a b c d : BitVec w), c = a ∨ d = a ∨ c = b ∨ d = b :=
  ⟨8, 0#8, 0#8, 0#8, 0#8, Or.inl rfl⟩

theorem Peephole.Lemmas.umin_ule_umax.drop_h :
    ¬ ∀ {w : Nat} {a b c d : BitVec w},
      BitVec.ule (if c.ule d then c else d) (if a.ule b then b else a) = true :=
  fun h => absurd (@h 8 0#8 0#8 1#8 1#8) (by decide)

theorem Peephole.Lemmas.umin_ule_umax.sat :
    ∃ (w : Nat) (a b c d : BitVec w), c = a ∨ d = a ∨ c = b ∨ d = b :=
  ⟨8, 0#8, 0#8, 0#8, 0#8, Or.inl rfl⟩

/-! ### Compares of `X + C0` and `X` -/

theorem Peephole.Lemmas.toNat_ofNat_small.drop_hw :
    ¬ ∀ {w k : Nat}, k ≤ 2 → (BitVec.ofNat w k).toNat = k :=
  fun h => absurd (@h 1 2 (by decide)) (by decide)

theorem Peephole.Lemmas.toNat_ofNat_small.drop_hk :
    ¬ ∀ {w k : Nat}, 2 ≤ w → (BitVec.ofNat w k).toNat = k :=
  fun h => absurd (@h 2 4 (by decide)) (by decide)

theorem Peephole.Lemmas.toNat_ofNat_small.sat : ∃ (w k : Nat), 2 ≤ w ∧ k ≤ 2 := ⟨2, 0, by decide, by decide⟩

theorem Peephole.Lemmas.two_le_of_toInt_pos.drop_h : ¬ ∀ {w : Nat} {_ : BitVec w}, 2 ≤ w :=
  fun h => absurd (@h 0 0#0) (by decide)

theorem Peephole.Lemmas.two_le_of_toInt_pos.sat : ∃ (w : Nat) (c : BitVec w), 0 < c.toInt := ⟨8, 1#8, by decide⟩

/-- `c0 = 0` and `v = 1`: `1 <u 2` and `0 <s 1`. -/
theorem Peephole.Lemmas.ult_add_two_and_sgt.drop_hc :
    ¬ ∀ {w : Nat} {v c0 : BitVec w}, (BitVec.ult (v + c0) (c0 + 2#w) && BitVec.slt c0 v) = false :=
  fun h => absurd (@h 8 1#8 0#8) (by decide)

theorem Peephole.Lemmas.ult_add_two_and_sgt.sat : ∃ (w : Nat) (_ c0 : BitVec w), 0 < c0.toInt :=
  ⟨8, 0#8, 1#8, by decide⟩

theorem Peephole.Lemmas.slt_add_two_and_sgt.drop_hc :
    ¬ ∀ {w : Nat} {v c0 : BitVec w}, v.saddOverflow c0 = false →
      (BitVec.slt (v + c0) (c0 + 2#w) && BitVec.slt c0 v) = false :=
  fun h => absurd (@h 8 1#8 0#8 (by decide)) (by decide)

/-- `127 + 1` wraps to `-128`, below `3`. -/
theorem Peephole.Lemmas.slt_add_two_and_sgt.drop_hn :
    ¬ ∀ {w : Nat} {v c0 : BitVec w}, 0 < c0.toInt →
      (BitVec.slt (v + c0) (c0 + 2#w) && BitVec.slt c0 v) = false :=
  fun h => absurd (@h 8 127#8 1#8 (by decide)) (by decide)

theorem Peephole.Lemmas.slt_add_two_and_sgt.sat :
    ∃ (w : Nat) (v c0 : BitVec w), 0 < c0.toInt ∧ v.saddOverflow c0 = false :=
  ⟨8, 0#8, 1#8, by decide, by decide⟩

theorem Peephole.Lemmas.ule_add_one_and_sgt.drop_hc :
    ¬ ∀ {w : Nat} {v c0 : BitVec w}, (BitVec.ule (v + c0) (c0 + 1#w) && BitVec.slt c0 v) = false :=
  fun h => absurd (@h 8 1#8 0#8) (by decide)

theorem Peephole.Lemmas.ule_add_one_and_sgt.sat : ∃ (w : Nat) (_ c0 : BitVec w), 0 < c0.toInt :=
  ⟨8, 0#8, 1#8, by decide⟩

theorem Peephole.Lemmas.sle_add_one_and_sgt.drop_hc :
    ¬ ∀ {w : Nat} {v c0 : BitVec w}, v.saddOverflow c0 = false →
      (BitVec.sle (v + c0) (c0 + 1#w) && BitVec.slt c0 v) = false :=
  fun h => absurd (@h 8 1#8 0#8 (by decide)) (by decide)

theorem Peephole.Lemmas.sle_add_one_and_sgt.drop_hn :
    ¬ ∀ {w : Nat} {v c0 : BitVec w}, 0 < c0.toInt →
      (BitVec.sle (v + c0) (c0 + 1#w) && BitVec.slt c0 v) = false :=
  fun h => absurd (@h 8 127#8 1#8 (by decide)) (by decide)

theorem Peephole.Lemmas.sle_add_one_and_sgt.sat :
    ∃ (w : Nat) (v c0 : BitVec w), 0 < c0.toInt ∧ v.saddOverflow c0 = false :=
  ⟨8, 0#8, 1#8, by decide, by decide⟩

theorem Peephole.Lemmas.ult_add_two_and_ugt.drop_hc :
    ¬ ∀ {w : Nat} {v c0 : BitVec w}, v.uaddOverflow c0 = false →
      (BitVec.ult (v + c0) (c0 + 2#w) && BitVec.ult c0 v) = false :=
  fun h => absurd (@h 8 1#8 0#8 (by decide)) (by decide)

/-- `255 + 1` wraps to `0`, below `3`. -/
theorem Peephole.Lemmas.ult_add_two_and_ugt.drop_hn :
    ¬ ∀ {w : Nat} {v c0 : BitVec w}, c0 ≠ 0#w →
      (BitVec.ult (v + c0) (c0 + 2#w) && BitVec.ult c0 v) = false :=
  fun h => absurd (@h 8 255#8 1#8 (by decide)) (by decide)

theorem Peephole.Lemmas.ult_add_two_and_ugt.sat :
    ∃ (w : Nat) (v c0 : BitVec w), c0 ≠ 0#w ∧ v.uaddOverflow c0 = false :=
  ⟨8, 0#8, 1#8, by decide, by decide⟩

theorem Peephole.Lemmas.ule_add_one_and_ugt.drop_hc :
    ¬ ∀ {w : Nat} {v c0 : BitVec w}, v.uaddOverflow c0 = false →
      (BitVec.ule (v + c0) (c0 + 1#w) && BitVec.ult c0 v) = false :=
  fun h => absurd (@h 8 1#8 0#8 (by decide)) (by decide)

theorem Peephole.Lemmas.ule_add_one_and_ugt.drop_hn :
    ¬ ∀ {w : Nat} {v c0 : BitVec w}, c0 ≠ 0#w →
      (BitVec.ule (v + c0) (c0 + 1#w) && BitVec.ult c0 v) = false :=
  fun h => absurd (@h 8 255#8 1#8 (by decide)) (by decide)

theorem Peephole.Lemmas.ule_add_one_and_ugt.sat :
    ∃ (w : Nat) (v c0 : BitVec w), c0 ≠ 0#w ∧ v.uaddOverflow c0 = false :=
  ⟨8, 0#8, 1#8, by decide, by decide⟩

/-! ### A `select` against a min or max -/

theorem Peephole.Lemmas.smax_of_sle.drop_h : ¬ ∀ {w : Nat} {x y : BitVec w}, (if x.sle y then y else x) = x :=
  fun h => absurd (@h 8 0#8 1#8) (by decide)

theorem Peephole.Lemmas.smax_of_sle.sat : ∃ (w : Nat) (x y : BitVec w), BitVec.sle y x = true :=
  ⟨8, 0#8, 0#8, by decide⟩

theorem Peephole.Lemmas.smin_of_sle.drop_h : ¬ ∀ {w : Nat} {x y : BitVec w}, (if x.sle y then x else y) = x :=
  fun h => absurd (@h 8 1#8 0#8) (by decide)

theorem Peephole.Lemmas.smin_of_sle.sat : ∃ (w : Nat) (x y : BitVec w), BitVec.sle x y = true :=
  ⟨8, 0#8, 0#8, by decide⟩

theorem Peephole.Lemmas.umax_of_ule.drop_h : ¬ ∀ {w : Nat} {x y : BitVec w}, (if x.ule y then y else x) = x :=
  fun h => absurd (@h 8 0#8 1#8) (by decide)

theorem Peephole.Lemmas.umax_of_ule.sat : ∃ (w : Nat) (x y : BitVec w), BitVec.ule y x = true :=
  ⟨8, 0#8, 0#8, by decide⟩

theorem Peephole.Lemmas.umin_of_ule.drop_h : ¬ ∀ {w : Nat} {x y : BitVec w}, (if x.ule y then x else y) = x :=
  fun h => absurd (@h 8 1#8 0#8) (by decide)

theorem Peephole.Lemmas.umin_of_ule.sat : ∃ (w : Nat) (x y : BitVec w), BitVec.ule x y = true :=
  ⟨8, 0#8, 0#8, by decide⟩

end LemmaStore.Counter
