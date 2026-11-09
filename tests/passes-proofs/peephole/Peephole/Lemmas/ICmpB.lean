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

/-- `x udiv c <u x` for `x ≠ 0` and `c` not 0 or 1. `IS.simplifyICmpWithBinOpOnLHS.L3295`. -/
theorem udiv_ult {x c : BitVec w} (hx : x ≠ 0#w) (hc0 : c ≠ 0#w) (hc : c.toNat ≠ 1) :
    BitVec.ult (x / c) x = true := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_udiv]
  have h0 : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simpa using h))
  have h1 : c.toNat ≠ 0 := fun h => hc0 (BitVec.eq_of_toNat_eq (by simpa using h))
  exact Nat.div_lt_self (by omega) (by omega)

/-- `(x * c1) udiv c2 <=u x` for `c1 <=u c2`, even if the product wraps. `IS.simplifyICmpWithBinOpOnLHS.L3321`. -/
theorem mul_udiv_ule {x c1 c2 : BitVec w} (hc : BitVec.ule c1 c2 = true) :
    BitVec.ule (x * c1 / c2) x = true := by
  simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_udiv, BitVec.toNat_mul] at hc ⊢
  apply Nat.div_le_of_le_mul
  calc x.toNat * c1.toNat % 2 ^ w ≤ x.toNat * c1.toNat := Nat.mod_le _ _
    _ ≤ x.toNat * c2.toNat := Nat.mul_le_mul_left _ hc
    _ = c2.toNat * x.toNat := Nat.mul_comm _ _

/-- `(x * c1) >>u c2 <=u x` for `c1 <=u 1 << c2` and `c2 < w`. `IS.simplifyICmpWithBinOpOnLHS.L3321`. -/
theorem mul_ushiftRight_ule {x c1 c2 : BitVec w} (h2 : c2.toNat < w)
    (hc : BitVec.ule c1 (1#w <<< c2) = true) : BitVec.ule ((x * c1) >>> c2) x = true := by
  simp only [BitVec.ule, decide_eq_true_eq, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq] at hc ⊢
  have hw : 0 < w := by omega
  have h1 : (1#w).toNat = 1 := by simp [Nat.one_mod_two_pow hw]
  rw [h1, Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h2)] at hc
  apply Nat.div_le_of_le_mul
  calc x.toNat * c1.toNat % 2 ^ w ≤ x.toNat * c1.toNat := Nat.mod_le _ _
    _ ≤ x.toNat * 2 ^ c2.toNat := Nat.mul_le_mul_left _ hc
    _ = 2 ^ c2.toNat * x.toNat := Nat.mul_comm _ _

/-- `(x << c1) udiv c2 <=u x` for `1 << c1 <=u c2` and `c1 < w`. `IS.simplifyICmpWithBinOpOnLHS.L3321`. -/
theorem shiftLeft_udiv_ule {x c1 c2 : BitVec w} (h1 : c1.toNat < w)
    (hc : BitVec.ule (1#w <<< c1) c2 = true) : BitVec.ule ((x <<< c1) / c2) x = true := by
  simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_udiv, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq] at hc ⊢
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

theorem toInt_inj' {a b : BitVec w} : a.toInt = b.toInt ↔ a = b := BitVec.toInt_inj

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

end Peephole.Lemmas

