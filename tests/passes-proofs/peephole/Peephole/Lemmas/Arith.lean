import IRLean.Int
import IRLean.Refine
import IRLean.Generic.Arith
import Peephole.IS.ArithBase

/-! # Facts about `sub`, `mul` and the divisions, at every width, that InstSimplify's rewrites of them rest on

Each is about values, not about LLVM's code: a candidate for the lemma store. The rewrite each one was cut from is
named in its docstring. A division's result is an `Outcome`: dividing by zero or poison, and the signed division of the
minimum by `-1`, are undefined, and an undefined source allows any replacement. For each hypothesis, the end of the
file shows the lemma is false without it. -/

namespace Peephole.Lemmas

open IRLean Peephole.IS.Arith

variable {w : Nat}

/-! ### `sub` -/

/-- `sub nuw 0, x` refines `0`: it's poison unless `x` is `0`. `IS.simplifySubInst.L773`. -/
theorem sub_zero_left_nuw_refines (b : Val w) (nsw : Bool) : Refines (Val.sub (some 0#w) b true nsw) (some 0#w) := by
  cases b with
  | none => exact Refine.val_none _
  | some y =>
    by_cases hy : y = 0#w
    · subst hy; exact Generic.sub_self_refines (some 0#w) true nsw
    · have : (0#w).usubOverflow y = true := by
        simp only [BitVec.usubOverflow, BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_true_eq]
        exact Nat.pos_of_ne_zero fun h => hy (BitVec.eq_of_toNat_eq (by simp [h]))
      simp [Val.sub, this, Refines, Refine.le]

/-- `sub nsw 0, x` refines `0` where `x` has no bit below the sign bit: it's `0`, or the negated minimum, which
overflows. `IS.simplifySubInst.L780`. -/
theorem sub_zero_left_nsw_refines {y : BitVec w} (h : y &&& BitVec.intMax w = 0#w) (nuw : Bool) :
    Refines (Val.sub (some 0#w) (some y) nuw true) (some 0#w) := by
  rcases eq_zero_or_intMin_of_and_intMax h with rfl | rfl
  · exact Generic.sub_self_refines (some 0#w) nuw true
  · rcases Nat.eq_zero_or_pos w with rfl | hw
    · exact Generic.sub_self_refines (some 0#0) nuw true
    · have : (0#w).ssubOverflow (BitVec.intMin w) = true := by
        simp only [BitVec.ssubOverflow, BitVec.toInt_zero, BitVec.toInt_intMin_of_pos hw, Bool.or_eq_true,
          decide_eq_true_eq]
        omega
      simp [Val.sub, this, Refines, Refine.le]

/-- `sub 0, x` refines `x` where `x` has no bit below the sign bit: `0` and the minimum are their own negations.
`IS.simplifySubInst.L783`. -/
theorem sub_zero_left_refines_self {y : BitVec w} (h : y &&& BitVec.intMax w = 0#w) (nuw nsw : Bool) :
    Refines (Val.sub (some 0#w) (some y) nuw nsw) (some y) := by
  have hneg : 0#w - y = y := by
    rcases eq_zero_or_intMin_of_and_intMax h with rfl | rfl
    · exact BitVec.sub_self _
    · rw [BitVec.zero_sub, BitVec.neg_intMin]
  simp only [Val.sub, hneg]
  split
  · exact Refine.val_none _
  · exact Refine.refl_val _

/-- A low-bit mask `c`, `2 ^ k - 1`, is `(c + 1) & c = 0`: what `APInt::isMask` tests, without its `c ≠ 0`. -/
private theorem mask_toNat {c : BitVec w} (hc : (c + 1#w) &&& c = 0#w) : ∃ k, c.toNat = 2 ^ k - 1 := by
  by_cases ha : c.toNat + 1 = 2 ^ w
  · exact ⟨w, by omega⟩
  · have hlt : c.toNat + 1 < 2 ^ w := by have := c.isLt; omega
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · exact ⟨0, by have := c.isLt; simp at this ⊢; omega⟩
    have h1 : (c + 1#w).toNat = c.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_one hw, Nat.mod_eq_of_lt hlt]
    have hn := congrArg BitVec.toNat hc
    rw [BitVec.toNat_and, h1, BitVec.toNat_ofNat, Nat.zero_mod] at hn
    have hp : (c.toNat + 1).isPowerOfTwo := by
      apply (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).1
      simpa using hn
    obtain ⟨k, hk⟩ := hp
    exact ⟨k, by omega⟩

/-- Below a low-bit mask, a value is inside it. -/
private theorem and_mask_of_le {c z : BitVec w} (hc : (c + 1#w) &&& c = 0#w) (hz : z.toNat ≤ c.toNat) :
    z &&& c = z := by
  obtain ⟨k, hk⟩ := mask_toNat hc
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, hk, Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.mod_eq_of_lt
  have : 0 < 2 ^ k := Nat.two_pow_pos k
  omega

/-- `sub nuw c, (x ^ c)` refines `x` for a low-bit mask `c`: where `x` is inside the mask, `x ^ c` is `c - x`, and
anywhere else `x ^ c` is above `c`, so the subtraction wraps. `IS.simplifySubInst.L886`. -/
theorem sub_mask_xor_nuw_refines (a : Val w) {c : BitVec w} (hc : (c + 1#w) &&& c = 0#w) (nsw : Bool) :
    Refines (Val.sub (some c) (Val.xor a (some c)) true nsw) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    simp only [Val.xor, Val.map₂, Val.sub, Bool.true_and]
    split
    · exact Refine.val_none _
    · next hov =>
      have hle : (x ^^^ c).toNat ≤ c.toNat := by
        simp only [Bool.or_eq_true, not_or, BitVec.usubOverflow, decide_eq_true_eq] at hov
        omega
      have hin := and_mask_of_le hc hle
      -- `x ^ c` and `c ^ (x ^ c)`, which is `x`, are disjoint, and make `c` between them.
      have hdis : (x ^^^ c) &&& x = 0#w := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have := congrArg (·.getLsbD i) hin
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor] at this
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_zero]
        revert this
        cases x.getLsbD i <;> cases c.getLsbD i <;> simp
      have hor : (x ^^^ c) ||| x = c := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have := congrArg (·.getLsbD i) hin
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor] at this
        simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor]
        revert this
        cases x.getLsbD i <;> cases c.getLsbD i <;> simp
      have hsum : (x ^^^ c) + x = c := by rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdis, hor]
      have : c - (x ^^^ c) = x := by
        have e : (x ^^^ c) + x - (x ^^^ c) = x := by rw [BitVec.add_comm, BitVec.add_sub_cancel]
        rwa [hsum] at e
      rw [this]
      exact Refine.refl_val _

/-! ### `mul` -/

theorem mul_comm (a b : Val w) (nuw nsw : Bool) : Val.mul a b nuw nsw = Val.mul b a nuw nsw := by
  cases a <;> cases b <;> simp only [Val.mul]
  rename_i x y
  have hu : x.umulOverflow y = y.umulOverflow x := by simp [BitVec.umulOverflow, Nat.mul_comm]
  have hs : x.smulOverflow y = y.smulOverflow x := by simp [BitVec.smulOverflow, Int.mul_comm]
  rw [hu, hs, BitVec.mul_comm]

/-- `(a udiv exact b) * b` refines `a`: an exact quotient times the divisor is the dividend.
`IS.simplifyMulInst.L923`. -/
theorem mul_udiv_exact_refines {a b q : Val w} (h : Val.udiv a b true = Outcome.ok q) (nuw nsw : Bool) :
    Refines (Val.mul q b nuw nsw) a := by
  obtain ⟨y, rfl, hy, hq⟩ := udiv_ok h
  rcases hq with rfl | ⟨p, rfl, hex, rfl⟩
  · exact Refine.val_none _
  · have hd : y.toNat ∣ p.toNat := Nat.dvd_of_mod_eq_zero (by
      have := congrArg BitVec.toNat (hex rfl)
      simpa [BitVec.toNat_umod] using this)
    have : p / y * y = p := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, BitVec.toNat_udiv, Nat.div_mul_cancel hd, Nat.mod_eq_of_lt p.isLt]
    simp only [Val.mul, this]
    split
    · exact Refine.val_none _
    · exact Refine.refl_val _

/-- `(a sdiv exact b) * b` refines `a`. `IS.simplifyMulInst.L923`. -/
theorem mul_sdiv_exact_refines {a b q : Val w} (h : Val.sdiv a b true = Outcome.ok q) (nuw nsw : Bool) :
    Refines (Val.mul q b nuw nsw) a := by
  obtain ⟨y, rfl, hy, hq⟩ := sdiv_ok h
  rcases hq with rfl | ⟨p, rfl, ho, hex, rfl⟩
  · exact Refine.val_none _
  · have hm : (p.toInt.tmod y.toInt) = 0 := by
      rw [← BitVec.toInt_srem, hex rfl, BitVec.toInt_zero]
    have : p.sdiv y * y = p := by
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_mul, toInt_sdiv_of hy ho, Int.tdiv_mul_cancel_of_tmod_eq_zero hm,
        BitVec.toInt_bmod_cancel]
    simp only [Val.mul, this]
    split
    · exact Refine.val_none _
    · exact Refine.refl_val _

/-- `mul nsw` in `i1` refines `0`: `-1 * -1` overflows, and every other product is `0`. `IS.simplifyMulInst.L929`. -/
theorem mul_nsw_one_bit_refines (a b : Val 1) (nuw : Bool) : Refines (Val.mul a b nuw true) (some 0#1) := by
  refine (Refine.val_iff _ _).2 ?_
  cases a with
  | none => exact .inl rfl
  | some x =>
    cases b with
    | none => exact .inl rfl
    | some y => revert x y; cases nuw <;> decide

/-! ### Division of a value by itself, and of zero -/

/-- `udiv x, x` refines `1`. `IS.simplifyDivRem.L1083`. -/
theorem udiv_self_refines (a : Val w) (exact : Bool) : Refines (Val.udiv a a exact) (Outcome.ok (some 1#w)) := by
  cases a with
  | none => exact udiv_none_left _ _ _
  | some x => exact udiv_refines_of exact fun hx => by rw [BitVec.udiv_self]; simp [hx]

/-- `urem x, x` refines `0`. `IS.simplifyDivRem.L1083`. -/
theorem urem_self_refines (a : Val w) : Refines (Val.urem a a) (Outcome.ok (some 0#w)) := by
  cases a with
  | none => exact urem_none_left _ _
  | some x => exact urem_refines_of fun _ => by rw [BitVec.umod_self]

/-- `sdiv x, x` refines `1`. `IS.simplifyDivRem.L1083`. -/
theorem sdiv_self_refines (a : Val w) (exact : Bool) : Refines (Val.sdiv a a exact) (Outcome.ok (some 1#w)) := by
  cases a with
  | none => exact sdiv_none_left _ _ _
  | some x => exact sdiv_refines_of exact fun hx _ => by rw [BitVec.sdiv_self]; simp [hx]

/-- `srem x, x` refines `0`. `IS.simplifyDivRem.L1083`. -/
theorem srem_self_refines (a : Val w) : Refines (Val.srem a a) (Outcome.ok (some 0#w)) := by
  cases a with
  | none => exact srem_none_left _ _
  | some x => exact srem_refines_of fun _ _ => by rw [BitVec.srem_self]

/-- `udiv 0, x` refines `0`. `IS.simplifyDivRem.L1078`. -/
theorem udiv_zero_left_refines (b : Val w) (exact : Bool) :
    Refines (Val.udiv (some 0#w) b exact) (Outcome.ok (some 0#w)) := by
  cases b with
  | none => exact udiv_none_right _ _ _
  | some y => exact udiv_refines_of exact fun _ => by rw [BitVec.zero_udiv]

/-- `urem 0, x` refines `0`. `IS.simplifyDivRem.L1078`. -/
theorem urem_zero_left_refines (b : Val w) : Refines (Val.urem (some 0#w) b) (Outcome.ok (some 0#w)) := by
  cases b with
  | none => exact urem_none_right _ _
  | some y => exact urem_refines_of fun _ => by rw [BitVec.zero_umod]

/-- `sdiv 0, x` refines `0`. `IS.simplifyDivRem.L1078`. -/
theorem sdiv_zero_left_refines (b : Val w) (exact : Bool) :
    Refines (Val.sdiv (some 0#w) b exact) (Outcome.ok (some 0#w)) := by
  cases b with
  | none => exact sdiv_none_right _ _ _
  | some y => exact sdiv_refines_of exact fun _ _ => by rw [BitVec.zero_sdiv]

/-- `srem 0, x` refines `0`. `IS.simplifyDivRem.L1078`. -/
theorem srem_zero_left_refines (b : Val w) : Refines (Val.srem (some 0#w) b) (Outcome.ok (some 0#w)) := by
  cases b with
  | none => exact srem_none_right _ _
  | some y => exact srem_refines_of fun _ _ => by rw [BitVec.zero_srem]

/-! ### A product divided by one of its factors -/

/-- `udiv (mul nuw x, y), y` refines `x`. `IS.simplifyDivRem.L1114`. -/
theorem udiv_mul_nuw_refines (a b : Val w) (nsw exact : Bool) :
    Refines (Val.udiv (Val.mul a b true nsw) b exact) (Outcome.ok a) := by
  cases b with
  | none => exact udiv_none_right _ _ _
  | some y =>
  cases a with
  | none => exact udiv_none_left _ _ _
  | some x =>
  simp only [Val.mul, Bool.true_and]
  split
  · exact udiv_none_left _ _ _
  · next hov =>
    have hu : x.umulOverflow y = false := by revert hov; cases x.umulOverflow y <;> simp
    refine udiv_refines_of exact fun hy => ?_
    have hy0 : 0 < y.toNat := Nat.pos_of_ne_zero fun h => hy (BitVec.eq_of_toNat_eq (by simp [h]))
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, BitVec.toNat_mul_of_not_umulOverflow (by simp [hu]), Nat.mul_div_cancel _ hy0]

/-- `urem (mul nuw x, y), y` refines `0`. `IS.simplifyDivRem.L1114`. -/
theorem urem_mul_nuw_refines (a b : Val w) (nsw : Bool) :
    Refines (Val.urem (Val.mul a b true nsw) b) (Outcome.ok (some 0#w)) := by
  cases b with
  | none => exact urem_none_right _ _
  | some y =>
  cases a with
  | none => exact urem_none_left _ _
  | some x =>
  simp only [Val.mul, Bool.true_and]
  split
  · exact urem_none_left _ _
  · next hov =>
    have hu : x.umulOverflow y = false := by revert hov; cases x.umulOverflow y <;> simp
    refine urem_refines_of fun _ => ?_
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod, BitVec.toNat_mul_of_not_umulOverflow (by simp [hu]), Nat.mul_mod_left]
    simp

/-- `sdiv (mul nsw x, y), y` refines `x`. `IS.simplifyDivRem.L1114`. -/
theorem sdiv_mul_nsw_refines (a b : Val w) (nuw exact : Bool) :
    Refines (Val.sdiv (Val.mul a b nuw true) b exact) (Outcome.ok a) := by
  cases b with
  | none => exact sdiv_none_right _ _ _
  | some y =>
  cases a with
  | none => exact sdiv_none_left _ _ _
  | some x =>
  simp only [Val.mul, Bool.true_and]
  split
  · exact sdiv_none_left _ _ _
  · next hov =>
    have hs : x.smulOverflow y = false := by
      revert hov; cases nuw <;> cases x.umulOverflow y <;> cases x.smulOverflow y <;> simp
    refine sdiv_refines_of exact fun hy ho => ?_
    congr 1
    apply BitVec.eq_of_toInt_eq
    rw [toInt_sdiv_of hy ho, BitVec.toInt_mul_of_not_smulOverflow (by simp [hs]),
      Int.mul_tdiv_cancel _ (toInt_ne_zero hy)]

/-- `srem (mul nsw x, y), y` refines `0`. `IS.simplifyDivRem.L1114`. -/
theorem srem_mul_nsw_refines (a b : Val w) (nuw : Bool) :
    Refines (Val.srem (Val.mul a b nuw true) b) (Outcome.ok (some 0#w)) := by
  cases b with
  | none => exact srem_none_right _ _
  | some y =>
  cases a with
  | none => exact srem_none_left _ _
  | some x =>
  simp only [Val.mul, Bool.true_and]
  split
  · exact srem_none_left _ _
  · next hov =>
    have hs : x.smulOverflow y = false := by
      revert hov; cases nuw <;> cases x.umulOverflow y <;> cases x.smulOverflow y <;> simp
    refine srem_refines_of fun _ _ => ?_
    congr 1
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_srem, BitVec.toInt_mul_of_not_smulOverflow (by simp [hs]), Int.mul_tmod_left,
      BitVec.toInt_zero]

/-- `udiv (mul (udiv a, y), y), y` refines `udiv a, y`: the quotient times the divisor is at most the dividend, so it
doesn't wrap. `IS.simplifyDivRem.L1114`. -/
theorem udiv_mul_udiv_refines {a b x : Val w} {e : Bool} (h : Val.udiv a b e = Outcome.ok x) (nuw nsw e' : Bool) :
    Refines (Val.udiv (Val.mul x b nuw nsw) b e') (Outcome.ok x) := by
  obtain ⟨y, rfl, hy, hx⟩ := udiv_ok h
  rcases hx with rfl | ⟨p, rfl, -, rfl⟩
  · exact udiv_none_left _ _ _
  · simp only [Val.mul]
    split
    · exact udiv_none_left _ _ _
    · refine udiv_refines_of e' fun _ => ?_
      have hy0 : 0 < y.toNat := Nat.pos_of_ne_zero fun h => hy (BitVec.eq_of_toNat_eq (by simp [h]))
      have hle : p.toNat / y.toNat * y.toNat < 2 ^ w :=
        Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) p.isLt
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_udiv, BitVec.toNat_mul]
      rw [Nat.mod_eq_of_lt hle, Nat.mul_div_cancel _ hy0]

/-- `urem (mul (udiv a, y), y), y` refines `0`. `IS.simplifyDivRem.L1114`. -/
theorem urem_mul_udiv_refines {a b x : Val w} {e : Bool} (h : Val.udiv a b e = Outcome.ok x) (nuw nsw : Bool) :
    Refines (Val.urem (Val.mul x b nuw nsw) b) (Outcome.ok (some 0#w)) := by
  obtain ⟨y, rfl, hy, hx⟩ := udiv_ok h
  rcases hx with rfl | ⟨p, rfl, -, rfl⟩
  · exact urem_none_left _ _
  · simp only [Val.mul]
    split
    · exact urem_none_left _ _
    · refine urem_refines_of fun _ => ?_
      have hle : p.toNat / y.toNat * y.toNat < 2 ^ w :=
        Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) p.isLt
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_umod, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.zero_mod]
      rw [Nat.mod_eq_of_lt hle, Nat.mul_mod_left]

/-- The signed quotient times the divisor is the dividend less its remainder, which is between `0` and the dividend,
so it's in range. -/
private theorem toInt_sdiv_mul {p y : BitVec w} (hy : y ≠ 0#w) (ho : p.sdivOverflow y = false) :
    (p.sdiv y * y).toInt = (p.sdiv y).toInt * y.toInt := by
  have hq := toInt_sdiv_of hy ho
  have hm : (p.sdiv y).toInt * y.toInt = p.toInt - p.toInt.tmod y.toInt := by
    rw [hq, Int.tdiv_mul_self]
  have hr : (p.toInt.tmod y.toInt).natAbs ≤ p.toInt.natAbs := by
    rw [Int.natAbs_tmod]; exact Nat.mod_le _ _
  have hs : 0 ≤ p.toInt → 0 ≤ p.toInt.tmod y.toInt := fun h => Int.tmod_nonneg _ h
  have hs' : p.toInt ≤ 0 → p.toInt.tmod y.toInt ≤ 0 := fun h => by
    have := Int.tmod_nonneg y.toInt (a := -p.toInt) (by omega)
    rw [Int.neg_tmod] at this
    omega
  obtain ⟨lo, hi⟩ := toInt_range p
  rw [BitVec.toInt_mul, hm]
  have hw := pos_of_ne_zero hy
  have h2 : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Int.pow_succ']; congr 1; omega
  apply Int.bmod_eq_of_le_mul_two
  · push_cast; omega
  · push_cast; omega

/-- `sdiv (mul (sdiv a, y), y), y` refines `sdiv a, y`. `IS.simplifyDivRem.L1114`. -/
theorem sdiv_mul_sdiv_refines {a b x : Val w} {e : Bool} (h : Val.sdiv a b e = Outcome.ok x) (nuw nsw e' : Bool) :
    Refines (Val.sdiv (Val.mul x b nuw nsw) b e') (Outcome.ok x) := by
  obtain ⟨y, rfl, hy, hx⟩ := sdiv_ok h
  rcases hx with rfl | ⟨p, rfl, ho, -, rfl⟩
  · exact sdiv_none_left _ _ _
  · simp only [Val.mul]
    split
    · exact sdiv_none_left _ _ _
    · refine sdiv_refines_of e' fun _ ho' => ?_
      congr 1
      apply BitVec.eq_of_toInt_eq
      rw [toInt_sdiv_of hy ho', toInt_sdiv_mul hy ho, Int.mul_tdiv_cancel _ (toInt_ne_zero hy)]

/-- `srem (mul (sdiv a, y), y), y` refines `0`. `IS.simplifyDivRem.L1114`. -/
theorem srem_mul_sdiv_refines {a b x : Val w} {e : Bool} (h : Val.sdiv a b e = Outcome.ok x) (nuw nsw : Bool) :
    Refines (Val.srem (Val.mul x b nuw nsw) b) (Outcome.ok (some 0#w)) := by
  obtain ⟨y, rfl, hy, hx⟩ := sdiv_ok h
  rcases hx with rfl | ⟨p, rfl, ho, -, rfl⟩
  · exact srem_none_left _ _
  · simp only [Val.mul]
    split
    · exact srem_none_left _ _
    · refine srem_refines_of fun _ _ => ?_
      congr 1
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_srem, toInt_sdiv_mul hy ho, Int.mul_tmod_left, BitVec.toInt_zero]

/-! ### A dividend smaller than the divisor -/

/-- `udiv x, y` refines `0` where `x < y`. `IS.simplifyDivRem.L1119`. -/
theorem udiv_of_lt_refines {x y : BitVec w} (h : x < y) (exact : Bool) :
    Refines (Val.udiv (some x) (some y) exact) (Outcome.ok (some 0#w)) :=
  udiv_refines_of exact fun _ => by rw [BitVec.udiv_eq_zero_iff_eq_zero_or_lt.2 (.inr h)]

/-- `urem x, y` refines `x` where `x < y`. `IS.simplifyDivRem.L1119`. -/
theorem urem_of_lt_refines {x y : BitVec w} (h : x < y) : Refines (Val.urem (some x) (some y)) (Outcome.ok (some x)) :=
  urem_refines_of fun _ => by rw [BitVec.umod_eq_of_lt h]

/-- `sdiv x, y` refines `0` where `|x| < |y|`. `IS.simplifyDivRem.L1119`. -/
theorem sdiv_of_natAbs_lt_refines {x y : BitVec w} (h : x.toInt.natAbs < y.toInt.natAbs) (exact : Bool) :
    Refines (Val.sdiv (some x) (some y) exact) (Outcome.ok (some 0#w)) :=
  sdiv_refines_of exact fun hy ho => by
    congr 1
    apply BitVec.eq_of_toInt_eq
    rw [toInt_sdiv_of hy ho, BitVec.toInt_zero]
    exact (Int.tdiv_eq_zero_iff_natAbs_lt_or_eq_zero.2 (.inl h)).symm

/-- `srem x, y` refines `x` where `|x| < |y|`. `IS.simplifyDivRem.L1119`. -/
theorem srem_of_natAbs_lt_refines {x y : BitVec w} (h : x.toInt.natAbs < y.toInt.natAbs) :
    Refines (Val.srem (some x) (some y)) (Outcome.ok (some x)) :=
  srem_refines_of fun _ _ => by
    congr 1
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_srem]
    have h0 : x.toInt.tdiv y.toInt = 0 := Int.tdiv_eq_zero_iff_natAbs_lt_or_eq_zero.2 (.inl h)
    have := Int.mul_tdiv_add_tmod x.toInt y.toInt
    rw [h0, Int.mul_zero, Int.zero_add] at this
    exact this.symm

/-! ### Exact division where the dividend has a low bit the divisor doesn't -/

/-- `udiv exact x, y` refines poison where `x` has a bit below `y`'s lowest: `y` doesn't divide `x`.
`IS.simplifyDiv.L1157`. -/
theorem udiv_exact_of_low_bit_refines {x y : BitVec w} {k : Nat} (hx : x.getLsbD k = true)
    (hk : k < y.ctz.toNat) : Refines (Val.udiv (some x) (some y) true) (Outcome.ok none) := by
  have hne : x % y ≠ 0#w := by
    intro h0
    have hd : y.toNat ∣ x.toNat := Nat.dvd_of_mod_eq_zero (by
      have := congrArg BitVec.toNat h0
      simpa [BitVec.toNat_umod] using this)
    have h2 := Nat.dvd_trans (two_pow_ctz_dvd y) hd
    have : x.toNat.testBit k = false := by
      have := Nat.testBit_mod_two_pow x.toNat y.ctz.toNat k
      rw [Nat.mod_eq_zero_of_dvd h2, Nat.zero_testBit] at this
      simp only [hk, decide_true, Bool.true_and] at this
      exact this.symm
    rw [BitVec.testBit_toNat, hx] at this
    exact Bool.noConfusion this
  simp only [Val.udiv]
  by_cases hy : y = 0#w
  · simp [hy]; exact Refine.outcome_ub _ _
  · simp only [beq_iff_eq, hy, ite_false, hne, bne_iff_ne, ne_eq, not_false_eq_true, Bool.true_and,
      ite_true]
    exact ok_refl _

/-- `sdiv exact x, y` refines poison where `x` has a bit below `y`'s lowest. `IS.simplifyDiv.L1157`. -/
theorem sdiv_exact_of_low_bit_refines {x y : BitVec w} {k : Nat} (hx : x.getLsbD k = true)
    (hk : k < y.ctz.toNat) : Refines (Val.sdiv (some x) (some y) true) (Outcome.ok none) := by
  have hne : x.srem y ≠ 0#w := by
    intro h0
    have hm : x.toInt.tmod y.toInt = 0 := by rw [← BitVec.toInt_srem, h0, BitVec.toInt_zero]
    have hd : y.toInt ∣ x.toInt := Int.dvd_of_tmod_eq_zero hm
    have hm2 := ctz_le y
    have h2w : (2 : Int) ^ y.ctz.toNat ∣ 2 ^ w := by
      have := Nat.pow_dvd_pow 2 hm2
      exact_mod_cast this
    have hy2 : (2 : Int) ^ y.ctz.toNat ∣ y.toInt := by
      rw [BitVec.toInt_eq_toNat_cond]
      have := Int.natCast_dvd_natCast.2 (two_pow_ctz_dvd y)
      push_cast at this
      split
      · exact this
      · exact Int.dvd_sub this (by exact_mod_cast h2w)
    have hx2 : (2 : Int) ^ y.ctz.toNat ∣ x.toInt := Int.dvd_trans hy2 hd
    have hxn : 2 ^ y.ctz.toNat ∣ x.toNat := by
      have : (2 : Int) ^ y.ctz.toNat ∣ (x.toNat : Int) := by
        rw [BitVec.toInt_eq_toNat_cond] at hx2
        split at hx2
        · exact hx2
        · have := Int.dvd_add hx2 (by exact_mod_cast h2w : (2 : Int) ^ y.ctz.toNat ∣ ((2 ^ w : Nat) : Int))
          simpa using this
      exact_mod_cast this
    have : x.toNat.testBit k = false := by
      have := Nat.testBit_mod_two_pow x.toNat y.ctz.toNat k
      rw [Nat.mod_eq_zero_of_dvd hxn, Nat.zero_testBit] at this
      simp only [hk, decide_true, Bool.true_and] at this
      exact this.symm
    rw [BitVec.testBit_toNat, hx] at this
    exact Bool.noConfusion this
  simp only [Val.sdiv, Val.divOverflows]
  by_cases hy : y = 0#w
  · simp [hy]; exact Refine.outcome_ub _ _
  · by_cases ho : x.sdivOverflow y = true
    · simp [hy, ho]; exact Refine.outcome_ub _ _
    · simp only [beq_iff_eq, hy, ite_false, ho, Bool.false_eq_true, hne, bne_iff_ne, ne_eq, not_false_eq_true,
        Bool.true_and, ite_true]
      exact ok_refl _

/-! ### Exact division of a product by a factor that isn't a power of two -/

/-- A divisor of `2 ^ n` is a power of two. -/
private theorem isPowerOfTwo_of_dvd_two_pow {d : Nat} : ∀ {n : Nat}, d ∣ 2 ^ n → d.isPowerOfTwo
  | 0, h => ⟨0, by simpa using Nat.eq_one_of_dvd_one h⟩
  | n + 1, h => by
    rcases Nat.mod_two_eq_zero_or_one d with he | ho
    · obtain ⟨e, rfl⟩ : 2 ∣ d := Nat.dvd_of_mod_eq_zero he
      have : e ∣ 2 ^ n := by
        have h' : 2 * e ∣ 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2] at h; exact h
        exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h'
      obtain ⟨k, hk⟩ := isPowerOfTwo_of_dvd_two_pow this
      exact ⟨k + 1, by rw [hk, Nat.pow_succ, Nat.mul_comm]⟩
    · have hc : Nat.Coprime d 2 := by
        show Nat.gcd d 2 = 1
        rw [Nat.gcd_comm, Nat.gcd_rec, ho]
        rfl
      rw [Nat.pow_succ] at h
      exact isPowerOfTwo_of_dvd_two_pow (hc.dvd_of_dvd_mul_right h)

/-- `udiv exact (mul nsw x, c), c` refines `x` where `c` isn't a power of two. If `c` is positive as a signed value,
a negative `x` makes the product wrap by `2 ^ w`, which `c` doesn't divide, so the division isn't exact. If `c` is
negative, the product is `0` or `c`, and `x` is `0` or `1`. `IS.simplifyDiv.L1168`. -/
theorem udiv_exact_mul_nsw_refines (a : Val w) {c : BitVec w} (hc : ¬ c.toNat.isPowerOfTwo) (nuw : Bool) :
    Refines (Val.udiv (Val.mul a (some c) nuw true) (some c) true) (Outcome.ok a) := by
  cases a with
  | none => exact udiv_none_left _ _ _
  | some x =>
  simp only [Val.mul]
  split
  · exact udiv_none_left _ _ _
  · next hov =>
    have hs : x.smulOverflow c = false := by
      revert hov; cases nuw <;> cases x.umulOverflow c <;> cases x.smulOverflow c <;> simp
    have hpi : (x * c).toInt = x.toInt * c.toInt := BitVec.toInt_mul_of_not_smulOverflow (by simp [hs])
    simp only [Val.udiv]
    by_cases hc0 : c = 0#w
    · simp [hc0]; exact Refine.outcome_ub _ _
    simp only [beq_iff_eq, hc0, ite_false]
    by_cases hm : x * c % c = 0#w
    · have hw := pos_of_ne_zero hc0
      have hC : 0 < c.toNat := Nat.pos_of_ne_zero fun h => hc0 (BitVec.eq_of_toNat_eq (by simp [h]))
      have hdvd : c.toNat ∣ (x * c).toNat := Nat.dvd_of_mod_eq_zero (by
        have := congrArg BitVec.toNat hm
        simpa [BitVec.toNat_umod] using this)
      obtain ⟨q, hq⟩ := hdvd
      have hq' : (x * c).toNat = q * c.toNat := by rw [hq, Nat.mul_comm]
      -- The quotient is `x`.
      have hres : x * c / c = x := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_udiv, hq', Nat.mul_div_cancel _ hC]
        have hP := BitVec.toInt_eq_toNat_cond (x * c)
        have hX := BitVec.toInt_eq_toNat_cond x
        have hCc := BitVec.toInt_eq_toNat_cond c
        have hlt := (x * c).isLt
        have hxlt := x.isLt
        have hclt := c.isLt
        by_cases hcpos : 2 * c.toNat < 2 ^ w
        · rw [ite_eq_left hcpos] at hCc
          by_cases hxpos : 2 * x.toNat < 2 ^ w
          · -- Both nonnegative: the product is `x * c` exactly.
            rw [ite_eq_left hxpos] at hX
            have hnn : 0 ≤ x.toInt * c.toInt := by rw [hX, hCc]; exact Int.mul_nonneg (by omega) (by omega)
            have hPpos : 2 * (x * c).toNat < 2 ^ w := by
              apply Classical.byContradiction
              intro hn
              rw [ite_eq_right hn] at hP
              omega
            rw [ite_eq_left hPpos] at hP
            have : ((q * c.toNat : Nat) : Int) = (x.toNat : Int) * (c.toNat : Int) := by
              rw [← hq', ← hP, hpi, hX, hCc]
            have : q * c.toNat = x.toNat * c.toNat := by exact_mod_cast this
            exact Nat.eq_of_mul_eq_mul_right hC this
          · -- `x` negative: the product wraps by `2 ^ w`, which `c` would have to divide.
            rw [ite_eq_right hxpos] at hX
            have hneg : x.toInt * c.toInt < 0 := by
              rw [hX, hCc]; exact Int.mul_neg_of_neg_of_pos (by omega) (by omega)
            have hPneg : ¬ 2 * (x * c).toNat < 2 ^ w := by
              intro hn; rw [ite_eq_left hn] at hP; omega
            rw [ite_eq_right hPneg] at hP
            exfalso
            apply hc
            apply isPowerOfTwo_of_dvd_two_pow (n := w)
            have hqc : ((x * c).toNat : Int) = (q : Int) * c.toNat := by exact_mod_cast hq'
            rw [hpi, hX, hCc] at hP
            have e : ((2 ^ w : Nat) : Int) =
                (q : Int) * c.toNat - ((x.toNat : Int) - (2 ^ w : Nat)) * c.toNat := by
              omega
            have : (c.toNat : Int) ∣ ((2 ^ w : Nat) : Int) := by
              rw [e]; exact Int.dvd_sub (Int.dvd_mul_left _ _) (Int.dvd_mul_left _ _)
            exact Int.natCast_dvd_natCast.1 this
        · -- `c` negative: the product is less than `2 * c`, so it's `0` or `c`.
          rw [ite_eq_right hcpos] at hCc
          have hq2 : q < 2 := by
            apply Classical.byContradiction
            intro hn
            have : 2 * c.toNat ≤ q * c.toNat := Nat.mul_le_mul_right _ (by omega)
            omega
          have hci : c.toInt ≠ 0 := toInt_ne_zero hc0
          rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
          · have h0 : x * c = 0#w := BitVec.eq_of_toNat_eq (by simp [hq'])
            have : x.toInt * c.toInt = 0 := by rw [← hpi, h0, BitVec.toInt_zero]
            have hx0 : x.toInt = 0 := (Int.mul_eq_zero.1 this).resolve_right hci
            have : x = 0#w := BitVec.eq_of_toInt_eq (by rw [hx0, BitVec.toInt_zero])
            simp [this]
          · have h1 : x * c = c := BitVec.eq_of_toNat_eq (by simp [hq'])
            have : x.toInt * c.toInt = 1 * c.toInt := by rw [← hpi, h1, Int.one_mul]
            have hx1 : x.toInt = 1 := Int.eq_of_mul_eq_mul_right hci this
            have hw2 : 1 < w := by
              have := BitVec.toInt_lt (x := x)
              rw [hx1] at this
              rcases (by omega : w = 1 ∨ 1 < w) with rfl | h
              · simp at this
              · exact h
            have : x = 1#w := BitVec.eq_of_toInt_eq (by rw [hx1, BitVec.toInt_one hw2])
            rw [this, BitVec.toNat_one hw]
      simp only [hm, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false, hres]
      exact ok_refl _
    · simp only [hm, bne_iff_ne, ne_eq, not_false_eq_true, Bool.true_and, ite_true]
      exact ok_none_refines _

/-- `sdiv exact (mul nuw x, c), c` refines `x` where `c` isn't a power of two. If `c` is positive as a signed value, a
product past the signed range is `2 ^ w` from its signed value, which `c` doesn't divide. If `c` is negative, `x` is `0`
or `1`. `IS.simplifyDiv.L1168`. -/
theorem sdiv_exact_mul_nuw_refines (a : Val w) {c : BitVec w} (hc : ¬ c.toNat.isPowerOfTwo) (nsw : Bool) :
    Refines (Val.sdiv (Val.mul a (some c) true nsw) (some c) true) (Outcome.ok a) := by
  cases a with
  | none => exact sdiv_none_left _ _ _
  | some x =>
  simp only [Val.mul, Bool.true_and]
  split
  · exact sdiv_none_left _ _ _
  · next hov =>
    have hu : x.umulOverflow c = false := by revert hov; cases x.umulOverflow c <;> simp
    have hP : (x * c).toNat = x.toNat * c.toNat := BitVec.toNat_mul_of_not_umulOverflow (by simp [hu])
    simp only [Val.sdiv, Val.divOverflows]
    by_cases hc0 : c = 0#w
    · simp [hc0]; exact Refine.outcome_ub _ _
    by_cases ho : (x * c).sdivOverflow c = true
    · simp [hc0, ho]; exact Refine.outcome_ub _ _
    simp only [Bool.not_eq_true] at ho
    simp only [beq_iff_eq, hc0, ite_false, ho, Bool.false_eq_true]
    by_cases hm : (x * c).srem c = 0#w
    · have hw := pos_of_ne_zero hc0
      have hC : 0 < c.toNat := Nat.pos_of_ne_zero fun h => hc0 (BitVec.eq_of_toNat_eq (by simp [h]))
      have hres : (x * c).sdiv c = x := by
        have hPc := BitVec.toInt_eq_toNat_cond (x * c)
        have hX := BitVec.toInt_eq_toNat_cond x
        have hCc := BitVec.toInt_eq_toNat_cond c
        have hlt := (x * c).isLt
        by_cases hcpos : 2 * c.toNat < 2 ^ w
        · rw [ite_eq_left hcpos] at hCc
          have hxle : x.toNat ≤ x.toNat * c.toNat := Nat.le_mul_of_pos_right _ hC
          by_cases hPpos : 2 * (x * c).toNat < 2 ^ w
          · rw [ite_eq_left hPpos] at hPc
            have hxpos : 2 * x.toNat < 2 ^ w := by omega
            rw [ite_eq_left hxpos] at hX
            apply BitVec.eq_of_toInt_eq
            rw [toInt_sdiv_of hc0 ho, hPc, hP, hX, hCc]
            push_cast
            exact Int.mul_tdiv_cancel _ (by omega)
          · -- The product's signed value is `x * c - 2 ^ w`, and `c` divides it exactly.
            rw [ite_eq_right hPpos] at hPc
            exfalso
            apply hc
            apply isPowerOfTwo_of_dvd_two_pow (n := w)
            have hm' : (x * c).toInt.tmod c.toInt = 0 := by rw [← BitVec.toInt_srem, hm, BitVec.toInt_zero]
            have hd := Int.dvd_of_tmod_eq_zero hm'
            rw [hPc, hCc, hP] at hd
            push_cast at hd
            have : (c.toNat : Int) ∣ (2 ^ w : Int) := by
              have := Int.dvd_sub (Int.dvd_mul_left (x.toNat : Int) (c.toNat : Int)) hd
              rwa [show (x.toNat : Int) * c.toNat - ((x.toNat : Int) * c.toNat - 2 ^ w) = 2 ^ w by omega] at this
            exact Int.natCast_dvd_natCast.1 (by exact_mod_cast this)
        · -- `c` negative: the product fits, so `x` is `0` or `1`.
          have hx2 : x.toNat < 2 := by
            apply Classical.byContradiction
            intro hn
            have : 2 * c.toNat ≤ x.toNat * c.toNat := Nat.mul_le_mul_right _ (by omega)
            omega
          rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with h0 | h1
          · have : x = 0#w := BitVec.eq_of_toNat_eq (by simp [h0])
            subst this
            simp [BitVec.zero_mul, BitVec.zero_sdiv]
          · have : x = 1#w := BitVec.eq_of_toNat_eq (by rw [h1, BitVec.toNat_one hw])
            subst this
            rw [BitVec.one_mul, BitVec.sdiv_self]
            simp [hc0]
      simp only [hm, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false, hres]
      exact ok_refl _
    · simp only [hm, bne_iff_ne, ne_eq, not_false_eq_true, Bool.true_and, ite_true]
      exact ok_none_refines _

/-! ### A remainder by a factor -/

/-- `urem (shl nuw x, s), x` refines `0`: the shift is `x * 2 ^ s`, exactly. `IS.simplifyRem.L1189`. -/
theorem urem_shl_nuw_refines (a s : Val w) (nsw : Bool) :
    Refines (Val.urem (Val.shl a s true nsw) a) (Outcome.ok (some 0#w)) := by
  cases a with
  | none => exact urem_none_right _ _
  | some x =>
  cases s with
  | none => exact urem_none_left _ _
  | some t =>
  simp only [Val.shl, Bool.true_and]
  split
  · exact urem_none_left _ _
  split
  · exact urem_none_left _ _
  split
  · exact urem_none_left _ _
  next hok hnuw _ =>
  refine urem_refines_of fun _ => ?_
  simp only [Bool.not_eq_true', Generic.shiftOk_iff, decide_eq_false_iff_not, Decidable.not_not] at hok
  simp only [bne_iff_ne, ne_eq, Decidable.not_not, BitVec.shiftLeft_eq'] at hnuw
  have hfit := (Generic.shl_lshr_eq_iff x (k := t.toNat) (Nat.le_of_lt hok)).1 hnuw
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hfit,
    Nat.mul_mod_right]
  simp

/-- `srem (shl nsw x, s), x` refines `0`: the shift is `x * 2 ^ s` as a signed value, exactly.
`IS.simplifyRem.L1189`. -/
theorem srem_shl_nsw_refines (a s : Val w) (nuw : Bool) :
    Refines (Val.srem (Val.shl a s nuw true) a) (Outcome.ok (some 0#w)) := by
  cases a with
  | none => exact srem_none_right _ _
  | some x =>
  cases s with
  | none => exact srem_none_left _ _
  | some t =>
  simp only [Val.shl, Bool.true_and]
  split
  · exact srem_none_left _ _
  split
  · exact srem_none_left _ _
  split
  · exact srem_none_left _ _
  next hok _ hnsw =>
  refine srem_refines_of fun hx _ => ?_
  simp only [Bool.not_eq_true', Generic.shiftOk_iff, decide_eq_false_iff_not, Decidable.not_not] at hok
  simp only [bne_iff_ne, ne_eq, Decidable.not_not, BitVec.shiftLeft_eq', BitVec.sshiftRight_eq'] at hnsw
  obtain ⟨lo, hi⟩ := (Generic.shl_sshr_eq_iff x (k := t.toNat) hok).1 hnsw
  have hw := pos_of_ne_zero hx
  have h2 : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Int.pow_succ']; congr 1; omega
  have hv : (x <<< t.toNat).toInt = x.toInt * 2 ^ t.toNat := by
    rw [BitVec.toInt_shiftLeft, Nat.shiftLeft_eq]
    push_cast
    rw [← Int.bmod_mul_bmod, ← BitVec.toInt_eq_toNat_bmod]
    apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> omega
  congr 1
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_srem, BitVec.shiftLeft_eq', hv, Int.mul_tmod_right, BitVec.toInt_zero]

/-- `urem (mul nuw x, c1), c0` refines `0` where `c0` divides `c1`. `IS.simplifyRem.L1204`. -/
theorem urem_mul_nuw_of_umod_refines (a : Val w) {c1 c0 : BitVec w} (h : c1 % c0 = 0#w) (nsw : Bool) :
    Refines (Val.urem (Val.mul a (some c1) true nsw) (some c0)) (Outcome.ok (some 0#w)) := by
  cases a with
  | none => exact urem_none_left _ _
  | some x =>
  simp only [Val.mul, Bool.true_and]
  split
  · exact urem_none_left _ _
  · next hov =>
    have hu : x.umulOverflow c1 = false := by revert hov; cases x.umulOverflow c1 <;> simp
    refine urem_refines_of fun _ => ?_
    have hd : c0.toNat ∣ c1.toNat := Nat.dvd_of_mod_eq_zero (by
      have := congrArg BitVec.toNat h
      simpa [BitVec.toNat_umod] using this)
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod, BitVec.toNat_mul_of_not_umulOverflow (by simp [hu]),
      Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd (Nat.dvd_mul_left _ _))]
    simp

/-- `srem (mul nsw x, c1), c0` refines `0` where `c0` divides `c1`. `IS.simplifyRem.L1204`. -/
theorem srem_mul_nsw_of_srem_refines (a : Val w) {c1 c0 : BitVec w} (h : c1.srem c0 = 0#w) (nuw : Bool) :
    Refines (Val.srem (Val.mul a (some c1) nuw true) (some c0)) (Outcome.ok (some 0#w)) := by
  cases a with
  | none => exact srem_none_left _ _
  | some x =>
  simp only [Val.mul, Bool.true_and]
  split
  · exact srem_none_left _ _
  · next hov =>
    have hs : x.smulOverflow c1 = false := by
      revert hov; cases nuw <;> cases x.umulOverflow c1 <;> cases x.smulOverflow c1 <;> simp
    refine srem_refines_of fun _ _ => ?_
    have hm : c1.toInt.tmod c0.toInt = 0 := by rw [← BitVec.toInt_srem, h, BitVec.toInt_zero]
    have hd := Int.dvd_of_tmod_eq_zero hm
    congr 1
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_srem, BitVec.toInt_mul_of_not_smulOverflow (by simp [hs]),
      Int.tmod_eq_zero_of_dvd (Int.dvd_trans hd (Int.dvd_mul_left _ _)), BitVec.toInt_zero]

/-! ### Division by a negation -/

private theorem tdiv_neg_self {v : Int} (h : v ≠ 0) : (-v).tdiv v = -1 := by
  rw [Int.neg_tdiv, Int.tdiv_self h]

private theorem tdiv_self_neg {v : Int} (h : v ≠ 0) : v.tdiv (-v) = -1 := by
  rw [Int.tdiv_neg, Int.tdiv_self h]

/-- `sdiv (sub nsw 0, y), y` refines `-1`. `IS.simplifySDivInst.L1216`. -/
theorem sdiv_neg_nsw_left_refines (b : Val w) (nuw exact : Bool) :
    Refines (Val.sdiv (Val.sub (some 0#w) b nuw true) b exact) (Outcome.ok (some (BitVec.allOnes w))) := by
  cases b with
  | none => exact sdiv_none_right _ _ _
  | some y =>
  simp only [Val.sub]
  split
  · exact sdiv_none_left _ _ _
  · next hov =>
    have hs : (0#w).ssubOverflow y = false := by
      revert hov; cases nuw <;> cases (0#w).usubOverflow y <;> cases (0#w).ssubOverflow y <;> simp
    refine sdiv_refines_of exact fun hy ho => ?_
    congr 1
    refine (eq_allOnes_of_toInt (pos_of_ne_zero hy) ?_).symm
    rw [toInt_sdiv_of hy ho, BitVec.toInt_sub_of_not_ssubOverflow (by simp [hs]), BitVec.toInt_zero, Int.zero_sub]
    exact tdiv_neg_self (toInt_ne_zero hy)

/-- `sdiv x, (sub nsw 0, x)` refines `-1`. `IS.simplifySDivInst.L1216`. -/
theorem sdiv_neg_nsw_right_refines (a : Val w) (nuw exact : Bool) :
    Refines (Val.sdiv a (Val.sub (some 0#w) a nuw true) exact) (Outcome.ok (some (BitVec.allOnes w))) := by
  cases a with
  | none => exact sdiv_none_right _ _ _
  | some x =>
  simp only [Val.sub]
  split
  · exact sdiv_none_right _ _ _
  · next hov =>
    have hs : (0#w).ssubOverflow x = false := by
      revert hov; cases nuw <;> cases (0#w).usubOverflow x <;> cases (0#w).ssubOverflow x <;> simp
    refine sdiv_refines_of exact fun hy ho => ?_
    have hd : (0#w - x).toInt = -x.toInt := by
      rw [BitVec.toInt_sub_of_not_ssubOverflow (by simp [hs]), BitVec.toInt_zero, Int.zero_sub]
    have hx : x.toInt ≠ 0 := fun h => toInt_ne_zero hy (by rw [hd, h, Int.neg_zero])
    congr 1
    refine (eq_allOnes_of_toInt (pos_of_ne_zero hy) ?_).symm
    rw [toInt_sdiv_of hy ho, hd]
    exact tdiv_self_neg hx

/-- `sdiv (sub nsw a, b), (sub nsw b, a)` refines `-1`. `IS.simplifySDivInst.L1216`. -/
theorem sdiv_sub_nsw_swap_refines (a b : Val w) (nuw1 nuw2 exact : Bool) :
    Refines (Val.sdiv (Val.sub a b nuw1 true) (Val.sub b a nuw2 true) exact)
      (Outcome.ok (some (BitVec.allOnes w))) := by
  cases a with
  | none => cases b <;> exact sdiv_none_right _ _ _
  | some x =>
  cases b with
  | none => exact sdiv_none_right _ _ _
  | some y =>
  simp only [Val.sub]
  split
  · split
    · exact sdiv_none_right _ _ _
    · exact sdiv_none_left _ _ _
  · next hov1 =>
    split
    · exact sdiv_none_right _ _ _
    · next hov2 =>
      have hs1 : x.ssubOverflow y = false := by
        revert hov1; cases nuw1 <;> cases x.usubOverflow y <;> cases x.ssubOverflow y <;> simp
      have hs2 : y.ssubOverflow x = false := by
        revert hov2; cases nuw2 <;> cases y.usubOverflow x <;> cases y.ssubOverflow x <;> simp
      refine sdiv_refines_of exact fun hy ho => ?_
      have hd : (y - x).toInt = -(x - y).toInt := by
        rw [BitVec.toInt_sub_of_not_ssubOverflow (by simp [hs2]),
          BitVec.toInt_sub_of_not_ssubOverflow (by simp [hs1])]
        omega
      have hn : (x - y).toInt ≠ 0 := fun h => toInt_ne_zero hy (by rw [hd, h, Int.neg_zero])
      congr 1
      refine (eq_allOnes_of_toInt (pos_of_ne_zero hy) ?_).symm
      rw [toInt_sdiv_of hy ho, hd]
      exact tdiv_self_neg hn

/-! ### Remainder by a negation, or by `sext` of a bit -/

/-- `sext` of a bit is `0` or all ones. -/
private theorem signExtend_one_bit (t : BitVec 1) :
    t.signExtend w = 0#w ∨ t.signExtend w = BitVec.allOnes w := by
  rcases (by decide : ∀ t : BitVec 1, t = 0#1 ∨ t = 1#1) t with rfl | rfl
  · left
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_signExtend]
  · right
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_signExtend, hi]

/-- `srem x, (sext i1 b)` refines `0`: the divisor is `0`, which is undefined, or `-1`. `IS.simplifySRemInst.L1246`. -/
theorem srem_sext_one_bit_refines (a : Val w) (b : Val 1) :
    Refines (Val.srem a (Val.sext w b)) (Outcome.ok (some 0#w)) := by
  cases b with
  | none => exact srem_none_right _ _
  | some t =>
  simp only [Val.sext, Val.map₁]
  rcases signExtend_one_bit (w := w) t with h | h
  · rw [h]; exact srem_zero_right _ _
  · rw [h]
    cases a with
    | none => exact srem_none_left _ _
    | some x =>
      refine srem_refines_of fun hy _ => ?_
      have hw := pos_of_ne_zero hy
      congr 1
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_srem, BitVec.toInt_allOnes, ite_eq_left hw, Int.tmod_neg, Int.tmod_one, BitVec.toInt_zero]

private theorem neg_srem_self (y : BitVec w) : (-y).srem y = 0#w := by
  by_cases hm : y = BitVec.intMin w
  · rw [hm, BitVec.neg_intMin, BitVec.srem_self]
  · apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_srem, BitVec.toInt_neg_of_ne_intMin hm, Int.neg_tmod, Int.tmod_self, Int.neg_zero,
      BitVec.toInt_zero]

private theorem srem_neg_self (x : BitVec w) : x.srem (-x) = 0#w := by
  by_cases hm : x = BitVec.intMin w
  · rw [hm, BitVec.neg_intMin, BitVec.srem_self]
  · apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_srem, BitVec.toInt_neg_of_ne_intMin hm, Int.tmod_neg, Int.tmod_self, BitVec.toInt_zero]

/-- `srem (sub 0, y), y` refines `0`, whatever the flags. `IS.simplifySRemInst.L1250`. -/
theorem srem_neg_left_refines (b : Val w) (nuw nsw : Bool) :
    Refines (Val.srem (Val.sub (some 0#w) b nuw nsw) b) (Outcome.ok (some 0#w)) := by
  cases b with
  | none => exact srem_none_right _ _
  | some y =>
  simp only [Val.sub]
  split
  · exact srem_none_left _ _
  · exact srem_refines_of fun _ _ => by rw [BitVec.zero_sub, neg_srem_self]

/-- `srem x, (sub 0, x)` refines `0`, whatever the flags. `IS.simplifySRemInst.L1250`. -/
theorem srem_neg_right_refines (a : Val w) (nuw nsw : Bool) :
    Refines (Val.srem a (Val.sub (some 0#w) a nuw nsw)) (Outcome.ok (some 0#w)) := by
  cases a with
  | none => exact srem_none_right _ _
  | some x =>
  simp only [Val.sub]
  split
  · exact srem_none_right _ _
  · exact srem_refines_of fun _ _ => by rw [BitVec.zero_sub, srem_neg_self]

/-- `srem (sub a, b), (sub b, a)` refines `0`, whatever the flags. `IS.simplifySRemInst.L1250`. -/
theorem srem_sub_swap_refines (a b : Val w) (f1 f2 f3 f4 : Bool) :
    Refines (Val.srem (Val.sub a b f1 f2) (Val.sub b a f3 f4)) (Outcome.ok (some 0#w)) := by
  cases a with
  | none => cases b <;> exact srem_none_right _ _
  | some x =>
  cases b with
  | none => exact srem_none_right _ _
  | some y =>
  simp only [Val.sub]
  split
  · split
    · exact srem_none_right _ _
    · exact srem_none_left _ _
  · split
    · exact srem_none_right _ _
    · have e : y - x = -(x - y) := by rw [BitVec.neg_sub, BitVec.add_comm, ← BitVec.sub_eq_add_neg]
      exact srem_refines_of fun _ _ => by rw [e, srem_neg_self]

end Peephole.Lemmas

/-! ## Counterexamples

For each hypothesis of a lemma above, the lemma without it is false: `drop_<hypothesis>` gives one input where it
fails. For each lemma with hypotheses, `sat` gives one input where they all hold. They're in the form
`store/LemmaStore/Counter/Generic.lean` uses, for the store to check. -/

namespace LemmaStore.Counter

open IRLean

/-- A value that's the value `x` only allows `x`. -/
private theorem arith_not_refines_val {w : Nat} {a b : Val w} (x : BitVec w) (ha : a = some x) (hb : b ≠ some x) :
    ¬ Refines a b := by
  subst ha; exact fun r => hb ((Refine.val_some x b).1 r)

/-- A run that returns the value `x` only allows `x`. -/
private theorem arith_not_refines_ok {w : Nat} {o : Outcome (Val w)} {b : Val w} (x : BitVec w)
    (ho : o = Outcome.ok (some x)) (hb : b ≠ some x) : ¬ Refines o (Outcome.ok b) := by
  subst ho; exact fun r => hb ((Refine.val_some x b).1 ((Refine.outcome_ok_ok _ _).1 r))

/-- `0 - 1` is `-1`, which is neither `0` nor `1`. -/
theorem Peephole.Lemmas.sub_zero_left_nsw_refines.drop_h :
    ¬ ∀ {w : Nat} {y : BitVec w} (nuw : Bool), Refines (Val.sub (some 0#w) (some y) nuw true) (some 0#w) :=
  fun h => arith_not_refines_val 3#2 rfl (by decide) (@h 2 1#2 false)

theorem Peephole.Lemmas.sub_zero_left_nsw_refines.sat :
    ∃ (w : Nat) (y : BitVec w) (_ : Bool), y &&& BitVec.intMax w = 0#w :=
  ⟨1, 0#1, false, by decide⟩

theorem Peephole.Lemmas.sub_zero_left_refines_self.drop_h :
    ¬ ∀ {w : Nat} {y : BitVec w} (nuw nsw : Bool), Refines (Val.sub (some 0#w) (some y) nuw nsw) (some y) :=
  fun h => arith_not_refines_val 3#2 rfl (by decide) (@h 2 1#2 false false)

theorem Peephole.Lemmas.sub_zero_left_refines_self.sat :
    ∃ (w : Nat) (y : BitVec w) (_ _ : Bool), y &&& BitVec.intMax w = 0#w :=
  ⟨1, 0#1, false, false, by decide⟩

/-- `2` isn't a low-bit mask: `2 - (3 ^ 2)` is `1`, not `3`. -/
theorem Peephole.Lemmas.sub_mask_xor_nuw_refines.drop_hc :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w} (nsw : Bool),
      Refines (Val.sub (some c) (Val.xor a (some c)) true nsw) a :=
  fun h => arith_not_refines_val 1#2 rfl (by decide) (@h 2 (some 3#2) 2#2 false)

theorem Peephole.Lemmas.sub_mask_xor_nuw_refines.sat :
    ∃ (w : Nat) (_ : Val w) (c : BitVec w) (_ : Bool), (c + 1#w) &&& c = 0#w :=
  ⟨1, none, 0#1, false, by decide⟩

/-- `1 * 1` is `1`, not `0`: the quotient has to be the dividend's. -/
theorem Peephole.Lemmas.mul_udiv_exact_refines.drop_h :
    ¬ ∀ {w : Nat} {a b q : Val w} (nuw nsw : Bool), Refines (Val.mul q b nuw nsw) a :=
  fun h => arith_not_refines_val 1#2 rfl (by decide) (@h 2 (some 0#2) (some 1#2) (some 1#2) false false)

theorem Peephole.Lemmas.mul_udiv_exact_refines.sat :
    ∃ (w : Nat) (a b q : Val w) (_ _ : Bool), Val.udiv a b true = Outcome.ok q :=
  ⟨1, none, some 1#1, none, false, false, rfl⟩

theorem Peephole.Lemmas.mul_sdiv_exact_refines.drop_h :
    ¬ ∀ {w : Nat} {a b q : Val w} (nuw nsw : Bool), Refines (Val.mul q b nuw nsw) a :=
  fun h => arith_not_refines_val 1#2 rfl (by decide) (@h 2 (some 0#2) (some 1#2) (some 1#2) false false)

theorem Peephole.Lemmas.mul_sdiv_exact_refines.sat :
    ∃ (w : Nat) (a b q : Val w) (_ _ : Bool), Val.sdiv a b true = Outcome.ok q :=
  ⟨2, none, some 1#2, none, false, false, rfl⟩

/-- `3 * 2` wraps to `2` in `i2`, and `2 / 2` is `1`, not `3`. -/
theorem Peephole.Lemmas.udiv_mul_udiv_refines.drop_h :
    ¬ ∀ {w : Nat} {_ : Val w} {b x : Val w} {_ : Bool} (nuw nsw e' : Bool),
      Refines (Val.udiv (Val.mul x b nuw nsw) b e') (Outcome.ok x) :=
  fun h => arith_not_refines_ok 1#2 rfl (by decide)
    (@h 2 none (some 2#2) (some 3#2) false false false false)

theorem Peephole.Lemmas.udiv_mul_udiv_refines.sat :
    ∃ (w : Nat) (a b x : Val w) (e : Bool) (_ _ _ : Bool), Val.udiv a b e = Outcome.ok x :=
  ⟨1, none, some 1#1, none, false, false, false, false, rfl⟩

/-- `3 * 3` wraps to `1` in `i2`, and `1 % 3` is `1`. -/
theorem Peephole.Lemmas.urem_mul_udiv_refines.drop_h :
    ¬ ∀ {w : Nat} {_ : Val w} {b x : Val w} {_ : Bool} (nuw nsw : Bool),
      Refines (Val.urem (Val.mul x b nuw nsw) b) (Outcome.ok (some 0#w)) :=
  fun h => arith_not_refines_ok 1#2 rfl (by decide) (@h 2 none (some 3#2) (some 3#2) false false false)

theorem Peephole.Lemmas.urem_mul_udiv_refines.sat :
    ∃ (w : Nat) (a b x : Val w) (e : Bool) (_ _ : Bool), Val.udiv a b e = Outcome.ok x :=
  ⟨1, none, some 1#1, none, false, false, false, rfl⟩

/-- `3 * 3` wraps to `1` in `i3`, and `1 sdiv 3` is `0`, not `3`. -/
theorem Peephole.Lemmas.sdiv_mul_sdiv_refines.drop_h :
    ¬ ∀ {w : Nat} {_ : Val w} {b x : Val w} {_ : Bool} (nuw nsw e' : Bool),
      Refines (Val.sdiv (Val.mul x b nuw nsw) b e') (Outcome.ok x) :=
  fun h => arith_not_refines_ok 0#3 rfl (by decide)
    (@h 3 none (some 3#3) (some 3#3) false false false false)

theorem Peephole.Lemmas.sdiv_mul_sdiv_refines.sat :
    ∃ (w : Nat) (a b x : Val w) (e : Bool) (_ _ _ : Bool), Val.sdiv a b e = Outcome.ok x :=
  ⟨2, none, some 1#2, none, false, false, false, false, rfl⟩

theorem Peephole.Lemmas.srem_mul_sdiv_refines.drop_h :
    ¬ ∀ {w : Nat} {_ : Val w} {b x : Val w} {_ : Bool} (nuw nsw : Bool),
      Refines (Val.srem (Val.mul x b nuw nsw) b) (Outcome.ok (some 0#w)) :=
  fun h => arith_not_refines_ok 1#3 rfl (by decide) (@h 3 none (some 3#3) (some 3#3) false false false)

theorem Peephole.Lemmas.srem_mul_sdiv_refines.sat :
    ∃ (w : Nat) (a b x : Val w) (e : Bool) (_ _ : Bool), Val.sdiv a b e = Outcome.ok x :=
  ⟨2, none, some 1#2, none, false, false, false, rfl⟩

/-- `1 / 1` is `1`. -/
theorem Peephole.Lemmas.udiv_of_lt_refines.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w} (exact : Bool),
      Refines (Val.udiv (some x) (some y) exact) (Outcome.ok (some 0#w)) :=
  fun h => arith_not_refines_ok 1#2 rfl (by decide) (@h 2 1#2 1#2 false)

theorem Peephole.Lemmas.udiv_of_lt_refines.sat : ∃ (w : Nat) (x y : BitVec w) (_ : Bool), x < y :=
  ⟨1, 0#1, 1#1, false, by decide⟩

/-- `1 % 1` is `0`. -/
theorem Peephole.Lemmas.urem_of_lt_refines.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w}, Refines (Val.urem (some x) (some y)) (Outcome.ok (some x)) :=
  fun h => arith_not_refines_ok 0#2 rfl (by decide) (@h 2 1#2 1#2)

theorem Peephole.Lemmas.urem_of_lt_refines.sat : ∃ (w : Nat) (x y : BitVec w), x < y :=
  ⟨1, 0#1, 1#1, by decide⟩

theorem Peephole.Lemmas.sdiv_of_natAbs_lt_refines.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w} (exact : Bool),
      Refines (Val.sdiv (some x) (some y) exact) (Outcome.ok (some 0#w)) :=
  fun h => arith_not_refines_ok 1#2 rfl (by decide) (@h 2 1#2 1#2 false)

theorem Peephole.Lemmas.sdiv_of_natAbs_lt_refines.sat :
    ∃ (w : Nat) (x y : BitVec w) (_ : Bool), x.toInt.natAbs < y.toInt.natAbs :=
  ⟨2, 0#2, 1#2, false, by decide⟩

theorem Peephole.Lemmas.srem_of_natAbs_lt_refines.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w}, Refines (Val.srem (some x) (some y)) (Outcome.ok (some x)) :=
  fun h => arith_not_refines_ok 0#2 rfl (by decide) (@h 2 1#2 1#2)

theorem Peephole.Lemmas.srem_of_natAbs_lt_refines.sat :
    ∃ (w : Nat) (x y : BitVec w), x.toInt.natAbs < y.toInt.natAbs :=
  ⟨2, 0#2, 1#2, by decide⟩

/-- `0 /exact 2` is `0`: no low bit of the dividend is set. -/
theorem Peephole.Lemmas.udiv_exact_of_low_bit_refines.drop_hx :
    ¬ ∀ {w : Nat} {x y : BitVec w} {k : Nat}, k < y.ctz.toNat →
      Refines (Val.udiv (some x) (some y) true) (Outcome.ok none) :=
  fun h => arith_not_refines_ok 0#2 rfl (by decide) (@h 2 0#2 2#2 0 (by decide))

/-- `2 /exact 2` is `1`: the dividend's set bit isn't below the divisor's lowest. -/
theorem Peephole.Lemmas.udiv_exact_of_low_bit_refines.drop_hk :
    ¬ ∀ {w : Nat} {x y : BitVec w} {k : Nat}, x.getLsbD k = true →
      Refines (Val.udiv (some x) (some y) true) (Outcome.ok none) :=
  fun h => arith_not_refines_ok 1#2 rfl (by decide) (@h 2 2#2 2#2 1 (by decide))

theorem Peephole.Lemmas.udiv_exact_of_low_bit_refines.sat :
    ∃ (w : Nat) (x y : BitVec w) (k : Nat), x.getLsbD k = true ∧ k < y.ctz.toNat :=
  ⟨2, 1#2, 2#2, 0, by decide, by decide⟩

theorem Peephole.Lemmas.sdiv_exact_of_low_bit_refines.drop_hx :
    ¬ ∀ {w : Nat} {x y : BitVec w} {k : Nat}, k < y.ctz.toNat →
      Refines (Val.sdiv (some x) (some y) true) (Outcome.ok none) :=
  fun h => arith_not_refines_ok 0#3 rfl (by decide) (@h 3 0#3 2#3 0 (by decide))

theorem Peephole.Lemmas.sdiv_exact_of_low_bit_refines.drop_hk :
    ¬ ∀ {w : Nat} {x y : BitVec w} {k : Nat}, x.getLsbD k = true →
      Refines (Val.sdiv (some x) (some y) true) (Outcome.ok none) :=
  fun h => arith_not_refines_ok 1#3 rfl (by decide) (@h 3 2#3 2#3 1 (by decide))

theorem Peephole.Lemmas.sdiv_exact_of_low_bit_refines.sat :
    ∃ (w : Nat) (x y : BitVec w) (k : Nat), x.getLsbD k = true ∧ k < y.ctz.toNat :=
  ⟨3, 1#3, 2#3, 0, by decide, by decide⟩

/-- `-2 * 2` is `-4` in `i3`, without signed overflow, and `4 /exact 2` is `2`, not `-2`. -/
theorem Peephole.Lemmas.udiv_exact_mul_nsw_refines.drop_hc :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w} (nuw : Bool),
      Refines (Val.udiv (Val.mul a (some c) nuw true) (some c) true) (Outcome.ok a) :=
  fun h => arith_not_refines_ok 2#3 rfl (by decide) (@h 3 (some 6#3) 2#3 false)

theorem Peephole.Lemmas.udiv_exact_mul_nsw_refines.sat :
    ∃ (w : Nat) (_ : Val w) (c : BitVec w) (_ : Bool), ¬ c.toNat.isPowerOfTwo :=
  ⟨2, none, 3#2, false, by decide⟩

/-- `3 * 2` is `6` in `i3`, without unsigned overflow, and `6 sdiv exact 2`, which is `-2 sdiv 2`, is `-1`. -/
theorem Peephole.Lemmas.sdiv_exact_mul_nuw_refines.drop_hc :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w} (nsw : Bool),
      Refines (Val.sdiv (Val.mul a (some c) true nsw) (some c) true) (Outcome.ok a) :=
  fun h => arith_not_refines_ok 7#3 rfl (by decide) (@h 3 (some 3#3) 2#3 false)

theorem Peephole.Lemmas.sdiv_exact_mul_nuw_refines.sat :
    ∃ (w : Nat) (_ : Val w) (c : BitVec w) (_ : Bool), ¬ c.toNat.isPowerOfTwo :=
  ⟨2, none, 3#2, false, by decide⟩

/-- `(1 * 1) % 2` is `1`. -/
theorem Peephole.Lemmas.urem_mul_nuw_of_umod_refines.drop_h :
    ¬ ∀ {w : Nat} (a : Val w) {c1 c0 : BitVec w} (nsw : Bool),
      Refines (Val.urem (Val.mul a (some c1) true nsw) (some c0)) (Outcome.ok (some 0#w)) :=
  fun h => arith_not_refines_ok 1#2 rfl (by decide) (@h 2 (some 1#2) 1#2 2#2 false)

theorem Peephole.Lemmas.urem_mul_nuw_of_umod_refines.sat :
    ∃ (w : Nat) (_ : Val w) (c1 c0 : BitVec w) (_ : Bool), c1 % c0 = 0#w :=
  ⟨1, none, 0#1, 1#1, false, by decide⟩

theorem Peephole.Lemmas.srem_mul_nsw_of_srem_refines.drop_h :
    ¬ ∀ {w : Nat} (a : Val w) {c1 c0 : BitVec w} (nuw : Bool),
      Refines (Val.srem (Val.mul a (some c1) nuw true) (some c0)) (Outcome.ok (some 0#w)) :=
  fun h => arith_not_refines_ok 1#3 rfl (by decide) (@h 3 (some 1#3) 1#3 2#3 false)

theorem Peephole.Lemmas.srem_mul_nsw_of_srem_refines.sat :
    ∃ (w : Nat) (_ : Val w) (c1 c0 : BitVec w) (_ : Bool), c1.srem c0 = 0#w :=
  ⟨1, none, 0#1, 1#1, false, by decide⟩

end LemmaStore.Counter
