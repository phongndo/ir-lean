import IRLean.Int
import IRLean.Refine

/-! # Facts about integer intrinsics, at every width, that InstSimplify's rewrites of them rest on

Each is about values, not about LLVM's code: a candidate for the lemma store, which any proof about these intrinsics
can use. The rewrite each one was cut from is named in its docstring. The facts they rest on about bits, such as where
`clz` and `ctz` land and what `bswap` does to a bit, are here too, and aren't offered.

The lemmas with a hypothesis have its counterexample at the end, which the store needs. -/

namespace Peephole.Lemmas

open IRLean

variable {w : Nat}

/-! ### Leading and trailing zeros -/

/-- A value whose highest set bit is `w - 1 - k` has `k` leading zeros. -/
theorem clz_eq_of_getLsbD {x : BitVec w} {k : Nat} (hk : k < w) (h1 : x.getLsbD (w - 1 - k) = true)
    (h0 : ∀ i, w - 1 - k < i → x.getLsbD i = false) : x.clz = BitVec.ofNat w k := by
  unfold BitVec.clz
  have hsplit := BitVec.clzAuxRec_eq_clzAuxRec_of_getLsbD_false (n := w - 1 - k) (k := k) h0
  rw [show w - 1 - k + k = w - 1 by omega] at hsplit
  rw [← hsplit]
  rcases hn : w - 1 - k with _ | n
  · rw [hn] at h1
    simp only [BitVec.clzAuxRec_zero, h1, ite_true]
    congr 1; omega
  · rw [hn] at h1
    simp only [BitVec.clzAuxRec_succ, h1, ite_true]
    congr 1; omega

/-- A value whose lowest set bit is `k` has `k` trailing zeros. -/
theorem ctz_eq_of_getLsbD {x : BitVec w} {k : Nat} (hk : k < w) (h1 : x.getLsbD k = true)
    (h0 : ∀ i, i < k → x.getLsbD i = false) : x.ctz = BitVec.ofNat w k := by
  rw [BitVec.ctz_eq_reverse_clz]
  apply clz_eq_of_getLsbD hk
  · rw [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
    simp only [show w - 1 - k < w by omega, decide_true, Bool.true_and]
    rw [show w - 1 - (w - 1 - k) = k by omega]; exact h1
  · intro i hi
    rw [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
    by_cases hiw : i < w
    · simp only [hiw, decide_true, Bool.true_and]; exact h0 _ (by omega)
    · simp [hiw]

/-- `cttz(1 << X)` refines `X`, whatever the flags: `1 << X` has only bit `X` set, or is poison.
`IS.simplifyBinaryIntrinsic.L6934`. -/
theorem cttz_shl_one_refines (a : Val w) (nuw nsw zeroPoison : Bool) :
    Refines (Val.cttz (Val.shl (some 1#w) a nuw nsw) zeroPoison) a := by
  cases a with
  | none => exact trivial
  | some y =>
  simp only [Val.shl]
  split
  · exact trivial
  · rename_i hok
    simp only [Val.shiftOk, Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not, BitVec.lt_def,
      BitVec.toNat_ofNat] at hok
    have hyw : y.toNat < w := by
      have := Nat.mod_le w (2 ^ w); omega
    have hw : 0 < w := by omega
    have hv : ((1#w) <<< y).getLsbD y.toNat = true := by
      simp [hyw]
    have hctz : ((1#w) <<< y).ctz = y := by
      rw [ctz_eq_of_getLsbD hyw hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      intro i hi
      simp [BitVec.getLsbD_shiftLeft, hi]
    have hne : ((1#w) <<< y) ≠ 0#w := by
      intro h; rw [h] at hv; simp at hv
    split
    · exact trivial
    · split
      · exact trivial
      · have hb : ((1#w <<< y) == 0#w) = false := by simpa using hne
        simp only [Val.cttz, hb, Bool.and_false, Bool.false_eq_true, ite_false, hctz]
        exact Refine.refl_val _


/-- `ctlz(C >> X)`, for a negative `C`, refines `X`, whatever the flags: the shift moves `C`'s sign bit to bit
`w - 1 - X`, with nothing above it, or is poison. `IS.simplifyBinaryIntrinsic.L6940`. -/
theorem ctlz_lshr_negative_refines {c : BitVec w} (hc : c.msb = true) (a : Val w) (exact zeroPoison : Bool) :
    Refines (Val.ctlz (Val.lshr (some c) a exact) zeroPoison) a := by
  cases a with
  | none => exact trivial
  | some y =>
  simp only [Val.lshr]
  split
  · exact trivial
  · rename_i hok
    simp only [Val.shiftOk, Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not, BitVec.lt_def,
      BitVec.toNat_ofNat] at hok
    have hyw : y.toNat < w := by
      have := Nat.mod_le w (2 ^ w); omega
    have hmsb : c.getLsbD (w - 1) = true := by rw [← hc, BitVec.msb_eq_getLsbD_last]
    have hv : (c >>> y).getLsbD (w - 1 - y.toNat) = true := by
      rw [BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, show y.toNat + (w - 1 - y.toNat) = w - 1 by omega]
      exact hmsb
    have hclz : (c >>> y).clz = y := by
      rw [clz_eq_of_getLsbD hyw hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      intro i hi
      rw [BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight]
      exact BitVec.getLsbD_of_ge _ _ (by omega)
    have hb : ((c >>> y) == 0#w) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h; rw [h] at hv; simp at hv
    split
    · exact trivial
    · simp only [Val.ctlz, hb, Bool.and_false, Bool.false_eq_true, ite_false, hclz]
      exact Refine.refl_val _

/-- `ctlz(C >>s X)`, for a negative `C`, refines 0, whatever the flags: an arithmetic shift keeps the sign bit, or is
poison. `IS.simplifyBinaryIntrinsic.L6942`. -/
theorem ctlz_ashr_negative_refines {c : BitVec w} (hc : c.msb = true) (a : Val w) (exact zeroPoison : Bool) :
    Refines (Val.ctlz (Val.ashr (some c) a exact) zeroPoison) (some 0#w) := by
  cases a with
  | none => exact trivial
  | some y =>
  simp only [Val.ashr]
  split
  · exact trivial
  · rename_i hok
    simp only [Val.shiftOk, Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not, BitVec.lt_def,
      BitVec.toNat_ofNat] at hok
    have hyw : y.toNat < w := by
      have := Nat.mod_le w (2 ^ w); omega
    have hmsb : c.getLsbD (w - 1) = true := by rw [← hc, BitVec.msb_eq_getLsbD_last]
    have hv : (c.sshiftRight' y).getLsbD (w - 1 - 0) = true := by
      rw [BitVec.getLsbD_sshiftRight']
      simp only [show ¬ w ≤ w - 1 - 0 by omega, decide_false, Bool.not_false, Bool.true_and]
      split
      · rw [show y.toNat + (w - 1 - 0) = w - 1 by omega]; exact hmsb
      · exact hc
    have hclz : (c.sshiftRight' y).clz = 0#w :=
      clz_eq_of_getLsbD (k := 0) (by omega) hv (fun i hi => BitVec.getLsbD_of_ge _ _ (by omega))
    have hb : ((c.sshiftRight' y) == 0#w) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h; rw [h] at hv; simp at hv
    split
    · exact trivial
    · simp only [Val.ctlz, hb, Bool.and_false, Bool.false_eq_true, ite_false, hclz]
      exact Refine.refl_val _

/-! ### Counting set bits -/

/-- Counting the set bits of `x` from bit `n` down: `acc` and one for each. -/
theorem cpopNatRec_of_single {x : BitVec w} {k : Nat} (hk : x.getLsbD k = true)
    (h0 : ∀ i, i ≠ k → x.getLsbD i = false) (n acc : Nat) :
    x.cpopNatRec n acc = acc + if k < n then 1 else 0 := by
  induction n generalizing acc with
  | zero => simp [BitVec.cpopNatRec]
  | succ n ih =>
    rw [BitVec.cpopNatRec_succ, ih]
    by_cases hn : n = k
    · subst hn; simp [hk]
    · rw [h0 n hn]
      by_cases hkn : k < n
      · simp [hkn, show k < n + 1 by omega]
      · simp [hkn, show ¬ k < n + 1 by omega]

/-- A power of two has one bit set. `IS.simplifyUnaryIntrinsic.L6614`. -/
theorem ctpop_of_isPowerOfTwo {x : BitVec w} (h : x.toNat.isPowerOfTwo) : Val.ctpop (some x) = some 1#w := by
  obtain ⟨k, hk⟩ := h
  have hkw : k < w := by
    have := x.isLt
    rw [hk] at this
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 this
  have hbit : ∀ i, x.getLsbD i = decide (i = k) := by
    intro i
    rw [BitVec.getLsbD, hk, Nat.testBit_two_pow]
    simp [eq_comm]
  simp only [Val.ctpop, Val.map₁, BitVec.cpop, Option.some.injEq]
  rw [cpopNatRec_of_single (k := k) (by simp [hbit]) (fun i hi => by simp [hbit, hi])]
  simp [hkw]

/-- A value with every bit but the lowest zero is its own count of set bits. `IS.simplifyUnaryIntrinsic.L6620`. -/
theorem ctpop_of_and_eq_zero {x : BitVec w} (h : x &&& (BitVec.allOnes w <<< 1) = 0#w) :
    Val.ctpop (some x) = some x := by
  have hbit : ∀ i, 0 < i → x.getLsbD i = false := by
    intro i hi
    by_cases hiw : i < w
    · have := congrArg (·.getLsbD i) h
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, hiw, decide_true,
        Bool.true_and, BitVec.getLsbD_zero] at this
      simpa [show ¬ i < 1 by omega, show i - 1 < w by omega] using this
    · exact BitVec.getLsbD_of_ge _ _ (by omega)
  simp only [Val.ctpop, Val.map₁, BitVec.cpop, Option.some.injEq]
  cases h0 : x.getLsbD 0
  · have hx : x = 0#w := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simp [h0]
      · simp [hbit i hpos]
    subst hx
    simp
  · rw [cpopNatRec_of_single (k := 0) h0 (fun i hi => hbit i (by omega))]
    have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with rfl | h
      · simp at h0
      · exact h
    simp only [hw, ite_true, Nat.zero_add]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp [hw, h0]
    · rw [hbit i hpos, BitVec.getLsbD_ofNat]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp [Nat.testBit_succ]

/-! ### `abs` -/

/-- `abs(x)` is its own `abs`: its sign bit is set only for `intMin`, which `abs` keeps. -/
theorem abs_abs_raw (x : BitVec w) :
    let y := if x.msb then -x else x
    (if y.msb then -y else y) = y := by
  dsimp only
  by_cases hx : x.msb
  · simp only [hx, ite_true, BitVec.neg_neg]
    by_cases hn : (-x).msb
    · simp only [hn, ite_true]
      have hm : x = BitVec.intMin w := by
        rw [BitVec.msb_neg] at hn
        refine Classical.byContradiction fun hne => ?_
        have h0 : x ≠ 0#w := by rintro rfl; simp at hx
        simp [h0, hne, hx] at hn
      subst hm; rw [BitVec.neg_intMin]
    · simp [hn]
  · simp [hx]

/-- `abs(abs(x))` refines `abs(x)`, whatever either's flag. `IS.simplifyBinaryIntrinsic.L6928`. -/
theorem abs_abs_refines (a : Val w) (p q : Bool) : Refines (Val.abs (Val.abs a p) q) (Val.abs a p) := by
  cases a with
  | none => exact trivial
  | some x =>
  by_cases hp : (p && x == BitVec.intMin w) = true
  · have h : Val.abs (some x) p = none := by simp only [Val.abs, hp, ite_true]
    rw [h]; exact trivial
  · have h : Val.abs (some x) p = some (if x.msb then -x else x) := by simp only [Val.abs, hp]; rfl
    have key := abs_abs_raw x
    generalize (if x.msb = true then -x else x) = y at h key
    rw [h]
    simp only [Val.abs]
    split
    · exact trivial
    · rw [key]; exact Refine.refl_val _

/-! ### `bswap` and `bitreverse` -/

/-- A bit of an or-fold is the start's or one of the terms'. -/
theorem getLsbD_foldl_or (f : Nat → BitVec w) (l : List Nat) (init : BitVec w) (j : Nat) :
    (l.foldl (fun acc i => acc ||| f i) init).getLsbD j = (init.getLsbD j || l.any fun i => (f i).getLsbD j) := by
  induction l generalizing init with
  | nil => simp
  | cons i l ih => simp [List.foldl, ih, Bool.or_assoc]

/-- Bit `j` of `bswap x`, at a width of whole bytes, is bit `j % 8` of the byte opposite `j`'s. -/
theorem getLsbD_bswapRaw (hw : w % 8 = 0) (x : BitVec w) {j : Nat} (hj : j < w) :
    (Val.bswapRaw x).getLsbD j = x.getLsbD (8 * (w / 8 - 1 - j / 8) + j % 8) := by
  unfold Val.bswapRaw
  rw [getLsbD_foldl_or (fun i => ((x >>> (8 * i)) &&& BitVec.ofNat w 0xff) <<< (w - 8 - 8 * i))]
  simp only [BitVec.getLsbD_zero, Bool.false_or]
  have h255 : ∀ k, (0xff : Nat).testBit k = decide (k < 8) := by
    intro k; rw [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, h255, hj, decide_true, Bool.true_and, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hle, hx, -, hlt⟩
    have hi' : i = w / 8 - 1 - j / 8 := by omega
    subst hi'
    rwa [show 8 * (w / 8 - 1 - j / 8) + (j - (w - 8 - 8 * (w / 8 - 1 - j / 8))) =
      8 * (w / 8 - 1 - j / 8) + j % 8 by omega] at hx
  · intro hx
    refine ⟨w / 8 - 1 - j / 8, by omega, by omega, ?_, by omega, by omega⟩
    rwa [show 8 * (w / 8 - 1 - j / 8) + (j - (w - 8 - 8 * (w / 8 - 1 - j / 8))) =
      8 * (w / 8 - 1 - j / 8) + j % 8 by omega]

/-- `bswap(bswap(x))` is `x`, at a width of whole bytes, which LLVM's verifier requires of `bswap`, in fact an even
number of them. `IS.simplifyUnaryIntrinsic.L6604`. -/
theorem bswap_bswap (hw : w % 8 = 0) (a : Val w) : Val.bswap (Val.bswap a) = a := by
  cases a with
  | none => rfl
  | some x =>
  simp only [Val.bswap, Val.map₁, Option.some.injEq]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_bswapRaw hw _ hj, getLsbD_bswapRaw hw _ (by omega)]
  congr 1
  omega

/-- `bitreverse(bitreverse(x))` is `x`. `IS.simplifyUnaryIntrinsic.L6609`. -/
theorem bitreverse_bitreverse (a : Val w) : Val.bitreverse (Val.bitreverse a) = a := by
  cases a with
  | none => rfl
  | some x => simp [Val.bitreverse, Val.map₁, BitVec.reverse_reverse_eq]

/-! ### Signed bounds -/

theorem toInt_le_intMax (x : BitVec w) : x.toInt ≤ (BitVec.intMax w).toInt := by
  rw [BitVec.toInt_intMax]; have := BitVec.toInt_lt (x := x); omega

theorem toInt_intMin_le (x : BitVec w) : (BitVec.intMin w).toInt ≤ x.toInt := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [BitVec.of_length_zero]
  · rw [BitVec.toInt_intMin, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]
    have := BitVec.le_toInt (x := x); push_cast; omega

/-! ### `umin`, `umax`, `smin` and `smax` -/

/-- Closes a goal about values `umin` and `umax` choose: each `if` split, each choice compared by `toNat`. -/
local macro "umm" : tactic => `(tactic| (
  simp only [Val.umax, Val.umin, Val.map₂, BitVec.ule_eq_decide, decide_eq_true_eq, Option.some.injEq] at *
  repeat' split
  all_goals first
    | rfl
    | trivial
    | (simp only [Option.some.injEq, ← BitVec.toNat_inj] at *; omega)
    | (show _ = _; simp only [Option.some.injEq, ← BitVec.toNat_inj] at *; omega)))

/-- The same for `smin` and `smax`, by `toInt`. -/
local macro "smm" : tactic => `(tactic| (
  simp only [Val.smax, Val.smin, Val.map₂, BitVec.sle_eq_decide, decide_eq_true_eq, Option.some.injEq] at *
  repeat' split
  all_goals first
    | rfl
    | trivial
    | (simp only [Option.some.injEq, ← BitVec.toInt_inj] at *; omega)
    | (show _ = _; simp only [Option.some.injEq, ← BitVec.toInt_inj] at *; omega)))


theorem umax_self (a : Val w) : Val.umax a a = a := by cases a <;> simp [Val.umax, Val.map₂]
theorem umin_self (a : Val w) : Val.umin a a = a := by cases a <;> simp [Val.umin, Val.map₂]
theorem smax_self (a : Val w) : Val.smax a a = a := by cases a <;> simp [Val.smax, Val.map₂]
theorem smin_self (a : Val w) : Val.smin a a = a := by cases a <;> simp [Val.smin, Val.map₂]

theorem umax_comm (a b : Val w) : Val.umax a b = Val.umax b a := by
  cases a <;> cases b <;> umm
theorem umin_comm (a b : Val w) : Val.umin a b = Val.umin b a := by
  cases a <;> cases b <;> umm
theorem smax_comm (a b : Val w) : Val.smax a b = Val.smax b a := by
  cases a <;> cases b <;> smm
theorem smin_comm (a b : Val w) : Val.smin a b = Val.smin b a := by
  cases a <;> cases b <;> smm

/-- `umax(x, -1)` refines -1: the saturation point. `IS.simplifyBinaryIntrinsic.L7020`. -/
theorem umax_allOnes_refines (a : Val w) :
    Refines (Val.umax a (some (BitVec.allOnes w))) (some (BitVec.allOnes w)) := by
  cases a with
  | none => exact trivial
  | some x =>
    have : x.ule (BitVec.allOnes w) = true := by
      rw [BitVec.ule_iff_toNat_le, BitVec.toNat_allOnes]; have := x.isLt; omega
    simp only [Val.umax, Val.map₂, this, ite_true]; exact Refine.refl_val _
theorem umin_zero_refines (a : Val w) : Refines (Val.umin a (some 0#w)) (some 0#w) := by
  cases a with
  | none => exact trivial
  | some x =>
    by_cases h : x.ule 0#w
    · have : x = 0#w := by
        rw [BitVec.ule_iff_toNat_le] at h; apply BitVec.eq_of_toNat_eq; simp at h ⊢; omega
      subst this; simp only [Val.umin, Val.map₂, h, ite_true]; exact Refine.refl_val _
    · simp only [Val.umin, Val.map₂, h]; exact Refine.refl_val _
theorem smax_intMax_refines (a : Val w) :
    Refines (Val.smax a (some (BitVec.intMax w))) (some (BitVec.intMax w)) := by
  cases a with
  | none => exact trivial
  | some x =>
    have : x.sle (BitVec.intMax w) = true := by
      rw [BitVec.sle_iff_toInt_le]; exact toInt_le_intMax x
    simp only [Val.smax, Val.map₂, this, ite_true]; exact Refine.refl_val _
theorem smin_intMin_refines (a : Val w) :
    Refines (Val.smin a (some (BitVec.intMin w))) (some (BitVec.intMin w)) := by
  cases a with
  | none => exact trivial
  | some x =>
    by_cases h : x.sle (BitVec.intMin w)
    · have : x = BitVec.intMin w := by
        rw [BitVec.sle_iff_toInt_le] at h; apply BitVec.eq_of_toInt_eq; have := toInt_intMin_le x; omega
      subst this; simp only [Val.smin, Val.map₂, h, ite_true]; exact Refine.refl_val _
    · simp only [Val.smin, Val.map₂, h]; exact Refine.refl_val _

/-- `umax(x, 0)` is `x`: the opposite of the saturation point. `IS.simplifyBinaryIntrinsic.L7027`. -/
theorem umax_zero (a : Val w) : Val.umax a (some 0#w) = a := by
  cases a with
  | none => rfl
  | some x =>
    by_cases h : x.ule 0#w
    · have : x = 0#w := by
        rw [BitVec.ule_iff_toNat_le] at h; apply BitVec.eq_of_toNat_eq; simp at h ⊢; omega
      subst this; simp [Val.umax, Val.map₂]
    · simp [Val.umax, Val.map₂, h]
theorem umin_allOnes (a : Val w) : Val.umin a (some (BitVec.allOnes w)) = a := by
  cases a with
  | none => rfl
  | some x =>
    have : x.ule (BitVec.allOnes w) = true := by
      rw [BitVec.ule_iff_toNat_le, BitVec.toNat_allOnes]; have := x.isLt; omega
    simp [Val.umin, Val.map₂, this]
theorem smax_intMin (a : Val w) : Val.smax a (some (BitVec.intMin w)) = a := by
  cases a with
  | none => rfl
  | some x =>
    by_cases h : x.sle (BitVec.intMin w)
    · have : x = BitVec.intMin w := by
        rw [BitVec.sle_iff_toInt_le] at h; apply BitVec.eq_of_toInt_eq; have := toInt_intMin_le x; omega
      subst this; simp [Val.smax, Val.map₂]
    · simp [Val.smax, Val.map₂, h]
theorem smin_intMax (a : Val w) : Val.smin a (some (BitVec.intMax w)) = a := by
  cases a with
  | none => rfl
  | some x =>
    have : x.sle (BitVec.intMax w) = true := by
      rw [BitVec.sle_iff_toInt_le]; exact toInt_le_intMax x
    simp [Val.smin, Val.map₂, this]

/-- `umax(umax(x, c), d)` is `umax(x, c)` if `c ≥ d`. `IS.simplifyBinaryIntrinsic.L7040`. -/
theorem umax_umax_of_ule (a : Val w) {c d : BitVec w} (h : d.ule c) :
    Val.umax (Val.umax a (some c)) (some d) = Val.umax a (some c) := by
  cases a <;> umm
theorem umin_umin_of_ule (a : Val w) {c d : BitVec w} (h : c.ule d) :
    Val.umin (Val.umin a (some c)) (some d) = Val.umin a (some c) := by
  cases a <;> umm
theorem smax_smax_of_sle (a : Val w) {c d : BitVec w} (h : d.sle c) :
    Val.smax (Val.smax a (some c)) (some d) = Val.smax a (some c) := by
  cases a <;> smm
theorem smin_smin_of_sle (a : Val w) {c d : BitVec w} (h : c.sle d) :
    Val.smin (Val.smin a (some c)) (some d) = Val.smin a (some c) := by
  cases a <;> smm

/-- `umax(umax(x, y), x)` is `umax(x, y)`. `IS.foldMinMaxSharedOp.L6698`. -/
theorem umax_umax_left (a b : Val w) : Val.umax (Val.umax a b) a = Val.umax a b := by
  cases a <;> cases b <;> umm
theorem umax_umax_right (a b : Val w) : Val.umax (Val.umax a b) b = Val.umax a b := by
  cases a <;> cases b <;> umm
theorem umin_umin_left (a b : Val w) : Val.umin (Val.umin a b) a = Val.umin a b := by
  cases a <;> cases b <;> umm
theorem umin_umin_right (a b : Val w) : Val.umin (Val.umin a b) b = Val.umin a b := by
  cases a <;> cases b <;> umm
theorem smax_smax_left (a b : Val w) : Val.smax (Val.smax a b) a = Val.smax a b := by
  cases a <;> cases b <;> smm
theorem smax_smax_right (a b : Val w) : Val.smax (Val.smax a b) b = Val.smax a b := by
  cases a <;> cases b <;> smm
theorem smin_smin_left (a b : Val w) : Val.smin (Val.smin a b) a = Val.smin a b := by
  cases a <;> cases b <;> smm
theorem smin_smin_right (a b : Val w) : Val.smin (Val.smin a b) b = Val.smin a b := by
  cases a <;> cases b <;> smm

/-- `umax(umin(x, y), x)` refines `x`. `IS.foldMinMaxSharedOp.L6701`. -/
theorem umax_umin_left_refines (a b : Val w) : Refines (Val.umax (Val.umin a b) a) a := by
  cases a <;> cases b <;> umm
theorem umax_umin_right_refines (a b : Val w) : Refines (Val.umax (Val.umin a b) b) b := by
  cases a <;> cases b <;> umm
theorem umin_umax_left_refines (a b : Val w) : Refines (Val.umin (Val.umax a b) a) a := by
  cases a <;> cases b <;> umm
theorem umin_umax_right_refines (a b : Val w) : Refines (Val.umin (Val.umax a b) b) b := by
  cases a <;> cases b <;> umm
theorem smax_smin_left_refines (a b : Val w) : Refines (Val.smax (Val.smin a b) a) a := by
  cases a <;> cases b <;> smm
theorem smax_smin_right_refines (a b : Val w) : Refines (Val.smax (Val.smin a b) b) b := by
  cases a <;> cases b <;> smm
theorem smin_smax_left_refines (a b : Val w) : Refines (Val.smin (Val.smax a b) a) a := by
  cases a <;> cases b <;> smm
theorem smin_smax_right_refines (a b : Val w) : Refines (Val.smin (Val.smax a b) b) b := by
  cases a <;> cases b <;> smm

/-- `umax(x, y)` is `x` if `x ≥ y`. `IS.simplifyBinaryIntrinsic.L7052`. -/
theorem umax_some_of_ule {x y : BitVec w} (h : y.ule x) : Val.umax (some x) (some y) = some x := by
  umm
theorem umin_some_of_ule {x y : BitVec w} (h : x.ule y) : Val.umin (some x) (some y) = some x := by
  umm
theorem smax_some_of_sle {x y : BitVec w} (h : y.sle x) : Val.smax (some x) (some y) = some x := by
  smm
theorem smin_some_of_sle {x y : BitVec w} (h : x.sle y) : Val.smin (some x) (some y) = some x := by
  smm

/-! ### Saturating arithmetic -/

/-- `uadd.sat(-1, y)` refines -1. `IS.simplifyBinaryIntrinsic.L7111`. -/
theorem uaddSat_allOnes_left_refines (b : Val w) :
    Refines (Val.uaddSat (some (BitVec.allOnes w)) b) (some (BitVec.allOnes w)) := by
  cases b with
  | none => exact trivial
  | some y =>
    show some _ = some _
    simp only [Option.some.injEq]
    split
    · rfl
    · rename_i h
      simp only [BitVec.uaddOverflow, BitVec.toNat_allOnes, decide_eq_true_eq, Nat.not_le] at h
      have : y = 0#w := by
        apply BitVec.eq_of_toNat_eq; have := Nat.two_pow_pos w; simp; omega
      subst this; simp
theorem uaddSat_allOnes_right_refines (a : Val w) :
    Refines (Val.uaddSat a (some (BitVec.allOnes w))) (some (BitVec.allOnes w)) := by
  cases a with
  | none => exact trivial
  | some x =>
    show some _ = some _
    simp only [Option.some.injEq]
    split
    · rfl
    · rename_i h
      simp only [BitVec.uaddOverflow, BitVec.toNat_allOnes, decide_eq_true_eq, Nat.not_le] at h
      have : x = 0#w := by
        apply BitVec.eq_of_toNat_eq; have := Nat.two_pow_pos w; simp; omega
      subst this; simp

/-- `uadd.sat(x, 0)` is `x`. `IS.simplifyBinaryIntrinsic.L7123`. -/
theorem uaddSat_zero (a : Val w) : Val.uaddSat a (some 0#w) = a := by
  cases a with
  | none => rfl
  | some x =>
    have : x.uaddOverflow 0#w = false := by
      simp [BitVec.uaddOverflow, x.isLt]
    simp [Val.uaddSat, Val.map₂, this]
/-- `uadd.sat(0, y)` is `y`. `IS.simplifyBinaryIntrinsic.L7126`. -/
theorem zero_uaddSat (b : Val w) : Val.uaddSat (some 0#w) b = b := by
  cases b with
  | none => rfl
  | some y =>
    have : (0#w).uaddOverflow y = false := by
      simp [BitVec.uaddOverflow, y.isLt]
    simp [Val.uaddSat, Val.map₂, this]
/-- `sadd.sat(x, 0)` is `x`. `IS.simplifyBinaryIntrinsic.L7123`. -/
theorem saddSat_zero (a : Val w) : Val.saddSat a (some 0#w) = a := by
  cases a with
  | none => rfl
  | some x =>
    have : x.saddOverflow 0#w = false := by
      have := BitVec.toInt_lt (x := x); have := BitVec.le_toInt (x := x)
      simp [BitVec.saddOverflow]; omega
    simp [Val.saddSat, Val.map₂, this]
/-- `sadd.sat(0, y)` is `y`. `IS.simplifyBinaryIntrinsic.L7126`. -/
theorem zero_saddSat (b : Val w) : Val.saddSat (some 0#w) b = b := by
  cases b with
  | none => rfl
  | some y =>
    have : (0#w).saddOverflow y = false := by
      have := BitVec.toInt_lt (x := y); have := BitVec.le_toInt (x := y)
      simp [BitVec.saddOverflow]; omega
    simp [Val.saddSat, Val.map₂, this]

/-- `usub.sat(0, y)` refines 0. `IS.simplifyBinaryIntrinsic.L7131`. -/
theorem zero_usubSat_refines (b : Val w) : Refines (Val.usubSat (some 0#w) b) (some 0#w) := by
  cases b with
  | none => exact trivial
  | some y =>
    show some _ = some _
    simp only [Option.some.injEq]
    split
    · rfl
    · rename_i h
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_true_eq, Nat.not_lt,
        Nat.le_zero] at h
      have : y = 0#w := BitVec.eq_of_toNat_eq (by simp [h])
      subst this; simp
/-- `usub.sat(x, -1)` refines 0. `IS.simplifyBinaryIntrinsic.L7131`. -/
theorem usubSat_allOnes_refines (a : Val w) : Refines (Val.usubSat a (some (BitVec.allOnes w))) (some 0#w) := by
  cases a with
  | none => exact trivial
  | some x =>
    show some _ = some _
    simp only [Option.some.injEq]
    split
    · rfl
    · rename_i h
      simp only [BitVec.ult, BitVec.toNat_allOnes, decide_eq_true_eq, Nat.not_lt] at h
      have : x = BitVec.allOnes w := by
        apply BitVec.eq_of_toNat_eq; have := x.isLt; simp; omega
      subst this; simp
/-- `usub.sat(x, x)` refines 0. `IS.simplifyBinaryIntrinsic.L7136`. -/
theorem usubSat_self_refines (a : Val w) : Refines (Val.usubSat a a) (some 0#w) := by
  cases a with
  | none => exact trivial
  | some x =>
    show some _ = some _
    simp [BitVec.ult]
/-- `ssub.sat(x, x)` refines 0. `IS.simplifyBinaryIntrinsic.L7136`. -/
theorem ssubSat_self_refines (a : Val w) : Refines (Val.ssubSat a a) (some 0#w) := by
  cases a with
  | none => exact trivial
  | some x =>
    show some _ = some _
    have : x.ssubOverflow x = false := by
      have := BitVec.toInt_lt (x := x); have := BitVec.le_toInt (x := x)
      simp [BitVec.ssubOverflow]; omega
    simp [this]
/-- `usub.sat(x, 0)` is `x`. `IS.simplifyBinaryIntrinsic.L7139`. -/
theorem usubSat_zero (a : Val w) : Val.usubSat a (some 0#w) = a := by
  cases a with
  | none => rfl
  | some x => simp [Val.usubSat, Val.map₂, BitVec.ult]
/-- `ssub.sat(x, 0)` is `x`. `IS.simplifyBinaryIntrinsic.L7139`. -/
theorem ssubSat_zero (a : Val w) : Val.ssubSat a (some 0#w) = a := by
  cases a with
  | none => rfl
  | some x =>
    have : x.ssubOverflow 0#w = false := by
      have := BitVec.toInt_lt (x := x); have := BitVec.le_toInt (x := x)
      simp [BitVec.ssubOverflow]; omega
    simp [Val.ssubSat, Val.map₂, this]

/-! ### Funnel shifts -/

/-- `fshl(x, y, s)` refines `x` when `s` is a multiple of the width. `IS.simplifyIntrinsic.L7387`. -/
theorem fshl_of_toNat_mod_eq_zero (a b : Val w) {s : BitVec w} (h : s.toNat % w = 0) :
    Refines (Val.fshl a b (some s)) a := by
  cases a <;> cases b <;> try exact trivial
  show some _ = some _
  simp [Val.fshlRaw, h]
/-- `fshr(x, y, s)` refines `y` when `s` is a multiple of the width. `IS.simplifyIntrinsic.L7387`. -/
theorem fshr_of_toNat_mod_eq_zero (a b : Val w) {s : BitVec w} (h : s.toNat % w = 0) :
    Refines (Val.fshr a b (some s)) b := by
  cases a <;> cases b <;> try exact trivial
  show some _ = some _
  simp [Val.fshrRaw, h]

/-- Shifting 0 in from both sides gives 0. `IS.simplifyIntrinsic.L7401`. -/
theorem fshl_zero_zero_refines (c : Val w) : Refines (Val.fshl (some 0#w) (some 0#w) c) (some 0#w) := by
  cases c with
  | none => exact trivial
  | some s =>
    show some _ = some _
    simp only [Val.fshlRaw, Option.some.injEq]
    split <;> simp
theorem fshr_zero_zero_refines (c : Val w) : Refines (Val.fshr (some 0#w) (some 0#w) c) (some 0#w) := by
  cases c with
  | none => exact trivial
  | some s =>
    show some _ = some _
    simp only [Val.fshrRaw, Option.some.injEq]
    split <;> simp

/-- Shifting -1 in from both sides gives -1. `IS.simplifyIntrinsic.L7405`. -/
theorem fshl_allOnes_allOnes_refines (c : Val w) :
    Refines (Val.fshl (some (BitVec.allOnes w)) (some (BitVec.allOnes w)) c) (some (BitVec.allOnes w)) := by
  cases c with
  | none => exact trivial
  | some s =>
    show some _ = some _
    simp only [Val.fshlRaw, Option.some.injEq]
    split
    · rfl
    · rename_i hk
      have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; exact hk (by simp [BitVec.of_length_zero]))
      have hlt : s.toNat % w < w := Nat.mod_lt _ hw
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
      by_cases hik : i < s.toNat % w
      · simp [hik]; omega
      · simp [hik]; omega
theorem fshr_allOnes_allOnes_refines (c : Val w) :
    Refines (Val.fshr (some (BitVec.allOnes w)) (some (BitVec.allOnes w)) c) (some (BitVec.allOnes w)) := by
  cases c with
  | none => exact trivial
  | some s =>
    show some _ = some _
    simp only [Val.fshrRaw, Option.some.injEq]
    split
    · rfl
    · rename_i hk
      have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; exact hk (by simp [BitVec.of_length_zero]))
      have hlt : s.toNat % w < w := Nat.mod_lt _ hw
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
      by_cases hik : i < w - s.toNat % w
      · simp [hik]; omega
      · simp [hik]; omega

/-- Shift amounts in range that sum to the width, as `C1 + C2 == BitWidth` says of them in `w` bits. -/
theorem toNat_add_eq_of_add_eq {c1 c2 : BitVec w} (h : c1 + c2 = BitVec.ofNat w w) (h1 : c1.toNat < w)
    (h2 : c2.toNat < w) : c1.toNat + c2.toNat = w := by
  have hw : w < 2 ^ w := Nat.lt_two_pow_self
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw] at this
  by_cases hs : c1.toNat + c2.toNat < 2 ^ w
  · rwa [Nat.mod_eq_of_lt hs] at this
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega

/-- The rotate `fshl(x >> c1, x << c2, c1)`, with `c1 + c2` the width, gives `x` back, whatever the shifts' flags.
`IS.simplifyIntrinsic.L7396`. -/
theorem fshl_lshr_shl_refines (a : Val w) {c1 c2 s : BitVec w} (h : c1 + c2 = BitVec.ofNat w w)
    (hs : s % BitVec.ofNat w w = c1) (exact nuw nsw : Bool) :
    Refines (Val.fshl (Val.lshr a (some c1) exact) (Val.shl a (some c2) nuw nsw) (some s)) a := by
  cases a with
  | none => exact trivial
  | some x =>
  simp only [Val.lshr, Val.shl]
  split
  · exact trivial
  rename_i h1
  split
  · cases (Val.shl (some x) (some c2) nuw nsw) <;> exact trivial
  split
  · exact trivial
  rename_i h2
  split
  · exact trivial
  split
  · exact trivial
  simp only [Val.shiftOk, Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not, BitVec.lt_def,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := w))] at h1 h2
  have hsum := toNat_add_eq_of_add_eq h h1 h2
  have hk : s.toNat % w = c1.toNat := by
    have := congrArg BitVec.toNat hs
    rwa [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := w))] at this
  show some _ = some _
  simp only [Val.fshlRaw, hk, Option.some.injEq]
  rw [ite_eq_right_iff.mpr (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', hi, decide_true, Bool.true_and]
  by_cases hic : i < c1.toNat
  · simp only [hic, decide_true, Bool.not_true, Bool.false_and, Bool.false_or]
    rw [show w - c1.toNat = c2.toNat by omega]
    simp [show c2.toNat + i < w by omega]
  · simp only [hic, decide_false, Bool.not_false, Bool.true_and]
    rw [show c1.toNat + (i - c1.toNat) = i by omega]
    cases x.getLsbD i <;> simp <;> intros <;> omega
/-- The rotate `fshr(x >> c1, x << c2, c2)`, with `c1 + c2` the width, gives `x` back, whatever the shifts' flags.
`IS.simplifyIntrinsic.L7396`. -/
theorem fshr_lshr_shl_refines (a : Val w) {c1 c2 s : BitVec w} (h : c1 + c2 = BitVec.ofNat w w)
    (hs : s % BitVec.ofNat w w = c2) (exact nuw nsw : Bool) :
    Refines (Val.fshr (Val.lshr a (some c1) exact) (Val.shl a (some c2) nuw nsw) (some s)) a := by
  cases a with
  | none => exact trivial
  | some x =>
  simp only [Val.lshr, Val.shl]
  split
  · exact trivial
  rename_i h1
  split
  · cases (Val.shl (some x) (some c2) nuw nsw) <;> exact trivial
  split
  · exact trivial
  rename_i h2
  split
  · exact trivial
  split
  · exact trivial
  simp only [Val.shiftOk, Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not, BitVec.lt_def,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := w))] at h1 h2
  have hsum := toNat_add_eq_of_add_eq h h1 h2
  have hk : s.toNat % w = c2.toNat := by
    have := congrArg BitVec.toNat hs
    rwa [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := w))] at this
  show some _ = some _
  simp only [Val.fshrRaw, hk, Option.some.injEq]
  rw [ite_eq_right_iff.mpr (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', hi, decide_true, Bool.true_and]
  rw [show w - c2.toNat = c1.toNat by omega]
  by_cases hic : i < c1.toNat
  · simp only [hic, decide_true, Bool.not_true, Bool.false_and, Bool.false_or]
    simp [show c2.toNat + i < w by omega]
  · simp only [hic, decide_false, Bool.not_false, Bool.true_and]
    rw [show c1.toNat + (i - c1.toNat) = i by omega]
    cases x.getLsbD i <;> simp <;> intros <;> omega

end Peephole.Lemmas

/-! ### Counterexamples, for the lemma store

For each hypothesis `h` of a lemma above that's offered, `drop_h` says the lemma without it is false, and `sat` that
its hypotheses can all hold, by the names and in the form `tools/store/store.py` looks for. Each counterexample is at
`i1` or `i2`, where `decide` can run the operations. -/

/-- In `i1`, `ctlz(0 >> 0)` is 1, not 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.ctlz_lshr_negative_refines.drop_hc :
    ¬ ∀ {w : Nat} {c : BitVec w} (a : IRLean.Val w) (exact zeroPoison : Bool),
      IRLean.Refines (IRLean.Val.ctlz (IRLean.Val.lshr (some c) a exact) zeroPoison) a := fun h => by
  have := (IRLean.Refine.val_iff _ _).1 (@h 1 0#1 (some 0#1) false false)
  revert this; decide

theorem LemmaStore.Counter.Peephole.Lemmas.ctlz_lshr_negative_refines.sat :
    ∃ (w : Nat) (c : BitVec w) (_ : IRLean.Val w) (_ _ : Bool), c.msb = true :=
  ⟨1, 1#1, none, false, false, by decide⟩

/-- In `i1`, `ctlz(0 >>s 0)` is 1, not 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.ctlz_ashr_negative_refines.drop_hc :
    ¬ ∀ {w : Nat} {c : BitVec w} (a : IRLean.Val w) (exact zeroPoison : Bool),
      IRLean.Refines (IRLean.Val.ctlz (IRLean.Val.ashr (some c) a exact) zeroPoison) (some 0#w) := fun h => by
  have := (IRLean.Refine.val_iff _ _).1 (@h 1 0#1 (some 0#1) false false)
  revert this; decide

theorem LemmaStore.Counter.Peephole.Lemmas.ctlz_ashr_negative_refines.sat :
    ∃ (w : Nat) (c : BitVec w) (_ : IRLean.Val w) (_ _ : Bool), c.msb = true :=
  ⟨1, 1#1, none, false, false, by decide⟩

/-- In `i1`, 0 has no bit set. -/
theorem LemmaStore.Counter.Peephole.Lemmas.ctpop_of_isPowerOfTwo.drop_h :
    ¬ ∀ {w : Nat} {x : BitVec w}, IRLean.Val.ctpop (some x) = some 1#w :=
  fun h => absurd (@h 1 0#1) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.ctpop_of_isPowerOfTwo.sat :
    ∃ (w : Nat) (x : BitVec w), x.toNat.isPowerOfTwo :=
  ⟨1, 1#1, ⟨0, rfl⟩⟩

/-- In `i2`, `0b10` has one bit set, not two. -/
theorem LemmaStore.Counter.Peephole.Lemmas.ctpop_of_and_eq_zero.drop_h :
    ¬ ∀ {w : Nat} {x : BitVec w}, IRLean.Val.ctpop (some x) = some x :=
  fun h => absurd (@h 2 2#2) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.ctpop_of_and_eq_zero.sat :
    ∃ (w : Nat) (x : BitVec w), x &&& BitVec.allOnes w <<< 1 = 0#w :=
  ⟨1, 0#1, by decide⟩

/-- In `i1`, which isn't whole bytes, `bswap` gives 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.bswap_bswap.drop_hw :
    ¬ ∀ {w : Nat} (a : IRLean.Val w), IRLean.Val.bswap (IRLean.Val.bswap a) = a :=
  fun h => absurd (@h 1 (some 1#1)) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.bswap_bswap.sat : ∃ (w : Nat) (_ : IRLean.Val w), w % 8 = 0 :=
  ⟨0, none, rfl⟩

/-- In `i1`, `umax(umax(0, 0), 1)` is 1. -/
theorem LemmaStore.Counter.Peephole.Lemmas.umax_umax_of_ule.drop_h :
    ¬ ∀ {w : Nat} (a : IRLean.Val w) {c d : BitVec w},
      IRLean.Val.umax (IRLean.Val.umax a (some c)) (some d) = IRLean.Val.umax a (some c) :=
  fun h => absurd (@h 1 (some 0#1) 0#1 1#1) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.umax_umax_of_ule.sat :
    ∃ (w : Nat) (_ : IRLean.Val w) (c d : BitVec w), d.ule c = true :=
  ⟨0, none, 0#0, 0#0, rfl⟩

/-- In `i1`, `umin(umin(1, 1), 0)` is 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.umin_umin_of_ule.drop_h :
    ¬ ∀ {w : Nat} (a : IRLean.Val w) {c d : BitVec w},
      IRLean.Val.umin (IRLean.Val.umin a (some c)) (some d) = IRLean.Val.umin a (some c) :=
  fun h => absurd (@h 1 (some 1#1) 1#1 0#1) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.umin_umin_of_ule.sat :
    ∃ (w : Nat) (_ : IRLean.Val w) (c d : BitVec w), c.ule d = true :=
  ⟨0, none, 0#0, 0#0, rfl⟩

/-- In `i1`, `smax(smax(-1, -1), 0)` is 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.smax_smax_of_sle.drop_h :
    ¬ ∀ {w : Nat} (a : IRLean.Val w) {c d : BitVec w},
      IRLean.Val.smax (IRLean.Val.smax a (some c)) (some d) = IRLean.Val.smax a (some c) :=
  fun h => absurd (@h 1 (some 1#1) 1#1 0#1) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.smax_smax_of_sle.sat :
    ∃ (w : Nat) (_ : IRLean.Val w) (c d : BitVec w), d.sle c = true :=
  ⟨0, none, 0#0, 0#0, rfl⟩

/-- In `i1`, `smin(smin(0, 0), -1)` is -1. -/
theorem LemmaStore.Counter.Peephole.Lemmas.smin_smin_of_sle.drop_h :
    ¬ ∀ {w : Nat} (a : IRLean.Val w) {c d : BitVec w},
      IRLean.Val.smin (IRLean.Val.smin a (some c)) (some d) = IRLean.Val.smin a (some c) :=
  fun h => absurd (@h 1 (some 0#1) 0#1 1#1) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.smin_smin_of_sle.sat :
    ∃ (w : Nat) (_ : IRLean.Val w) (c d : BitVec w), c.sle d = true :=
  ⟨0, none, 0#0, 0#0, rfl⟩

/-- In `i1`, `umax(0, 1)` is 1. -/
theorem LemmaStore.Counter.Peephole.Lemmas.umax_some_of_ule.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w}, IRLean.Val.umax (some x) (some y) = some x :=
  fun h => absurd (@h 1 0#1 1#1) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.umax_some_of_ule.sat : ∃ (w : Nat) (x y : BitVec w), y.ule x = true :=
  ⟨0, 0#0, 0#0, rfl⟩

/-- In `i1`, `umin(1, 0)` is 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.umin_some_of_ule.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w}, IRLean.Val.umin (some x) (some y) = some x :=
  fun h => absurd (@h 1 1#1 0#1) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.umin_some_of_ule.sat : ∃ (w : Nat) (x y : BitVec w), x.ule y = true :=
  ⟨0, 0#0, 0#0, rfl⟩

/-- In `i1`, `smax(-1, 0)` is 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.smax_some_of_sle.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w}, IRLean.Val.smax (some x) (some y) = some x :=
  fun h => absurd (@h 1 1#1 0#1) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.smax_some_of_sle.sat : ∃ (w : Nat) (x y : BitVec w), y.sle x = true :=
  ⟨0, 0#0, 0#0, rfl⟩

/-- In `i1`, `smin(0, -1)` is -1. -/
theorem LemmaStore.Counter.Peephole.Lemmas.smin_some_of_sle.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w}, IRLean.Val.smin (some x) (some y) = some x :=
  fun h => absurd (@h 1 0#1 1#1) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.smin_some_of_sle.sat : ∃ (w : Nat) (x y : BitVec w), x.sle y = true :=
  ⟨0, 0#0, 0#0, rfl⟩

/-- In `i2`, `fshl(1, 0, 1)` is 2. -/
theorem LemmaStore.Counter.Peephole.Lemmas.fshl_of_toNat_mod_eq_zero.drop_h :
    ¬ ∀ {w : Nat} (a b : IRLean.Val w) {s : BitVec w}, IRLean.Refines (IRLean.Val.fshl a b (some s)) a := fun h => by
  have := (IRLean.Refine.val_iff _ _).1 (@h 2 (some 1#2) (some 0#2) 1#2)
  revert this; decide

theorem LemmaStore.Counter.Peephole.Lemmas.fshl_of_toNat_mod_eq_zero.sat :
    ∃ (w : Nat) (_ _ : IRLean.Val w) (s : BitVec w), s.toNat % w = 0 :=
  ⟨0, none, none, 0#0, rfl⟩

/-- In `i2`, `fshr(0, 1, 1)` is 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.fshr_of_toNat_mod_eq_zero.drop_h :
    ¬ ∀ {w : Nat} (a b : IRLean.Val w) {s : BitVec w}, IRLean.Refines (IRLean.Val.fshr a b (some s)) b := fun h => by
  have := (IRLean.Refine.val_iff _ _).1 (@h 2 (some 0#2) (some 1#2) 1#2)
  revert this; decide

theorem LemmaStore.Counter.Peephole.Lemmas.fshr_of_toNat_mod_eq_zero.sat :
    ∃ (w : Nat) (_ _ : IRLean.Val w) (s : BitVec w), s.toNat % w = 0 :=
  ⟨0, none, none, 0#0, rfl⟩

/-- In `i2`, shifts by 1 and 0 don't sum to the width: `fshl(1 >> 1, 1 << 0, 1)` is 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.fshl_lshr_shl_refines.drop_h :
    ¬ ∀ {w : Nat} (a : IRLean.Val w) {c1 c2 s : BitVec w}, s % BitVec.ofNat w w = c1 → ∀ (exact nuw nsw : Bool),
      IRLean.Refines (IRLean.Val.fshl (IRLean.Val.lshr a (some c1) exact) (IRLean.Val.shl a (some c2) nuw nsw)
        (some s)) a := fun h => by
  have := (IRLean.Refine.val_iff _ _).1 (@h 2 (some 1#2) 1#2 0#2 1#2 (by decide) false false false)
  revert this; decide

/-- In `i2`, shifting by 0 rather than by the first shift's 1: `fshl(1 >> 1, 1 << 1, 0)` is 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.fshl_lshr_shl_refines.drop_hs :
    ¬ ∀ {w : Nat} (a : IRLean.Val w) {c1 c2 s : BitVec w}, c1 + c2 = BitVec.ofNat w w → ∀ (exact nuw nsw : Bool),
      IRLean.Refines (IRLean.Val.fshl (IRLean.Val.lshr a (some c1) exact) (IRLean.Val.shl a (some c2) nuw nsw)
        (some s)) a := fun h => by
  have := (IRLean.Refine.val_iff _ _).1 (@h 2 (some 1#2) 1#2 1#2 0#2 (by decide) false false false)
  revert this; decide

theorem LemmaStore.Counter.Peephole.Lemmas.fshl_lshr_shl_refines.sat :
    ∃ (w : Nat) (_ : IRLean.Val w) (c1 c2 s : BitVec w) (_ _ _ : Bool),
      c1 + c2 = BitVec.ofNat w w ∧ s % BitVec.ofNat w w = c1 :=
  ⟨2, none, 1#2, 1#2, 1#2, false, false, false, by decide, by decide⟩

/-- In `i2`, shifts by 0 and 1 don't sum to the width: `fshr(1 >> 0, 1 << 1, 1)` is 3. -/
theorem LemmaStore.Counter.Peephole.Lemmas.fshr_lshr_shl_refines.drop_h :
    ¬ ∀ {w : Nat} (a : IRLean.Val w) {c1 c2 s : BitVec w}, s % BitVec.ofNat w w = c2 → ∀ (exact nuw nsw : Bool),
      IRLean.Refines (IRLean.Val.fshr (IRLean.Val.lshr a (some c1) exact) (IRLean.Val.shl a (some c2) nuw nsw)
        (some s)) a := fun h => by
  have := (IRLean.Refine.val_iff _ _).1 (@h 2 (some 1#2) 0#2 1#2 1#2 (by decide) false false false)
  revert this; decide

/-- In `i2`, shifting by 0 rather than by the second shift's 1: `fshr(1 >> 1, 1 << 1, 0)` is 2. -/
theorem LemmaStore.Counter.Peephole.Lemmas.fshr_lshr_shl_refines.drop_hs :
    ¬ ∀ {w : Nat} (a : IRLean.Val w) {c1 c2 s : BitVec w}, c1 + c2 = BitVec.ofNat w w → ∀ (exact nuw nsw : Bool),
      IRLean.Refines (IRLean.Val.fshr (IRLean.Val.lshr a (some c1) exact) (IRLean.Val.shl a (some c2) nuw nsw)
        (some s)) a := fun h => by
  have := (IRLean.Refine.val_iff _ _).1 (@h 2 (some 1#2) 1#2 1#2 0#2 (by decide) false false false)
  revert this; decide

theorem LemmaStore.Counter.Peephole.Lemmas.fshr_lshr_shl_refines.sat :
    ∃ (w : Nat) (_ : IRLean.Val w) (c1 c2 s : BitVec w) (_ _ _ : Bool),
      c1 + c2 = BitVec.ofNat w w ∧ s % BitVec.ofNat w w = c2 :=
  ⟨2, none, 1#2, 1#2, 1#2, false, false, false, by decide, by decide⟩
