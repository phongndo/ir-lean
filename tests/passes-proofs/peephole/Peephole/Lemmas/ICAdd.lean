import IRLean.Int
import IRLean.Refine
import IRLean.Generic.BitVec
import Peephole.Lemmas.Add

/-! # Facts about `add` with a constant, at every width, that InstCombine's rewrites of it rest on

Each is about values, not about LLVM's code: a candidate for the lemma store. The rewrite each one was cut from is
named in its docstring, by its ID in `tests/llvm_scope/rewrites/instcombine.json`. The source is always an `add`, with
any flags, and the replacement is what InstCombine builds, with the flags it sets. For each hypothesis, the end of the
file shows the lemma is false without it. -/

namespace Peephole.Lemmas

open IRLean

variable {w v : Nat}

/-! ### Bit vectors -/

/-- Bits that `y` has and `x` hasn't: `x - y` is `x ^ y` when every bit of `y` is in `x`. -/
theorem sub_eq_xor_of_and_eq {x y : BitVec w} (h : x &&& y = y) : x - y = x ^^^ y := by
  have hz : (x ^^^ y) &&& y = 0#w := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (·.getLsbD i) h
    simp only [BitVec.getLsbD_and] at this
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_zero]
    cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all
  have hor : (x ^^^ y) ||| y = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (·.getLsbD i) h
    simp only [BitVec.getLsbD_and] at this
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor]
    cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all
  have hadd := (Generic.add_of_and_eq_zero hz).2.2
  rw [hor] at hadd
  calc x - y = (x ^^^ y) + y - y := by rw [hadd]
    _ = x ^^^ y := BitVec.add_sub_cancel _ _

/-- A bit vector with every bit of `k` set is at least `k`. -/
theorem le_of_and_eq {x k : BitVec w} (h : x &&& k = k) : k.toNat ≤ x.toNat := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_and] at this
  rw [← this]
  exact Nat.and_le_left

/-- `xor` of values commutes. -/
theorem xor_comm (a b : Val w) : Val.xor a b = Val.xor b a := by
  cases a <;> cases b <;> simp [Val.xor, Val.map₂, BitVec.xor_comm]

/-- An `add` that isn't poison is the sum. -/
theorem add_eq_some {x y r : BitVec w} {nuw nsw : Bool} (h : Val.add (some x) (some y) nuw nsw = some r) :
    r = x + y := by
  simp only [Val.add] at h
  split at h <;> simp_all

/-- `i1`'s two values. -/
theorem bv1_cases (b : BitVec 1) : b = 0#1 ∨ b = 1#1 := by
  rcases b with ⟨⟨n, hn⟩⟩
  rcases n with _ | _ | n
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

/-- `~x` is `-x - 1` as a signed integer. -/
theorem toInt_not_eq (p : BitVec w) (hw : 0 < w) : (~~~p).toInt = -p.toInt - 1 := by
  rw [BitVec.toInt_eq_msb_cond (~~~p), BitVec.toInt_eq_msb_cond p, BitVec.msb_not, BitVec.toNat_not]
  have hp := p.isLt
  have h1 := Nat.one_le_two_pow (n := w)
  cases hm : p.msb <;>
    simp only [hw, decide_true, Bool.true_and, Bool.not_false, Bool.not_true, ite_true, ite_false,
      Bool.false_eq_true] <;>
    generalize 2 ^ w = K at * <;> omega

/-- Shifting right arithmetically by `w - 1` leaves only copies of the sign bit. -/
theorem sshiftRight_width_sub_one (x : BitVec w) (hw : 0 < w) :
    x.sshiftRight' (BitVec.ofNat w (w - 1)) = if x.msb then BitVec.allOnes w else 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hk : (BitVec.ofNat w (w - 1)).toNat = w - 1 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := @Nat.lt_two_pow_self w; omega)
  rw [BitVec.getLsbD_sshiftRight', hk]
  split
  · next h =>
    have : i = 0 := by omega
    subst this
    simp only [Nat.add_zero, BitVec.msb_eq_getLsbD_last]
    cases x.getLsbD (w - 1) <;> simp [hi] <;> omega
  · cases hm : x.msb <;> simp [hi] <;> omega

/-! ### The rewrites -/

/-- `(c - x) + b` refines `(c + b) - x`, with no flags on either. `IC.AddSub.foldAddWithConstant.L874`. -/
theorem add_sub_left_refines (c x b : Val w) (f1 f2 nuw nsw : Bool) :
    Refines (Val.add (Val.sub c x f1 f2) b nuw nsw) (Val.sub (Val.add c b) x) := by
  cases c with
  | none => simp [Refines, Val.sub, Val.add, Refine.le]
  | some p =>
  cases x with
  | none => simp [Refines, Val.sub, Val.add, Refine.le]
  | some q =>
  cases b with
  | none => simp [Refines, Val.sub, Val.add, Refine.le]
  | some r =>
  simp only [Val.sub]
  split
  · exact Refine.val_none _
  · simp only [Val.add, Bool.false_and, Bool.or_false]
    refine add_refines_of_sum ?_
    grind

/-- `(x - y) + -1` refines `~y + x`, with no flags. `IC.AddSub.foldAddWithConstant.L881`. -/
theorem add_sub_allOnes_refines (x y : Val w) (f1 f2 nuw nsw : Bool) :
    Refines (Val.add (Val.sub x y f1 f2) (some (BitVec.allOnes w)) nuw nsw)
      (Val.add (Val.xor y (some (BitVec.allOnes w))) x) := by
  cases x with
  | none => simp [Refines, Val.sub, Val.add, Refine.le]
  | some p =>
  cases y with
  | none => simp [Refines, Val.sub, Val.add, Refine.le]
  | some q =>
  simp only [Val.sub]
  split
  · exact Refine.val_none _
  · simp only [Val.xor, Val.map₂, BitVec.xor_allOnes, Val.add, Bool.false_and, Bool.or_false]
    refine add_refines_of_sum ?_
    rw [BitVec.not_eq_neg_add, ← BitVec.neg_one_eq_allOnes]
    grind

/-- `zext b + c` refines `select b, c + 1, c` for an `i1` `b`. `IC.AddSub.foldAddWithConstant.L886`. -/
theorem add_zext_bool_refines (b : Val 1) (c : Val w) (nneg nuw nsw : Bool) :
    Refines (Val.add (Val.zext w b nneg) c nuw nsw) (IRLean.select b (Val.add c (some 1#w)) c) := by
  cases c with
  | none => rw [add_none_right]; exact Refine.val_none _
  | some y =>
  cases b with
  | none => exact Refine.val_none _
  | some x =>
  simp only [Val.zext]
  split
  · exact Refine.val_none _
  · rcases bv1_cases x with rfl | rfl
    · have : IRLean.select (some 0#1) (Val.add (some y) (some 1#w)) (some y) = some y := by
        simp [IRLean.select]
      rw [this]
      exact add_refines_of_sum (by simp)
    · have : IRLean.select (some 1#1) (Val.add (some y) (some 1#w)) (some y) = some (y + 1#w) := by
        simp [IRLean.select, Val.add]
      rw [this]
      exact add_refines_of_sum (by
        rw [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by omega), BitVec.add_comm])

/-- `(1#1).signExtend w` is all ones. -/
theorem signExtend_one (w : Nat) : (1#1).signExtend w = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_signExtend, BitVec.getLsbD_allOnes]
  split <;> simp [hi] <;> omega

/-- `(0#1).signExtend w` is 0. -/
theorem signExtend_zero (w : Nat) : (0#1).signExtend w = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_signExtend, BitVec.getLsbD_zero]
  split <;> simp

/-- `sext b + c` refines `select b, c - 1, c` for an `i1` `b`. `IC.AddSub.foldAddWithConstant.L891`. -/
theorem add_sext_bool_refines (b : Val 1) (c : Val w) (nuw nsw : Bool) :
    Refines (Val.add (Val.sext w b) c nuw nsw) (IRLean.select b (Val.sub c (some 1#w)) c) := by
  cases c with
  | none => rw [add_none_right]; exact Refine.val_none _
  | some y =>
  cases b with
  | none => exact Refine.val_none _
  | some x =>
  simp only [Val.sext, Val.map₁]
  rcases bv1_cases x with rfl | rfl
  · have : IRLean.select (some 0#1) (Val.sub (some y) (some 1#w)) (some y) = some y := by
      simp [IRLean.select]
    rw [this, signExtend_zero]
    exact add_refines_of_sum (by simp)
  · have : IRLean.select (some 1#1) (Val.sub (some y) (some 1#w)) (some y) = some (y - 1#w) := by
      simp [IRLean.select, Val.sub]
    rw [this, signExtend_one]
    exact add_refines_of_sum (by rw [← BitVec.neg_one_eq_allOnes]; grind)

/-- `~x + c` refines `(c - 1) - x`, with `nsw` if the `add` has it and `c - 1` doesn't overflow, except at `i1`, where
`1` is `-1`: there `add nsw (xor x, 1), 1` is 1 for `x = 1`, and `sub nsw 0, x` is poison. `IC.AddSub.foldAddWithConstant.L902`. -/
theorem add_not_refines (x : Val w) (c : BitVec w) (nuw nsw : Bool) (hw : w ≠ 1) :
    Refines (Val.add (Val.xor x (some (BitVec.allOnes w))) (some c) nuw nsw)
      (Val.sub (some (c - 1#w)) x false (nsw && !c.ssubOverflow 1#w)) := by
  cases x with
  | none => simp [Refines, Val.xor, Val.map₂, Val.add, Refine.le]
  | some p =>
  simp only [Val.xor, Val.map₂, BitVec.xor_allOnes, Val.add, Val.sub, Bool.false_and, Bool.false_or]
  have heq : ~~~p + c = c - 1#w - p := by rw [BitVec.not_eq_neg_add]; grind
  split
  · exact Refine.val_none _
  · next hsrc =>
    refine (Refine.val_iff _ _).2 (Or.inr ?_)
    rw [if_neg, heq]
    intro ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨⟨rfl, h1⟩, h2⟩ := ht
    have hs : ¬ (~~~p).saddOverflow c = true := by intro h; apply hsrc; simp [h]
    rcases Nat.lt_or_ge w 2 with hw2 | hw2
    · -- `w = 0`: every value is 0.
      have : w = 0 := by omega
      subst this
      rw [BitVec.of_length_zero (x := c), BitVec.of_length_zero (x := p)] at h2
      exact absurd h2 (by decide)
    · have hone : (1#w).toInt = 1 := BitVec.toInt_one (by omega)
      have hc1 := BitVec.toInt_sub_of_not_ssubOverflow (x := c) (y := 1#w) (by simp [h1])
      have hnot := toInt_not_eq p (by omega)
      simp only [BitVec.saddOverflow, BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq, not_or] at hs h2
      rw [hc1, hone] at h2
      omega

/-- `ashr y, w - 1` plus 1 refines 1 for a non-negative `y`, and 0 for a negative one. -/
theorem add_ashr_sign_one (y : BitVec w) (exact nuw nsw : Bool) (hw : 0 < w) :
    Refines (Val.add (Val.ashr (some y) (some (BitVec.ofNat w (w - 1))) exact) (some 1#w) nuw nsw)
      (some (if y.msb then 0#w else 1#w)) := by
  have hk : (BitVec.ofNat w (w - 1)).toNat = w - 1 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := @Nat.lt_two_pow_self w; omega)
  have hok : Val.shiftOk (BitVec.ofNat w (w - 1)) = true := by
    rw [Generic.shiftOk_iff, hk]; simp; omega
  simp only [Val.ashr, hok, Bool.not_true, Bool.false_eq_true, ite_false]
  split
  · exact Refine.val_none _
  · refine add_refines_of_sum ?_
    rw [sshiftRight_width_sub_one y hw]
    cases y.msb
    · simp
    · simp only [ite_true]; rw [← BitVec.neg_one_eq_allOnes, BitVec.add_left_neg]

/-- `ashr x, w - 1` plus 1 refines `zext (x > -1)`. `IC.AddSub.foldAddWithConstant.L911`. -/
theorem add_ashr_sign_one_refines (x : Val w) (exact nuw nsw : Bool) :
    Refines (Val.add (Val.ashr x (some (BitVec.ofNat w (w - 1))) exact) (some 1#w) nuw nsw)
      (Val.zext w (Val.icmpSgt x (some (BitVec.allOnes w))) false) := by
  cases x with
  | none => exact Refine.val_none _
  | some p =>
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [Refines, Val.ashr, Val.shiftOk, Val.add, Refine.le]
  have ht : Val.zext w (Val.icmpSgt (some p) (some (BitVec.allOnes w))) false =
      some (if p.msb then 0#w else 1#w) := by
    simp only [Val.icmpSgt, Val.icmp, Bool.false_and, Bool.false_eq_true, ite_false, Val.zext,
      Option.some.injEq]
    rw [BitVec.slt_eq_decide, BitVec.toInt_allOnes, if_pos hw]
    have hm := BitVec.toInt_eq_msb_cond p
    have := p.isLt
    cases hp : p.msb
    · have : -1 < p.toInt := by rw [hm]; simp only [hp, Bool.false_eq_true, ite_false]; omega
      simp only [this, decide_true, BitVec.ofBool_true, Bool.false_eq_true, ite_false]
      exact BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by omega)
    · have : ¬ -1 < p.toInt := by have := BitVec.toInt_neg_of_msb_true hp; omega
      simp only [this, decide_false, BitVec.ofBool_false, ite_true]
      exact BitVec.eq_of_toNat_eq (by simp)
  rw [ht]
  exact add_ashr_sign_one p exact nuw nsw hw

/-- An `or disjoint` with a constant, plus a constant, refines one `add` of the sum of the constants, `nuw` if the
`add` had it, and `nsw` if it had it and the constants' sum doesn't overflow. `IC.AddSub.foldAddWithConstant.L924`. -/
theorem add_or_disjoint_refines (x : Val w) (c1 c : BitVec w) (nuw nsw : Bool) :
    Refines (Val.add (Val.or x (some c1) true) (some c) nuw nsw)
      (Val.add x (some (c1 + c)) nuw (nsw && !c1.saddOverflow c)) := by
  cases x with
  | none => simp [Refines, Val.or, Val.add, Refine.le]
  | some p =>
  simp only [Val.or, Bool.true_and]
  split
  · exact Refine.val_none _
  · next hd =>
    have hz : p &&& c1 = 0#w := by simpa using hd
    obtain ⟨hu, hs, hsum⟩ := Generic.add_of_and_eq_zero hz
    rw [← hsum]
    simp only [Val.add]
    split
    · exact Refine.val_none _
    · next hsrc =>
      refine (Refine.val_iff _ _).2 (Or.inr ?_)
      rw [if_neg, BitVec.add_assoc]
      intro ht
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hsrc ht
      have hnat : (p + c1).toNat = p.toNat + c1.toNat := by
        have := BitVec.toNat_add_of_and_eq_zero hz; exact this
      rcases ht with ⟨rfl, ht⟩ | ⟨⟨rfl, h1⟩, ht⟩
      · apply hsrc; left; refine ⟨rfl, ?_⟩
        simp only [BitVec.uaddOverflow, decide_eq_true_eq] at ht ⊢
        rw [hnat]
        have : (c1 + c).toNat ≤ c1.toNat + c.toNat := by rw [BitVec.toNat_add]; exact Nat.mod_le _ _
        omega
      · apply hsrc; right; refine ⟨rfl, ?_⟩
        have hpc := BitVec.toInt_add_of_not_saddOverflow (x := p) (y := c1) (by simp [hs])
        have hcc := BitVec.toInt_add_of_not_saddOverflow (x := c1) (y := c) (by simp [h1])
        simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq] at ht ⊢
        rw [hpc]
        rw [hcc] at ht
        omega

/-- `(x | c2) + -c2` refines `(x | c2) ^ c2`: every bit of `c2` is set in `x | c2`. `IC.AddSub.foldAddWithConstant.L930`. -/
theorem add_or_neg_refines (x : Val w) (c : BitVec w) (d nuw nsw : Bool) :
    Refines (Val.add (Val.or x (some (-c)) d) (some c) nuw nsw) (Val.xor (Val.or x (some (-c)) d) (some (-c))) := by
  cases x with
  | none => simp [Refines, Val.or, Val.add, Refine.le]
  | some p =>
  simp only [Val.or]
  split
  · simp [Refines, Val.add, Refine.le]
  · simp only [Val.xor, Val.map₂]
    refine add_refines_of_sum ?_
    have hsub := sub_eq_xor_of_and_eq (x := p ||| -c) (y := -c) (by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
      cases p.getLsbD i <;> cases (-c).getLsbD i <;> rfl)
    rw [← hsub, BitVec.sub_neg]

/-- With `nuw` or `nsw`, `x + signmask` refines `x | signmask` with `disjoint`: either flag rules out `x` having the
sign bit. `IC.AddSub.foldAddWithConstant.L936`. -/
theorem add_signMask_disjoint_refines (x : Val w) (nuw nsw : Bool) (h : (nuw || nsw) = true) :
    Refines (Val.add x (some (BitVec.intMin w)) nuw nsw) (Val.or x (some (BitVec.intMin w)) true) := by
  cases x with
  | none => simp [Refines, Val.or, Val.add, Refine.le]
  | some p =>
  simp only [Val.add]
  split
  · exact Refine.val_none _
  · next hsrc =>
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · rw [BitVec.of_length_zero (x := p), BitVec.of_length_zero (x := BitVec.intMin 0)]
      simp [Val.or, Refines, Refine.le]
    have hmsb : p.msb = false := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, not_or, not_and] at hsrc h
      cases hp : p.msb
      · rfl
      · exfalso
        have hp2 : 2 ^ (w - 1) ≤ p.toNat := by
          rw [BitVec.msb_eq_decide] at hp; simpa using hp
        rcases h with rfl | rfl
        · apply hsrc.1 rfl
          simp only [BitVec.uaddOverflow, BitVec.toNat_intMin, decide_eq_true_eq]
          rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]
          have : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
          omega
        · apply hsrc.2 rfl
          rw [BitVec.saddOverflow_eq, hp, BitVec.msb_intMin, add_intMin, BitVec.msb_xor, hp,
            BitVec.msb_intMin]
          simp [hw]
    have hz : p &&& BitVec.intMin w = 0#w := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_and, BitVec.getLsbD_intMin, BitVec.getLsbD_zero]
      by_cases hi' : i = w - 1
      · subst hi'; rw [← BitVec.msb_eq_getLsbD_last, hmsb]; simp
      · have : ¬ (i + 1 = w) := by omega
        simp [this]
    simp only [Val.or, hz, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false]
    refine (Refine.val_iff _ _).2 (Or.inr ?_)
    rw [(Generic.add_of_and_eq_zero hz).2.2]

/-- `x + signmask` refines `x ^ signmask`. `IC.AddSub.foldAddWithConstant.L940`. -/
theorem add_signMask_xor_refines (x : Val w) (nuw nsw : Bool) :
    Refines (Val.add x (some (BitVec.intMin w)) nuw nsw) (Val.xor x (some (BitVec.intMin w))) := by
  cases x with
  | none => simp [Refines, Val.xor, Val.add, Refine.le]
  | some p =>
  simp only [Val.xor, Val.map₂]
  exact add_refines_of_sum (add_intMin p)

/-- `(x ^ signmask) + c` refines `x + (signmask ^ c)`, with no flags. `IC.AddSub.foldAddWithConstant.L952`. -/
theorem add_xor_signMask_const_refines (x : Val w) (c : BitVec w) (nuw nsw : Bool) :
    Refines (Val.add (Val.xor x (some (BitVec.intMin w))) (some c) nuw nsw)
      (Val.add x (some (BitVec.intMin w ^^^ c))) := by
  cases x with
  | none => simp [Refines, Val.xor, Val.map₂, Val.add, Refine.le]
  | some p =>
  simp only [Val.xor, Val.map₂]
  have : Val.add (some p) (some (BitVec.intMin w ^^^ c)) = some ((p ^^^ BitVec.intMin w) + c) := by
    simp only [Val.add, Bool.false_and, Bool.or_false, Bool.false_eq_true, ite_false, Option.some.injEq]
    rw [← add_intMin p, BitVec.xor_comm (BitVec.intMin w) c, ← add_intMin c]
    grind
  rw [this]
  exact add_refines_of_sum rfl

/-- `(x ^ c2) + c` refines `(c2 + c) - x` where `x` has no bit outside `c2`'s. `IC.AddSub.foldAddWithConstant.L959`. -/
theorem add_xor_mask_refines {x c2 : BitVec w} (h : x &&& ~~~c2 = 0#w) (c : BitVec w) (nuw nsw : Bool) :
    Refines (Val.add (some (x ^^^ c2)) (some c) nuw nsw) (Val.sub (some (c2 + c)) (some x)) := by
  have hx : c2 &&& x = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (·.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
      BitVec.getLsbD_zero] at this
    simp only [BitVec.getLsbD_and]
    cases hc : c2.getLsbD i <;> cases hxi : x.getLsbD i <;> simp_all
  have hsub := sub_eq_xor_of_and_eq hx
  simp only [Val.sub, Bool.false_and, Bool.or_false, Bool.false_eq_true, ite_false]
  refine add_refines_of_sum ?_
  rw [BitVec.xor_comm, ← hsub]
  grind

/-- `sext b + 1` refines `zext ~b` for an `i1` `b`. `IC.AddSub.foldAddWithConstant.L989`. -/
theorem add_sext_bool_one_refines (b : Val 1) (nuw nsw : Bool) :
    Refines (Val.add (Val.sext w b) (some 1#w) nuw nsw) (Val.zext w (Val.xor b (some (BitVec.allOnes 1))) false) := by
  cases b with
  | none => simp [Refines, Val.sext, Val.map₁, Val.add, Refine.le]
  | some x =>
  simp only [Val.sext, Val.map₁, Val.xor, Val.map₂, Val.zext, Bool.false_and, Bool.false_eq_true, ite_false]
  refine add_refines_of_sum ?_
  rcases bv1_cases x with rfl | rfl
  · rw [signExtend_zero, BitVec.zero_add]
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · rfl
    · exact (BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by omega)).symm
  · rw [signExtend_one, ← BitVec.neg_one_eq_allOnes, BitVec.add_left_neg]
    exact BitVec.eq_of_toNat_eq (by simp)

/-- `ashr (shl x, w - 1), w - 1` plus 1 refines `~x & 1`. `IC.AddSub.foldAddWithConstant.L997`. -/
theorem add_ashr_shl_sign_one_refines (x : Val w) (f1 f2 exact nuw nsw : Bool) :
    Refines (Val.add (Val.ashr (Val.shl x (some (BitVec.ofNat w (w - 1))) f1 f2) (some (BitVec.ofNat w (w - 1))) exact)
        (some 1#w) nuw nsw)
      (Val.and (Val.xor x (some (BitVec.allOnes w))) (some 1#w)) := by
  cases x with
  | none => exact Refine.val_none _
  | some p =>
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [Refines, Val.shl, Val.shiftOk, Val.ashr, Val.add, Refine.le]
  have hk : (BitVec.ofNat w (w - 1)).toNat = w - 1 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := @Nat.lt_two_pow_self w; omega)
  have hmsb : (p <<< BitVec.ofNat w (w - 1)).msb = p.getLsbD 0 := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.shiftLeft_eq', hk, BitVec.getLsbD_shiftLeft]
    have : ¬ (w - 1 < w - 1) := by omega
    simp [this]
    omega
  have ht : Val.and (Val.xor (some p) (some (BitVec.allOnes w))) (some 1#w) =
      some (if p.getLsbD 0 then 0#w else 1#w) := by
    simp only [Val.and, Val.xor, Val.map₂, BitVec.xor_allOnes, Option.some.injEq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
    cases hp : p.getLsbD 0 <;> by_cases h0 : i = 0 <;> simp_all
  rw [ht]
  simp only [Val.shl]
  split
  · exact Refine.val_none _
  split
  · exact Refine.val_none _
  split
  · exact Refine.val_none _
  · have := add_ashr_sign_one (p <<< BitVec.ofNat w (w - 1)) exact nuw nsw hw
    rwa [hmsb] at this

/-- `umax(x, -c) + c` refines `usub.sat(x, -c)`: the `umax` is at least `-c`. `IC.AddSub.foldAddWithConstant.L1003`. -/
theorem add_umax_refines (x : Val w) (c : BitVec w) (nuw nsw : Bool) :
    Refines (Val.add (Val.umax x (some (-c))) (some c) nuw nsw) (Val.usubSat x (some (-c))) := by
  cases x with
  | none => exact Refine.val_none _
  | some p =>
  simp only [Val.umax, Val.usubSat, Val.map₂]
  refine add_refines_of_sum ?_
  by_cases h : p.toNat ≤ (-c).toNat
  · have h1 : BitVec.ule p (-c) = true := by simp only [BitVec.ule, decide_eq_true_eq]; exact h
    rw [if_pos h1, BitVec.add_left_neg]
    by_cases he : p = -c
    · subst he
      have : BitVec.ult (-c) (-c) = false := by simp [BitVec.ult]
      rw [this]
      simp
    · have hne : p.toNat ≠ (-c).toNat := fun h' => he (BitVec.eq_of_toNat_eq h')
      have : BitVec.ult p (-c) = true := by simp only [BitVec.ult, decide_eq_true_eq]; omega
      rw [this]
      simp
  · have h1 : BitVec.ule p (-c) = false := by simp only [BitVec.ule, decide_eq_false_iff_not]; exact h
    have h2 : BitVec.ult p (-c) = false := by simp only [BitVec.ult, decide_eq_false_iff_not]; omega
    rw [h1, h2]
    simp [BitVec.sub_neg]

/-- `zext (x - n) + zext n` refines `zext x` where `x ≥ n`: the narrow subtraction doesn't wrap.
`IC.AddSub.foldAddWithConstant.L1020`. -/
theorem add_zext_add_neg_refines {x n : BitVec v} (h : n.toNat ≤ x.toNat) (f1 f2 nneg nuw nsw : Bool) :
    Refines (Val.add (Val.zext w (Val.add (some x) (some (-n)) f1 f2) nneg) (some (n.setWidth w)) nuw nsw)
      (Val.zext w (some x) false) := by
  have hin : Val.add (some x) (some (-n)) f1 f2 = none ∨ Val.add (some x) (some (-n)) f1 f2 = some (x + -n) := by
    simp only [Val.add]; split <;> simp
  rcases hin with h1 | h1
  · rw [h1]; exact Refine.val_none _
  rw [h1]
  simp only [Val.zext, Bool.false_and, Bool.false_eq_true, ite_false]
  split
  · exact Refine.val_none _
  refine add_refines_of_sum ?_
  apply BitVec.eq_of_toNat_eq
  have hsub : (x + -n).toNat = x.toNat - n.toNat := by
    rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using h)]
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, hsub]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.sub_add_cancel h]

end Peephole.Lemmas
