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
theorem sshiftRight_width_sub_one (x : BitVec w) :
    x.sshiftRight' (BitVec.ofNat w (w - 1)) = if x.msb then BitVec.allOnes w else 0#w := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact Subsingleton.elim _ _
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

/-- The bits of `-2^k`: those at `k` and above. -/
theorem getLsbD_neg_twoPow {k i : Nat} :
    (-BitVec.twoPow w k).getLsbD i = (decide (k ≤ i) && decide (i < w)) := by
  by_cases hk : w ≤ k
  · have : BitVec.twoPow w k = 0#w := BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_twoPow_of_le hk])
    rw [this, BitVec.neg_zero]
    by_cases h : k ≤ i
    · have : ¬ i < w := by omega
      simp [this]
    · simp [h]
  have hk : k < w := by omega
  rw [BitVec.getLsbD_neg, BitVec.getLsbD_twoPow]
  by_cases hi : i < w
  · have : (∃ j < i, (BitVec.twoPow w k).getLsbD j = true) ↔ k < i := by
      simp only [BitVec.getLsbD_twoPow, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj, -, rfl⟩; exact hj
      · intro h; exact ⟨k, h, hk, rfl⟩
    simp only [this, hk, hi, decide_true, Bool.true_and, Bool.and_true]
    by_cases hki : k = i
    · subst hki; simp
    · by_cases hlt : k < i <;> simp [hki, hlt] <;> omega
  · have : ¬ (k = i) := by omega
    simp [hi, this]

/-- The bits of `2^k`, for `k` inside the width. -/
theorem getLsbD_twoPow_of_lt {k : Nat} (hk : k < w) (i : Nat) :
    (BitVec.twoPow w k).getLsbD i = decide (i = k) := by
  rw [BitVec.getLsbD_twoPow]
  by_cases h : i = k
  · subst h; simp [hk]
  · have : ¬ k = i := fun e => h e.symm
    simp [h, this]

/-- Two bit vectors with no bit in common add to their `or`. -/
theorem add_eq_or {x y : BitVec w} (h : ∀ i, x.getLsbD i = true → y.getLsbD i = false) : x + y = x ||| y := by
  refine (Generic.add_of_and_eq_zero ?_).2.2
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  cases hx : x.getLsbD i
  · rfl
  · simp [h i hx]

/-- Shifting `x` left by `s` and arithmetically back extends its bit `w - 1 - s` over those above it. -/
theorem sshiftRight_shiftLeft_getLsbD (x : BitVec w) {s i : Nat} (hs : s < w) (hi : i < w) :
    ((x <<< s).sshiftRight s).getLsbD i = if i < w - s then x.getLsbD i else x.getLsbD (w - 1 - s) := by
  rw [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
  have hw : ¬ (w ≤ i) := by omega
  have hw1 : w - 1 < w := by omega
  have hw2 : ¬ (w - 1 < s) := by omega
  by_cases h : i < w - s
  · have h1 : s + i < w := by omega
    have h2 : ¬ (s + i < s) := by omega
    simp only [hw, h1, h2, h, decide_false, decide_true, Bool.not_false, Bool.true_and, ite_true,
      show s + i - s = i by omega]
  · have h1 : ¬ (s + i < w) := by omega
    simp only [hw, h1, h, hw1, hw2, decide_false, decide_true, Bool.not_false, Bool.true_and, ite_false]

/-- `(x ^ c2) + c`, where `x` has no bit above `k` and one of `c` and `c2` is `2^k` and the other its negation, is
`x` extended from bit `k`: the sign extension in a register. -/
theorem xor_add_sext {x : BitVec w} {k : Nat} (hx : ∀ i, k < i → x.getLsbD i = false)
    {c c2 : BitVec w} (hc : (c = BitVec.twoPow w k ∧ c2 = -c) ∨ (c2 = BitVec.twoPow w k ∧ c = -c2)) :
    (x ^^^ c2) + c = (x <<< (w - 1 - k)).sshiftRight (w - 1 - k) := by
  by_cases hk : w ≤ k + 1
  · -- No shift: `2^k` is the sign bit, its own negation, or past the width, and 0.
    rw [show w - 1 - k = 0 by omega, BitVec.shiftLeft_zero, BitVec.sshiftRight_zero]
    have hadd : -BitVec.twoPow w k = BitVec.twoPow w k ∧
        ∀ y : BitVec w, (y ^^^ BitVec.twoPow w k) + BitVec.twoPow w k = y := by
      rcases Nat.lt_or_ge k w with hkw | hkw
      · obtain rfl : k = w - 1 := by omega
        refine ⟨BitVec.neg_intMin, fun y => ?_⟩
        show (y ^^^ BitVec.intMin w) + BitVec.intMin w = y
        rw [add_intMin, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      · have h0 : BitVec.twoPow w k = 0#w := BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_twoPow_of_le hkw])
        rw [h0]
        exact ⟨BitVec.neg_zero w, fun y => by simp⟩
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hadd.1]; exact hadd.2 x
    · rw [hadd.1]; exact hadd.2 x
  have hk : k + 1 < w := by omega
  have hs : w - 1 - k < w := by omega
  have hws : w - (w - 1 - k) = k + 1 := by omega
  have ht := getLsbD_twoPow_of_lt (w := w) (k := k) (by omega)
  have hn : ∀ i, (-BitVec.twoPow w k).getLsbD i = (decide (k ≤ i) && decide (i < w)) :=
    fun i => getLsbD_neg_twoPow
  have hn1 : ∀ i, (-BitVec.twoPow w (k + 1)).getLsbD i = (decide (k + 1 ≤ i) && decide (i < w)) :=
    fun i => getLsbD_neg_twoPow
  -- Both sides are `x` with bit `k` copied over every bit above it.
  have hE : ∀ i, i < w → ((x <<< (w - 1 - k)).sshiftRight (w - 1 - k)).getLsbD i =
      if i ≤ k then x.getLsbD i else x.getLsbD k := by
    intro i hi
    rw [sshiftRight_shiftLeft_getLsbD x hs hi, hws, show w - 1 - (w - 1 - k) = k by omega]
    by_cases h : i ≤ k
    · simp [h, show i < k + 1 by omega]
    · simp [h, show ¬ i < k + 1 by omega]
  -- The value with bit `k` clear is `x`, and with it set is `x - 2^(k+1)`, which sets every bit above `k`.
  have hclear : x.getLsbD k = false → x = (x <<< (w - 1 - k)).sshiftRight (w - 1 - k) := by
    intro hxk
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [hE i hi]
    by_cases hik : i ≤ k
    · simp [hik]
    · simp only [hik, ite_false, hxk]; exact hx i (by omega)
  have hset : x.getLsbD k = true →
      x + -BitVec.twoPow w (k + 1) = (x <<< (w - 1 - k)).sshiftRight (w - 1 - k) := by
    intro hxk
    rw [add_eq_or]
    · apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [hE i hi, BitVec.getLsbD_or, hn1]
      by_cases hik : i ≤ k
      · have : ¬ (k + 1 ≤ i) := by omega
        simp [hik, this]
      · have : k + 1 ≤ i := by omega
        simp [hik, this, hi, hxk]
    · intro j hj; rw [hn1]
      by_cases hjk : k + 1 ≤ j
      · rw [hx j (by omega)] at hj; cases hj
      · simp [hjk]
  have h2 : BitVec.twoPow w k + BitVec.twoPow w k = BitVec.twoPow w (k + 1) := by
    apply BitVec.eq_of_toNat_eq
    have hlt := Nat.pow_lt_pow_right (a := 2) (by omega) hk
    rw [BitVec.toNat_add, BitVec.toNat_twoPow_of_lt (by omega), BitVec.toNat_twoPow_of_lt (by omega)]
    rw [Nat.pow_succ] at hlt ⊢
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `(x ^ -2^k) + 2^k`
    cases hxk : x.getLsbD k
    · -- `x ^ -2^k` is `x + -2^k`, with no carry.
      have hor : x ^^^ -BitVec.twoPow w k = x + -BitVec.twoPow w k := by
        rw [add_eq_or]
        · apply BitVec.eq_of_getLsbD_eq; intro j hj
          rw [BitVec.getLsbD_xor, BitVec.getLsbD_or, hn]
          by_cases hjk : k ≤ j
          · have : x.getLsbD j = false := by
              rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
              · exact hxk
              · exact hx j hlt
            simp [this]
          · simp [hjk]
        · intro j hj; rw [hn]
          by_cases hjk : k ≤ j
          · rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
            · rw [hxk] at hj; cases hj
            · rw [hx j hlt] at hj; cases hj
          · simp [hjk]
      rw [hor, BitVec.add_assoc, BitVec.add_left_neg, BitVec.add_zero]
      exact hclear hxk
    · -- `x ^ -2^k` has bit `k` clear, so adding `2^k` sets it with no carry, which is `x - 2^(k+1)`.
      have hval : (x ^^^ -BitVec.twoPow w k) + BitVec.twoPow w k = x + -BitVec.twoPow w (k + 1) := by
        rw [add_eq_or, add_eq_or]
        · apply BitVec.eq_of_getLsbD_eq; intro i hi
          rw [BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_xor, hn, hn1, ht]
          by_cases hik : i = k
          · subst hik; simp [hxk]
          · by_cases hlt : k < i
            · have : k + 1 ≤ i := hlt
              have hxi := hx i hlt
              simp only [hik, Nat.le_of_lt hlt, this, hi, hxi, decide_true, decide_false,
                Bool.false_xor, Bool.false_or, Bool.and_self, Bool.or_false]
            · have h1 : ¬ k ≤ i := by omega
              have h2' : ¬ k + 1 ≤ i := by omega
              simp [hik, h1, h2']
        · intro j hj; rw [hn1]
          by_cases hjk : k + 1 ≤ j
          · rw [hx j (by omega)] at hj; cases hj
          · simp [hjk]
        · intro j hj; rw [ht]
          by_cases hjk : j = k
          · subst hjk; rw [BitVec.getLsbD_xor, hn, hxk] at hj; simp at hj; omega
          · simp [hjk]
      rw [hval]
      exact hset hxk
  · -- `(x ^ 2^k) + -2^k`
    cases hxk : x.getLsbD k
    · -- `x ^ 2^k` is `x + 2^k`.
      have hor : x ^^^ BitVec.twoPow w k = x + BitVec.twoPow w k := by
        rw [add_eq_or]
        · apply BitVec.eq_of_getLsbD_eq; intro j hj
          rw [BitVec.getLsbD_xor, BitVec.getLsbD_or, ht]
          by_cases hjk : j = k
          · subst hjk; simp [hxk]
          · simp [hjk]
        · intro j hj; rw [ht]; by_cases hjk : j = k
          · subst hjk; rw [hxk] at hj; cases hj
          · simp [hjk]
      rw [hor, BitVec.add_assoc, BitVec.add_right_neg, BitVec.add_zero]
      exact hclear hxk
    · -- `x ^ 2^k` is `x - 2^k`, and taking `2^k` again leaves `x - 2^(k+1)`.
      have hsub : x ^^^ BitVec.twoPow w k = x - BitVec.twoPow w k := by
        refine (sub_eq_xor_of_and_eq ?_).symm
        apply BitVec.eq_of_getLsbD_eq; intro j hj
        rw [BitVec.getLsbD_and, ht]
        by_cases hjk : j = k
        · subst hjk; simp [hxk]
        · simp [hjk]
      have hval : (x ^^^ BitVec.twoPow w k) + -BitVec.twoPow w k = x + -BitVec.twoPow w (k + 1) := by
        rw [hsub, ← h2]; grind
      rw [hval]
      exact hset hxk

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
theorem add_not_refines (x : Val w) (c : BitVec w) (nuw nsw : Bool) (hw : w ≠ 1 ∨ nsw = false) :
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
    rw [ite_eq_right, heq]
    intro ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨⟨rfl, h1⟩, h2⟩ := ht
    have hw : w ≠ 1 := hw.resolve_right (by simp)
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
theorem add_ashr_sign_one (y : BitVec w) (exact nuw nsw : Bool) :
    Refines (Val.add (Val.ashr (some y) (some (BitVec.ofNat w (w - 1))) exact) (some 1#w) nuw nsw)
      (some (if y.msb then 0#w else 1#w)) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [Refines, Val.ashr, Val.shiftOk, Val.add, Refine.le]
  have hk : (BitVec.ofNat w (w - 1)).toNat = w - 1 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := @Nat.lt_two_pow_self w; omega)
  have hok : Val.shiftOk (BitVec.ofNat w (w - 1)) = true := by
    rw [Generic.shiftOk_iff, hk]; simp; omega
  simp only [Val.ashr, hok, Bool.not_true, Bool.false_eq_true, ite_false]
  split
  · exact Refine.val_none _
  · refine add_refines_of_sum ?_
    rw [sshiftRight_width_sub_one y]
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
    rw [BitVec.slt_eq_decide, BitVec.toInt_allOnes, ite_eq_left hw]
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
  exact add_ashr_sign_one p exact nuw nsw

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
      rw [ite_eq_right, BitVec.add_assoc]
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
  | none => simp [Refines, Val.add, Refine.le]
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
  | none => simp [Refines, Val.add, Refine.le]
  | some p =>
  simp only [Val.xor, Val.map₂]
  exact add_refines_of_sum (add_intMin p)

/-- `(x ^ signmask) + c` refines `x + (c ^ signmask)`, with no flags. `IC.AddSub.foldAddWithConstant.L952`. -/
theorem add_xor_signMask_const_refines (x : Val w) (c : BitVec w) (nuw nsw : Bool) :
    Refines (Val.add (Val.xor x (some (BitVec.intMin w))) (some c) nuw nsw)
      (Val.add x (some (c ^^^ BitVec.intMin w))) := by
  cases x with
  | none => simp [Refines, Val.xor, Val.map₂, Val.add, Refine.le]
  | some p =>
  simp only [Val.xor, Val.map₂]
  have : Val.add (some p) (some (c ^^^ BitVec.intMin w)) = some ((p ^^^ BitVec.intMin w) + c) := by
    simp only [Val.add, Bool.false_and, Bool.or_false, Bool.false_eq_true, ite_false, Option.some.injEq]
    rw [← add_intMin p, ← add_intMin c]
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
  · have := add_ashr_sign_one (p <<< BitVec.ofNat w (w - 1)) exact nuw nsw
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
    rw [ite_eq_left h1, BitVec.add_left_neg]
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

/-- `zext (x ^ signmask) + sext signmask` is `sext x`, at any widths: flipping the sign bit and taking it back off
the wider value extends it. -/
theorem zext_xor_intMin_add (x : BitVec v) (w : Nat) :
    (x ^^^ BitVec.intMin v).setWidth w + (BitVec.intMin v).signExtend w = x.signExtend w := by
  rcases Nat.lt_or_ge w v with hwv | hvw
  · rw [BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_of_lt hwv), BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_of_lt hwv)]
    have hm : (BitVec.intMin v).setWidth w = 0#w := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_intMin, BitVec.getLsbD_zero]
      have : ¬ (i + 1 = v) := by omega
      simp [this]
    rw [hm, BitVec.add_zero, BitVec.setWidth_xor, hm, BitVec.xor_zero]
  · rcases Nat.eq_zero_or_pos v with rfl | hv
    · rw [BitVec.of_length_zero (x := x)]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_signExtend, BitVec.msb_intMin]
    · apply BitVec.eq_of_toNat_eq
      have hpow : 2 ^ v = 2 * 2 ^ (v - 1) := by rw [← Nat.pow_succ']; congr 1; omega
      have hvw' : 2 ^ v ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hvw
      have hx := x.isLt
      have hm : (BitVec.intMin v).toNat = 2 ^ (v - 1) := by
        rw [BitVec.toNat_intMin, Nat.mod_eq_of_lt (by omega)]
      have hmsb : (BitVec.intMin v).msb = true := by simp [BitVec.msb_intMin, hv]
      have h1 : ((x ^^^ BitVec.intMin v).setWidth w).toNat =
          if 2 ^ (v - 1) ≤ x.toNat then x.toNat + 2 ^ (v - 1) - 2 ^ v else x.toNat + 2 ^ (v - 1) := by
        have hxor : (x ^^^ BitVec.intMin v).toNat = (x.toNat + 2 ^ (v - 1)) % 2 ^ v := by
          rw [← add_intMin, BitVec.toNat_add, hm]
        rw [BitVec.toNat_setWidth, hxor, Nat.mod_eq_of_lt (a := (x.toNat + 2 ^ (v - 1)) % 2 ^ v)
          (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hvw')]
        split
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        · rw [Nat.mod_eq_of_lt (by omega)]
      have h2 : ((BitVec.intMin v).signExtend w).toNat = 2 ^ (v - 1) + (2 ^ w - 2 ^ v) := by
        rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, hm, hmsb, ite_eq_left rfl, Nat.mod_eq_of_lt (by omega)]
      have h3 : (x.signExtend w).toNat = x.toNat + if 2 ^ (v - 1) ≤ x.toNat then 2 ^ w - 2 ^ v else 0 := by
        rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide, Nat.mod_eq_of_lt (by omega)]
        by_cases h : 2 ^ (v - 1) ≤ x.toNat <;> simp [h]
      rw [BitVec.toNat_add, h1, h2, h3]
      split
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
      · rw [show x.toNat + 2 ^ (v - 1) + (2 ^ (v - 1) + (2 ^ w - 2 ^ v)) = x.toNat + 2 ^ w by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        simp

/-- `zext (x ^ signmask) + sext signmask` refines `sext x`. `IC.AddSub.foldAddWithConstant.L947`. -/
theorem add_zext_xor_intMin_refines (x : Val v) (nneg nuw nsw : Bool) :
    Refines (Val.add (Val.zext w (Val.xor x (some (BitVec.intMin v))) nneg)
        (some ((BitVec.intMin v).signExtend w)) nuw nsw) (Val.sext w x) := by
  cases x with
  | none => exact Refine.val_none _
  | some p =>
  simp only [Val.xor, Val.map₂, Val.zext, Val.sext, Val.map₁]
  split
  · exact Refine.val_none _
  · exact add_refines_of_sum (zext_xor_intMin_add p w)

/-- `(x ^ c2) + c` refines `ashr (shl x, s), s` for `s = w - 1 - k`, where `x` has no bit above `k`, `k + 1 < w`, and one
of `c` and `c2` is `2^k` and the other its negation. `IC.AddSub.foldAddWithConstant.L976`. -/
theorem add_xor_sext_refines {x : BitVec w} {k : Nat} (hk : k + 1 < w) (hx : ∀ i, k < i → x.getLsbD i = false)
    {c c2 : BitVec w} (hc : (c = BitVec.twoPow w k ∧ c2 = -c) ∨ (c2 = BitVec.twoPow w k ∧ c = -c2)) (nuw nsw : Bool) :
    Refines (Val.add (some (x ^^^ c2)) (some c) nuw nsw)
      (Val.ashr (Val.shl (some x) (some (BitVec.ofNat w (w - 1 - k)))) (some (BitVec.ofNat w (w - 1 - k)))) := by
  have hs : (BitVec.ofNat w (w - 1 - k)).toNat = w - 1 - k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := @Nat.lt_two_pow_self w; omega)
  have hok : Val.shiftOk (BitVec.ofNat w (w - 1 - k)) = true := by
    rw [Generic.shiftOk_iff, hs]; simp; omega
  simp only [Val.shl, Val.ashr, hok, Bool.not_true, Bool.false_eq_true, ite_false, Bool.false_and]
  refine add_refines_of_sum ?_
  rw [BitVec.shiftLeft_eq', BitVec.sshiftRight_eq', hs]
  exact xor_add_sext hx hc

end Peephole.Lemmas

/-! ### Counterexamples, for the lemma store

For each hypothesis `h` of a lemma above, `drop_h` says the lemma without it is false, and `sat` that its hypotheses
can all hold, by the names and in the form `tools/store/store.py` looks for. -/

namespace Peephole.Lemmas.Counter

/-- A source that's the value `x` only allows `x`. -/
theorem not_refines_of {w : Nat} {a b : IRLean.Val w} (x : BitVec w) (ha : a = some x) (hb : b ≠ some x) :
    ¬ IRLean.Refines a b := by
  subst ha; exact fun r => hb ((IRLean.Refine.val_some x b).1 r)

end Peephole.Lemmas.Counter

open IRLean Peephole.Lemmas.Counter

/-- In `i2`, `0 - 1` is `3`, and `0 ^ 1` is `1`. -/
theorem LemmaStore.Counter.Peephole.Lemmas.sub_eq_xor_of_and_eq.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w}, x - y = x ^^^ y :=
  fun h => absurd (@h 2 0#2 1#2) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.sub_eq_xor_of_and_eq.sat :
    ∃ (w : Nat) (x y : BitVec w), x &&& y = y :=
  ⟨0, 0#0, 0#0, by decide⟩

/-- In `i1`, `0` has no bit of `1`, and is less. -/
theorem LemmaStore.Counter.Peephole.Lemmas.le_of_and_eq.drop_h :
    ¬ ∀ {w : Nat} {x k : BitVec w}, k.toNat ≤ x.toNat :=
  fun h => absurd (@h 1 0#1 1#1) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.le_of_and_eq.sat :
    ∃ (w : Nat) (x k : BitVec w), x &&& k = k :=
  ⟨0, 0#0, 0#0, by decide⟩

/-- At width 0 every value is 0, its `not` too, and `-0 - 1` isn't 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.toInt_not_eq.drop_hw :
    ¬ ∀ {w : Nat} (p : BitVec w), (~~~p).toInt = -p.toInt - 1 :=
  fun h => absurd (@h 0 0#0) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.toInt_not_eq.sat : ∃ (w : Nat) (_ : BitVec w), 0 < w :=
  ⟨1, 0#1, Nat.one_pos⟩

/-- Past the width, `2^0` at width 0 is 0, with no bit 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.getLsbD_twoPow_of_lt.drop_hk :
    ¬ ∀ {w k : Nat} (i : Nat), (BitVec.twoPow w k).getLsbD i = decide (i = k) :=
  fun h => absurd (@h 0 0 0) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.getLsbD_twoPow_of_lt.sat : ∃ (w k : Nat) (_ : Nat), k < w :=
  ⟨1, 0, 0, Nat.one_pos⟩

/-- In `i2`, `1 + 1` is `2`, and `1 | 1` is `1`. -/
theorem LemmaStore.Counter.Peephole.Lemmas.add_eq_or.drop_h :
    ¬ ∀ {w : Nat} {x y : BitVec w}, x + y = x ||| y :=
  fun h => absurd (@h 2 1#2 1#2) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.add_eq_or.sat :
    ∃ (w : Nat) (x y : BitVec w), ∀ i, x.getLsbD i = true → y.getLsbD i = false :=
  ⟨0, 0#0, 0#0, fun _ h => by simp at h⟩

/-- In `i1`, shifting `1` by the width loses it, where bit `0` is still read as `1`. -/
theorem LemmaStore.Counter.Peephole.Lemmas.sshiftRight_shiftLeft_getLsbD.drop_hs :
    ¬ ∀ {w : Nat} (x : BitVec w) {s i : Nat}, i < w →
      ((x <<< s).sshiftRight s).getLsbD i = if i < w - s then x.getLsbD i else x.getLsbD (w - 1 - s) :=
  fun h => absurd (@h 1 1#1 1 0 (by decide)) (by decide)

/-- In `i1`, bit `1` is past the width, and read as bit `0`, which is `1`. -/
theorem LemmaStore.Counter.Peephole.Lemmas.sshiftRight_shiftLeft_getLsbD.drop_hi :
    ¬ ∀ {w : Nat} (x : BitVec w) {s i : Nat}, s < w →
      ((x <<< s).sshiftRight s).getLsbD i = if i < w - s then x.getLsbD i else x.getLsbD (w - 1 - s) :=
  fun h => absurd (@h 1 1#1 0 1 (by decide)) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.sshiftRight_shiftLeft_getLsbD.sat :
    ∃ (w : Nat) (_ : BitVec w) (s i : Nat), s < w ∧ i < w :=
  ⟨1, 0#1, 0, 0, by decide, by decide⟩

/-- In `i3`, `2` has bit 1 above `k = 0`: `(2 ^ -1) + 1` is `6`, and extending from bit 0 gives `0`. -/
theorem LemmaStore.Counter.Peephole.Lemmas.xor_add_sext.drop_hx :
    ¬ ∀ {w : Nat} {x : BitVec w} {k : Nat} {c c2 : BitVec w},
      (c = BitVec.twoPow w k ∧ c2 = -c) ∨ (c2 = BitVec.twoPow w k ∧ c = -c2) →
      (x ^^^ c2) + c = (x <<< (w - 1 - k)).sshiftRight (w - 1 - k) :=
  fun h => absurd (@h 3 2#3 0 1#3 7#3 (.inl ⟨by decide, by decide⟩)) (by decide)

/-- In `i3`, with both constants 0, `1` stays `1`, and extending from bit 0 gives `-1`. -/
theorem LemmaStore.Counter.Peephole.Lemmas.xor_add_sext.drop_hc :
    ¬ ∀ {w : Nat} {x : BitVec w} {k : Nat}, (∀ i, k < i → x.getLsbD i = false) → ∀ {c c2 : BitVec w},
      (x ^^^ c2) + c = (x <<< (w - 1 - k)).sshiftRight (w - 1 - k) :=
  fun h => absurd (@h 3 1#3 0 (fun i hi => by simp [BitVec.getLsbD_one]; omega) 0#3 0#3) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.xor_add_sext.sat :
    ∃ (w : Nat) (x : BitVec w) (k : Nat) (c c2 : BitVec w),
      (∀ i, k < i → x.getLsbD i = false) ∧ ((c = BitVec.twoPow w k ∧ c2 = -c) ∨ (c2 = BitVec.twoPow w k ∧ c = -c2)) :=
  ⟨1, 0#1, 0, BitVec.twoPow 1 0, -BitVec.twoPow 1 0, fun _ _ => by simp, .inl ⟨rfl, rfl⟩⟩

/-- In `i1`, `add nsw (xor 1, 1), 1` is `1`, and `sub nsw 0, 1` is poison: `0 - -1` doesn't fit. -/
theorem LemmaStore.Counter.Peephole.Lemmas.add_not_refines.drop_hw :
    ¬ ∀ {w : Nat} (x : Val w) (c : BitVec w) (nuw nsw : Bool),
      Refines (Val.add (Val.xor x (some (BitVec.allOnes w))) (some c) nuw nsw)
        (Val.sub (some (c - 1#w)) x false (nsw && !c.ssubOverflow 1#w)) :=
  fun h => not_refines_of 1#1 (by decide) (by decide) (@h 1 (some 1#1) 1#1 false true)

theorem LemmaStore.Counter.Peephole.Lemmas.add_not_refines.sat :
    ∃ (w : Nat) (_ : Val w) (_ : BitVec w) (_ nsw : Bool), w ≠ 1 ∨ nsw = false :=
  ⟨0, none, 0#0, false, false, .inl (by decide)⟩

/-- In `i1`, `add 1, 1` is `0`, and `or disjoint 1, 1` is poison. -/
theorem LemmaStore.Counter.Peephole.Lemmas.add_signMask_disjoint_refines.drop_h :
    ¬ ∀ {w : Nat} (x : Val w) (nuw nsw : Bool),
      Refines (Val.add x (some (BitVec.intMin w)) nuw nsw) (Val.or x (some (BitVec.intMin w)) true) :=
  fun h => not_refines_of 0#1 (by decide) (by decide) (@h 1 (some 1#1) false false)

theorem LemmaStore.Counter.Peephole.Lemmas.add_signMask_disjoint_refines.sat :
    ∃ (w : Nat) (_ : Val w) (nuw nsw : Bool), (nuw || nsw) = true :=
  ⟨0, none, true, false, rfl⟩

/-- In `i2`, `1` has a bit outside `0`: `(1 ^ 0) + 0` is `1`, and `(0 + 0) - 1` is `3`. -/
theorem LemmaStore.Counter.Peephole.Lemmas.add_xor_mask_refines.drop_h :
    ¬ ∀ {w : Nat} {x c2 : BitVec w} (c : BitVec w) (nuw nsw : Bool),
      Refines (Val.add (some (x ^^^ c2)) (some c) nuw nsw) (Val.sub (some (c2 + c)) (some x)) :=
  fun h => not_refines_of 1#2 (by decide) (by decide) (@h 2 1#2 0#2 0#2 false false)

theorem LemmaStore.Counter.Peephole.Lemmas.add_xor_mask_refines.sat :
    ∃ (w : Nat) (x c2 : BitVec w) (_ : BitVec w) (_ _ : Bool), x &&& ~~~c2 = 0#w :=
  ⟨0, 0#0, 0#0, 0#0, false, false, by decide⟩

/-- From `i1` to `i2`, `0 - 1` wraps to `1`: `zext 1 + 1` is `2`, and `zext 0` is `0`. -/
theorem LemmaStore.Counter.Peephole.Lemmas.add_zext_add_neg_refines.drop_h :
    ¬ ∀ {w v : Nat} {x n : BitVec v} (f1 f2 nneg nuw nsw : Bool),
      Refines (Val.add (Val.zext w (Val.add (some x) (some (-n)) f1 f2) nneg) (some (n.setWidth w)) nuw nsw)
        (Val.zext w (some x) false) :=
  fun h => not_refines_of 2#2 (by decide) (by decide) (@h 2 1 0#1 1#1 false false false false false)

theorem LemmaStore.Counter.Peephole.Lemmas.add_zext_add_neg_refines.sat :
    ∃ (_ v : Nat) (x n : BitVec v) (_ _ _ _ _ : Bool), n.toNat ≤ x.toNat :=
  ⟨0, 0, 0#0, 0#0, false, false, false, false, false, Nat.le_refl _⟩

/-- At width 0 the shift by `w - 1 - k`, 0, is out of range, so the shifts are poison, where the `add` is 0. -/
theorem LemmaStore.Counter.Peephole.Lemmas.add_xor_sext_refines.drop_hk :
    ¬ ∀ {w : Nat} {x : BitVec w} {k : Nat}, (∀ i, k < i → x.getLsbD i = false) → ∀ {c c2 : BitVec w},
      (c = BitVec.twoPow w k ∧ c2 = -c) ∨ (c2 = BitVec.twoPow w k ∧ c = -c2) → ∀ (nuw nsw : Bool),
      Refines (Val.add (some (x ^^^ c2)) (some c) nuw nsw)
        (Val.ashr (Val.shl (some x) (some (BitVec.ofNat w (w - 1 - k)))) (some (BitVec.ofNat w (w - 1 - k)))) :=
  fun h => not_refines_of 0#0 (by decide) (by decide)
    (@h 0 0#0 0 (fun _ _ => by simp) (BitVec.twoPow 0 0) (-BitVec.twoPow 0 0) (.inl ⟨rfl, rfl⟩) false false)

/-- In `i3`, `2` has bit 1 above `k = 0`: `(2 ^ -1) + 1` is `6`, and extending from bit 0 gives `0`. -/
theorem LemmaStore.Counter.Peephole.Lemmas.add_xor_sext_refines.drop_hx :
    ¬ ∀ {w : Nat} {x : BitVec w} {k : Nat}, k + 1 < w → ∀ {c c2 : BitVec w},
      (c = BitVec.twoPow w k ∧ c2 = -c) ∨ (c2 = BitVec.twoPow w k ∧ c = -c2) → ∀ (nuw nsw : Bool),
      Refines (Val.add (some (x ^^^ c2)) (some c) nuw nsw)
        (Val.ashr (Val.shl (some x) (some (BitVec.ofNat w (w - 1 - k)))) (some (BitVec.ofNat w (w - 1 - k)))) :=
  fun h => not_refines_of 6#3 (by decide) (by decide)
    (@h 3 2#3 0 (by decide) 1#3 7#3 (.inl ⟨by decide, by decide⟩) false false)

/-- In `i3`, with both constants 0, `1` stays `1`, and extending from bit 0 gives `-1`. -/
theorem LemmaStore.Counter.Peephole.Lemmas.add_xor_sext_refines.drop_hc :
    ¬ ∀ {w : Nat} {x : BitVec w} {k : Nat}, k + 1 < w → (∀ i, k < i → x.getLsbD i = false) →
      ∀ {c c2 : BitVec w} (nuw nsw : Bool),
      Refines (Val.add (some (x ^^^ c2)) (some c) nuw nsw)
        (Val.ashr (Val.shl (some x) (some (BitVec.ofNat w (w - 1 - k)))) (some (BitVec.ofNat w (w - 1 - k)))) :=
  fun h => not_refines_of 1#3 (by decide) (by decide)
    (@h 3 1#3 0 (by decide) (fun i hi => by simp [BitVec.getLsbD_one]; omega) 0#3 0#3 false false)

theorem LemmaStore.Counter.Peephole.Lemmas.add_xor_sext_refines.sat :
    ∃ (w : Nat) (x : BitVec w) (k : Nat) (c c2 : BitVec w) (_ _ : Bool),
      k + 1 < w ∧ (∀ i, k < i → x.getLsbD i = false) ∧
        ((c = BitVec.twoPow w k ∧ c2 = -c) ∨ (c2 = BitVec.twoPow w k ∧ c = -c2)) :=
  ⟨2, 0#2, 0, BitVec.twoPow 2 0, -BitVec.twoPow 2 0, false, false, by decide, fun _ _ => by simp, .inl ⟨rfl, rfl⟩⟩
