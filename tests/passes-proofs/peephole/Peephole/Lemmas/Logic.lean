import IRLean.Int
import IRLean.Refine
import IRLean.Generic.BitVec

/-! # Facts about `and`, `or` and `xor`, at every width, that InstSimplify's rewrites of them rest on

Each is about values, not about LLVM's code: a candidate for the lemma store, which any proof about a bitwise operation
can use. The rewrite each one was cut from is named in its docstring. `not x` is `xor x, -1`, as LLVM writes it; a
matcher's other order, `xor -1, x`, is the same value by `Logic.xor_comm`. Each lemma takes the flags of every
instruction in it, so `or disjoint` and `add nuw nsw` are covered: a flag only makes the source poison more often.

The helpers in `Peephole.Lemmas.Logic` (commutativity, what an operation does on values and poison, and the tactics
that prove an identity bit by bit) aren't offered to the store. After the lemmas, `LemmaStore.Counter` holds, for each
hypothesis of a lemma, an input showing the lemma is false without it, and for each lemma with hypotheses, an input
where they all hold. -/

namespace Peephole.Lemmas

open IRLean

variable {w : Nat}

namespace Logic

theorem and_some (x y : BitVec w) : Val.and (some x) (some y) = some (x &&& y) := rfl
theorem and_none_left (b : Val w) : Val.and none b = none := rfl
theorem and_none_right (a : Val w) : Val.and a none = none := by cases a <;> rfl
theorem xor_some (x y : BitVec w) : Val.xor (some x) (some y) = some (x ^^^ y) := rfl
theorem xor_none_left (b : Val w) : Val.xor none b = none := rfl
theorem xor_none_right (a : Val w) : Val.xor a none = none := by cases a <;> rfl
theorem or_some (x y : BitVec w) (d : Bool) :
    Val.or (some x) (some y) d = if d && x &&& y != 0#w then none else some (x ||| y) := rfl
theorem or_none_left (b : Val w) (d : Bool) : Val.or none b d = none := rfl
theorem or_none_right (a : Val w) (d : Bool) : Val.or a none d = none := by cases a <;> rfl

theorem and_comm (a b : Val w) : Val.and a b = Val.and b a := by
  cases a <;> cases b <;> simp [Val.and, Val.map₂, BitVec.and_comm]

theorem xor_comm (a b : Val w) : Val.xor a b = Val.xor b a := by
  cases a <;> cases b <;> simp [Val.xor, Val.map₂, BitVec.xor_comm]

theorem or_comm (a b : Val w) (d : Bool) : Val.or a b d = Val.or b a d := by
  cases a <;> cases b <;> simp [Val.or, BitVec.or_comm, BitVec.and_comm]

theorem refines_iff (a b : Val w) : Refines a b ↔ a = none ∨ b = a := Refine.val_iff a b

theorem refines_none (b : Val w) : Refines (none : Val w) b := Refine.val_none b

theorem refines_some {x y : BitVec w} (h : y = x) : Refines (some x : Val w) (some y) := by
  rw [refines_iff, h]; exact .inr rfl

/-- Proves an equation of bit vectors bit by bit. -/
macro "bitwise" : tactic => `(tactic| (apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi] <;> grind))

/-- Unfolds `and`, `or` and `xor` on values and poison. -/
macro "vsimp" : tactic => `(tactic| simp only [Logic.and_some, Logic.and_none_left, Logic.and_none_right,
  Logic.xor_some, Logic.xor_none_left, Logic.xor_none_right, Logic.or_some, Logic.or_none_left,
  Logic.or_none_right] at *)

/-- Closes `Refines src tgt` of `and`, `or` and `xor` once every operand is a value or poison, splitting on each
`disjoint` that may make the source poison, and proving what's left bit by bit. -/
macro "vfinish" : tactic => `(tactic| (
  rw [Logic.refines_iff]
  vsimp
  repeat' (split <;> (try vsimp))
  all_goals first
    | exact .inl rfl
    | (refine .inr ?_; congr 1; bitwise)
    | (refine .inr ?_; bitwise)
    | simp_all))

/-- `i1` has two values. -/
theorem bv1_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := BitVec.eq_zero_or_eq_one x

/-- A source that's the value `x` only allows `x`. -/
theorem not_refines {a b : Val w} (x : BitVec w) (ha : a = some x) (hb : b ≠ some x) : ¬ Refines a b := by
  subst ha; exact fun r => hb ((Refine.val_some x b).1 r)

/-! ### Facts about bit vectors the rewrites use -/

/-- A power of two in `w` bits is `twoPow w k` for a `k` below `w`. -/
theorem eq_twoPow_of_isPowerOfTwo {x : BitVec w} (h : x.toNat.isPowerOfTwo) :
    ∃ k, k < w ∧ x = BitVec.twoPow w k := by
  obtain ⟨k, hk⟩ := h
  have hlt : 2 ^ k < 2 ^ w := hk ▸ x.isLt
  have hkw : k < w := (Nat.pow_lt_pow_iff_right (by decide)).1 hlt
  exact ⟨k, hkw, BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_twoPow_of_lt hkw, hk])⟩

theorem twoPow_shiftLeft (k n : Nat) : BitVec.twoPow w k <<< n = BitVec.twoPow w (k + n) := by
  rw [BitVec.twoPow_eq, BitVec.twoPow_eq, BitVec.shiftLeft_add]

theorem twoPow_eq_zero {k : Nat} (h : w ≤ k) : BitVec.twoPow w k = 0#w :=
  BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_twoPow_of_le h])

/-- `2 ^ k - 1` in `w` bits, for `k` below `w`, has no bit at or above `k`. -/
theorem getLsbD_twoPow_add_allOnes {k i : Nat} (hk : k < w) (hi : k ≤ i) :
    (BitVec.twoPow w k + BitVec.allOnes w).getLsbD i = false := by
  rw [← BitVec.testBit_toNat, BitVec.toNat_add, BitVec.toNat_twoPow_of_lt hk, BitVec.toNat_allOnes]
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) hk
  rw [show 2 ^ k + (2 ^ w - 1) = (2 ^ k - 1) + 2 ^ w by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide) hi))

/-- A mask of low bits, `c &&& (c + 1) = 0`, is closed downwards: below a set bit, every bit is set. -/
theorem getLsbD_of_lowMask {c : BitVec w} (hc : c &&& (c + 1#w) = 0#w) {i j : Nat} (hi : c.getLsbD i = true)
    (hj : j ≤ i) : c.getLsbD j = true := by
  have hiw : i < w := BitVec.lt_of_getLsbD hi
  cases hcj : c.getLsbD j
  case true => rfl
  exfalso
  have hji : j < i := by
    rcases Nat.lt_or_eq_of_le hj with h | rfl
    · exact h
    · simp [hi] at hcj
  -- Bits below `i` aren't all set, so adding 1 doesn't carry into bit `i`.
  have hcarry : BitVec.carry i c 1#w false = false := by
    simp only [BitVec.carry, Bool.toNat_false, Nat.add_zero, decide_eq_false_iff_not, Nat.not_le,
      BitVec.toNat_ofNat]
    have hmod : (1 % 2 ^ w) % 2 ^ i = 1 := by
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega)), Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    rw [hmod]
    have hlt : c.toNat % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    suffices c.toNat % 2 ^ i ≠ 2 ^ i - 1 by omega
    intro heq
    have := congrArg (Nat.testBit · j) heq
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, hji, decide_true, Bool.true_and,
      BitVec.testBit_toNat] at this
    simp [this] at hcj
  have h1 : (c + 1#w).getLsbD i = true := by
    rw [BitVec.getLsbD_add hiw, hcarry, hi]
    simp [BitVec.getLsbD_one]; omega
  have := congrArg (BitVec.getLsbD · i) hc
  simp [BitVec.getLsbD_and, hi, h1] at this

/-- Adding a value with no bit in a low mask leaves the bits in the mask alone. -/
theorem add_and_lowMask {c u v : BitVec w} (hc : c &&& (c + 1#w) = 0#w) (hv : v &&& c = 0#w) :
    (u + v) &&& c = u &&& c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  cases hci : c.getLsbD i
  · simp
  · have hlow : ∀ j, j ≤ i → v.getLsbD j = false := fun j hj => by
      have := congrArg (BitVec.getLsbD · j) hv
      simpa [BitVec.getLsbD_and, getLsbD_of_lowMask hc hci hj] using this
    have hvmod : v.toNat % 2 ^ i = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit, BitVec.testBit_toNat]
      by_cases hj : j < i
      · simp [hj, hlow j (by omega)]
      · simp [hj]
    have hcarry : BitVec.carry i u v false = false := by
      simp only [BitVec.carry, hvmod, Bool.toNat_false, Nat.add_zero, decide_eq_false_iff_not, Nat.not_le]
      exact Nat.mod_lt _ (Nat.two_pow_pos i)
    rw [BitVec.getLsbD_add hi, hcarry, hlow i (Nat.le_refl i)]
    simp

/-- Below a low mask, in the order of the naturals, means inside it, bit by bit. -/
theorem and_lowMask_of_le {c u : BitVec w} (hc : c &&& (c + 1#w) = 0#w) (hu : u.toNat ≤ c.toNat) :
    u &&& c = u := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  cases hui : u.getLsbD i
  · simp
  · simp only [Bool.true_and]
    cases hci : c.getLsbD i
    case true => rfl
    exfalso
    -- No bit of `c` is set at or above `i`, so `c < 2 ^ i ≤ u`.
    have hhigh : ∀ j, j ≥ i → c.toNat.testBit j = false := fun j hj => by
      rw [BitVec.testBit_toNat]
      cases hcj : c.getLsbD j
      · rfl
      · rw [getLsbD_of_lowMask hc hcj hj] at hci; cases hci
    have h1 := Nat.lt_pow_two_of_testBit c.toNat hhigh
    have h2 := Nat.ge_two_pow_of_testBit (by rw [BitVec.testBit_toNat]; exact hui)
    omega

/-- Subtracting a value whose bits are all in `c` is `xor`: no bit borrows. -/
theorem sub_of_and_eq {c u : BitVec w} (hu : u &&& c = u) : c - u = c ^^^ u := by
  rw [BitVec.sub_eq_iff_eq_add]
  have hd : (c ^^^ u) &&& u = 0#w := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h := congrArg (BitVec.getLsbD · i) hu
    simp only [BitVec.getLsbD_and] at h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_zero]
    cases hc' : c.getLsbD i <;> cases hu' : u.getLsbD i <;> simp_all
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hd]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := congrArg (BitVec.getLsbD · i) hu
  simp only [BitVec.getLsbD_and] at h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor]
  cases hc' : c.getLsbD i <;> cases hu' : u.getLsbD i <;> simp_all

/-! ### What an operation on two values gives: poison, or its result -/

theorem shl_cases (x y : BitVec w) (nuw nsw : Bool) :
    Val.shl (some x) (some y) nuw nsw = none ∨
      (y.toNat < w ∧ Val.shl (some x) (some y) nuw nsw = some (x <<< y.toNat)) := by
  simp only [Val.shl]
  split
  · exact .inl rfl
  · next h =>
    split
    · exact .inl rfl
    · split
      · exact .inl rfl
      · right
        refine ⟨?_, by rw [BitVec.shiftLeft_eq']⟩
        simpa [IRLean.Generic.shiftOk_iff] using h

theorem lshr_cases (x y : BitVec w) (exact : Bool) :
    Val.lshr (some x) (some y) exact = none ∨
      (y.toNat < w ∧ Val.lshr (some x) (some y) exact = some (x >>> y.toNat)) := by
  simp only [Val.lshr]
  split
  · exact .inl rfl
  · next h =>
    split
    · exact .inl rfl
    · right
      refine ⟨?_, by rw [BitVec.ushiftRight_eq']⟩
      simpa [IRLean.Generic.shiftOk_iff] using h

theorem add_cases (x y : BitVec w) (nuw nsw : Bool) :
    Val.add (some x) (some y) nuw nsw = none ∨ Val.add (some x) (some y) nuw nsw = some (x + y) := by
  simp only [Val.add]
  split
  · exact .inl rfl
  · exact .inr rfl

theorem sub_cases (x y : BitVec w) (nuw nsw : Bool) :
    Val.sub (some x) (some y) nuw nsw = none ∨
      ((nuw = true → y.toNat ≤ x.toNat) ∧ Val.sub (some x) (some y) nuw nsw = some (x - y)) := by
  simp only [Val.sub]
  split
  · exact .inl rfl
  · next h =>
    right
    refine ⟨fun hn => ?_, rfl⟩
    simp only [hn, Bool.true_and, Bool.or_eq_true, BitVec.usubOverflow, decide_eq_true_eq, not_or] at h
    omega

theorem or_cases (x y : BitVec w) (d : Bool) :
    Val.or (some x) (some y) d = none ∨ Val.or (some x) (some y) d = some (x ||| y) := by
  rw [or_some]
  split
  · exact .inl rfl
  · exact .inr rfl

/-- `2 * w ≤ 2 ^ w`: a shift amount below the width, doubled, still fits. -/
theorem two_mul_le_two_pow (w : Nat) : 2 * w ≤ 2 ^ w := by
  induction w with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

/-- If `x = c - y` in `w` bits and both are shift amounts in range, `x + y` is `c` as a natural number. -/
theorem toNat_sub_add_of_lt {c y : BitVec w} (hx : (c - y).toNat < w) (hy : y.toNat < w) :
    (c - y).toNat + y.toNat = c.toNat := by
  have hp := two_mul_le_two_pow w
  rw [BitVec.toNat_sub] at hx ⊢
  by_cases hcy : y.toNat ≤ c.toNat
  · rw [show 2 ^ w - y.toNat + c.toNat = (c.toNat - y.toNat) + 2 ^ w by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hx
    omega

/-- `-1 << x` and `-1 >> y` cover every bit when `x + y ≤ w`. -/
theorem allOnes_shiftLeft_or_ushiftRight {x y : Nat} (h : x + y ≤ w) :
    (BitVec.allOnes w <<< x) ||| (BitVec.allOnes w >>> y) = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes, hi]
  by_cases hx : i < x
  · simp [hx]; omega
  · simp [hx]; omega

/-- `~c - u` is `~(u + c)`. -/
theorem not_sub_eq_not_add (c u : BitVec w) : ~~~c - u = ~~~(u + c) := by
  have h := BitVec.not_sub_eq_not_add (x := ~~~c) (y := u)
  rw [BitVec.not_not, BitVec.add_comm] at h
  rw [← h, BitVec.not_not]

/-- Rotating left and shifting left by the same amount in range: the shift's bits are the rotation's. -/
theorem fshlRaw_or_shiftLeft {x z s : BitVec w} (hs : s.toNat < w) :
    Val.fshlRaw x z s ||| x <<< s.toNat = Val.fshlRaw x z s := by
  simp only [Val.fshlRaw, Nat.mod_eq_of_lt hs]
  split
  · next h => rw [h]; simp
  · bitwise

theorem fshrRaw_or_ushiftRight {z x s : BitVec w} (hs : s.toNat < w) :
    Val.fshrRaw z x s ||| x >>> s.toNat = Val.fshrRaw z x s := by
  simp only [Val.fshrRaw, Nat.mod_eq_of_lt hs]
  split
  · next h => rw [h]; simp
  · bitwise

end Logic

open Logic

/-! ### `and` -/

/-- `and (not a), a` refines 0. `IS.simplifyAndCommutative.L2024`. -/
theorem and_not_self_refines (a : Val w) :
    Refines (Val.and (Val.xor a (some (BitVec.allOnes w))) a) (some 0#w) := by
  cases a <;> vfinish

/-- `and (or x, (not y)), (or x, y)` refines `x`. `IS.simplifyAndCommutative.L2034`. -/
theorem and_or_not_or_refines (x y : Val w) (d d' : Bool) :
    Refines (Val.and (Val.or x (Val.xor y (some (BitVec.allOnes w))) d) (Val.or x y d')) x := by
  cases x <;> cases y <;> vfinish

/-- `and (sub 0, a), a` refines `a` where `a` is a power of two or 0. `IS.simplifyAndCommutative.L2045`. -/
theorem and_neg_self_refines (a : Val w) (nuw nsw : Bool)
    (h : ∀ x, a = some x → x.toNat.isPowerOfTwo ∨ x = 0#w) :
    Refines (Val.and (Val.sub (some 0#w) a nuw nsw) a) a := by
  cases a with
  | none => exact refines_none _
  | some x =>
    rcases sub_cases 0#w x nuw nsw with hs | ⟨-, hs⟩ <;> rw [hs]
    · exact refines_none _
    · rw [and_some]
      refine refines_some ?_
      rcases h x rfl with hp | rfl
      · obtain ⟨k, hk, rfl⟩ := eq_twoPow_of_isPowerOfTwo hp
        rw [BitVec.and_twoPow]
        simp [BitVec.getLsbD_neg, BitVec.getLsbD_twoPow, hk]
      · simp

/-- `and (add a, -1), a` refines 0 where `a` is a power of two or 0. `IS.simplifyAndCommutative.L2051`. -/
theorem and_add_allOnes_self_refines (a : Val w) (nuw nsw : Bool)
    (h : ∀ x, a = some x → x.toNat.isPowerOfTwo ∨ x = 0#w) :
    Refines (Val.and (Val.add a (some (BitVec.allOnes w)) nuw nsw) a) (some 0#w) := by
  cases a with
  | none => exact refines_none _
  | some x =>
    rcases add_cases x (BitVec.allOnes w) nuw nsw with hs | hs <;> rw [hs]
    · exact refines_none _
    · rw [and_some]
      refine refines_some ?_
      rcases h x rfl with hp | rfl
      · obtain ⟨k, hk, rfl⟩ := eq_twoPow_of_isPowerOfTwo hp
        rw [BitVec.and_twoPow, getLsbD_twoPow_add_allOnes hk (Nat.le_refl k)]
        simp
      · simp

/-- `and (shl a, n), (add (shl a, m), -1)` refines 0 where `a` is a power of two or 0 and `m ≤ n`.
`IS.simplifyAndCommutative.L2060`. -/
theorem and_shl_shl_add_allOnes_refines (a : Val w) (n m : BitVec w) (f1 f2 f3 f4 f5 f6 : Bool)
    (h : ∀ x, a = some x → x.toNat.isPowerOfTwo ∨ x = 0#w) (hmn : m.toNat ≤ n.toNat) :
    Refines (Val.and (Val.shl a (some n) f1 f2) (Val.add (Val.shl a (some m) f3 f4) (some (BitVec.allOnes w)) f5 f6))
      (some 0#w) := by
  cases a with
  | none => exact refines_none _
  | some x =>
    rcases shl_cases x n f1 f2 with h1 | ⟨hn, h1⟩ <;> rw [h1]
    · exact refines_none _
    rcases shl_cases x m f3 f4 with h2 | ⟨hm, h2⟩ <;> rw [h2]
    · rw [show Val.add none (some (BitVec.allOnes w)) f5 f6 = none from rfl, and_none_right]
      exact refines_none _
    rcases add_cases (x <<< m.toNat) (BitVec.allOnes w) f5 f6 with h3 | h3 <;> rw [h3]
    · rw [and_none_right]; exact refines_none _
    rw [and_some]
    refine refines_some ?_
    rcases h x rfl with hp | rfl
    · obtain ⟨k, hk, rfl⟩ := eq_twoPow_of_isPowerOfTwo hp
      rw [twoPow_shiftLeft, twoPow_shiftLeft, BitVec.and_comm, BitVec.and_twoPow]
      by_cases hkm : k + m.toNat < w
      · rw [getLsbD_twoPow_add_allOnes hkm (by omega)]; simp
      · rw [twoPow_eq_zero (by omega : w ≤ k + n.toNat)]; simp
    · simp

/-- `and (shl a, s), m` is `shl a, s` where `m` has every bit `shl` can set. `IS.simplifyAndInst.L2113`. -/
theorem and_shl_mask (a : Val w) (s m : BitVec w) (nuw nsw : Bool) (h : ~~~m >>> s.toNat = 0#w) :
    Val.and (Val.shl a (some s) nuw nsw) (some m) = Val.shl a (some s) nuw nsw := by
  cases a with
  | none => rfl
  | some x =>
    rcases shl_cases x s nuw nsw with h1 | ⟨hs, h1⟩ <;> rw [h1]
    · rfl
    rw [and_some]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
    by_cases his : i < s.toNat
    · simp [his]
    · have := congrArg (BitVec.getLsbD · (i - s.toNat)) h
      simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not, BitVec.getLsbD_zero,
        show s.toNat + (i - s.toNat) = i by omega, hi, decide_true, Bool.true_and] at this
      simp [his, (by simpa using this : m.getLsbD i = true)]

/-- `and (lshr a, s), m` is `lshr a, s` where `m` has every bit `lshr` can set. `IS.simplifyAndInst.L2119`. -/
theorem and_lshr_mask (a : Val w) (s m : BitVec w) (exact : Bool) (h : ~~~m <<< s.toNat = 0#w) :
    Val.and (Val.lshr a (some s) exact) (some m) = Val.lshr a (some s) exact := by
  cases a with
  | none => rfl
  | some x =>
    rcases lshr_cases x s exact with h1 | ⟨hs, h1⟩ <;> rw [h1]
    · rfl
    rw [and_some]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
    by_cases his : s.toNat + i < w
    · have := congrArg (BitVec.getLsbD · (i + s.toNat)) h
      simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_not, BitVec.getLsbD_zero,
        show i + s.toNat - s.toNat = i by omega, hi, decide_true, Bool.true_and,
        show i + s.toNat < w by omega, show ¬ (i + s.toNat < s.toNat) by omega, decide_false,
        Bool.not_false] at this
      simp [(by simpa using this : m.getLsbD i = true)]
    · simp [BitVec.getLsbD_of_ge x (s.toNat + i) (by omega)]

/-- `and (add a, -1), c` refines 0 where `a` and `c` are powers of two and `a < 2 * c`.
`IS.simplifyAndInst.L2132`. -/
theorem and_add_allOnes_twoPow_refines (a : Val w) (c : BitVec w) (nuw nsw : Bool)
    (ha : ∀ x, a = some x → x.toNat.isPowerOfTwo ∧ x.toNat < 2 * c.toNat) (hc : c.toNat.isPowerOfTwo) :
    Refines (Val.and (Val.add a (some (BitVec.allOnes w)) nuw nsw) (some c)) (some 0#w) := by
  cases a with
  | none => exact refines_none _
  | some x =>
    rcases add_cases x (BitVec.allOnes w) nuw nsw with hs | hs <;> rw [hs]
    · exact refines_none _
    rw [and_some]
    refine refines_some ?_
    obtain ⟨hp, hlt⟩ := ha x rfl
    obtain ⟨k, hk, rfl⟩ := eq_twoPow_of_isPowerOfTwo hp
    obtain ⟨j, hj, rfl⟩ := eq_twoPow_of_isPowerOfTwo hc
    rw [BitVec.toNat_twoPow_of_lt hk, BitVec.toNat_twoPow_of_lt hj, ← Nat.pow_succ'] at hlt
    have hkj : k ≤ j := Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right (by decide)).1 hlt)
    rw [BitVec.and_twoPow, getLsbD_twoPow_add_allOnes hk hkj]
    simp

/-- `and (or (shl x, s), y), m` refines `y` where `m` keeps every bit of `y` and none of `x << s`.
`IS.simplifyAndInst.L2203`. -/
theorem and_or_shl_mask_refines_right (x y : Val w) (s m : BitVec w) (nuw nsw d : Bool)
    (hy : ∀ v, y = some v → v &&& m = v) (hx : ∀ u, x = some u → (u <<< s.toNat) &&& m = 0#w) :
    Refines (Val.and (Val.or (Val.shl x (some s) nuw nsw) y d) (some m)) y := by
  cases x with
  | none => exact refines_none _
  | some u =>
    rcases shl_cases u s nuw nsw with h1 | ⟨-, h1⟩ <;> rw [h1]
    · exact refines_none _
    cases y with
    | none => rw [or_none_right]; exact refines_none _
    | some v =>
      rcases or_cases (u <<< s.toNat) v d with h2 | h2 <;> rw [h2]
      · exact refines_none _
      rw [and_some]
      refine refines_some ?_
      rw [BitVec.and_or_distrib_right, hx u rfl, hy v rfl]
      simp

/-- `and (or (shl x, s), y), m` refines `shl x, s` where `m` keeps every bit of `x << s` and none of `y`.
`IS.simplifyAndInst.L2205`. -/
theorem and_or_shl_mask_refines_left (x y : Val w) (s m : BitVec w) (nuw nsw d : Bool)
    (hy : ∀ v, y = some v → v &&& m = 0#w) (hx : ∀ u, x = some u → (u <<< s.toNat) &&& m = u <<< s.toNat) :
    Refines (Val.and (Val.or (Val.shl x (some s) nuw nsw) y d) (some m)) (Val.shl x (some s) nuw nsw) := by
  cases x with
  | none => exact refines_none _
  | some u =>
    rcases shl_cases u s nuw nsw with h1 | ⟨-, h1⟩ <;> rw [h1]
    · exact refines_none _
    cases y with
    | none => rw [or_none_right]; exact refines_none _
    | some v =>
      rcases or_cases (u <<< s.toNat) v d with h2 | h2 <;> rw [h2]
      · exact refines_none _
      rw [and_some]
      refine refines_some ?_
      rw [BitVec.and_or_distrib_right, hx u rfl, hy v rfl]
      simp

/-- `and (xor (or x, y), x), (xor (or x, y), y)` refines 0. `IS.simplifyAndInst.L2216`. -/
theorem and_xor_or_xor_or_refines (x y : Val w) (d : Bool) :
    Refines (Val.and (Val.xor (Val.or x y d) x) (Val.xor (Val.or x y d) y)) (some 0#w) := by
  cases x <;> cases y <;> vfinish

/-- `and (xor a, c), (xor a, ~c)` refines 0. `IS.simplifyAndInst.L2223`. -/
theorem and_xor_xor_not_refines (a : Val w) (c : BitVec w) :
    Refines (Val.and (Val.xor a (some c)) (Val.xor a (some (~~~c)))) (some 0#w) := by
  cases a <;> vfinish

/-! ### `(x + k) op (~k - x)`: the second is `not` of the first -/

theorem Logic.add_sub_not_cases (x : Val w) (k : BitVec w) (f1 f2 f3 f4 : Bool) :
    Val.add x (some k) f1 f2 = none ∨ Val.sub (some (~~~k)) x f3 f4 = none ∨
      ∃ t, Val.add x (some k) f1 f2 = some t ∧ Val.sub (some (~~~k)) x f3 f4 = some (~~~t) := by
  cases x with
  | none => exact .inl rfl
  | some u =>
    rcases add_cases u k f1 f2 with h1 | h1
    · exact .inl h1
    rcases sub_cases (~~~k) u f3 f4 with h2 | ⟨-, h2⟩
    · exact .inr (.inl h2)
    exact .inr (.inr ⟨u + k, h1, by rw [h2, not_sub_eq_not_add]⟩)

/-- `and (add x, k), (sub ~k, x)` refines 0. `IS.simplifyLogicOfAddSub.L2011`. -/
theorem and_add_sub_not_refines (x : Val w) (k : BitVec w) (f1 f2 f3 f4 : Bool) :
    Refines (Val.and (Val.add x (some k) f1 f2) (Val.sub (some (~~~k)) x f3 f4)) (some 0#w) := by
  rcases Logic.add_sub_not_cases x k f1 f2 f3 f4 with h | h | ⟨t, h1, h2⟩
  · rw [h, and_none_left]; exact refines_none _
  · rw [h, and_none_right]; exact refines_none _
  · rw [h1, h2]; vfinish

/-- `or (add x, k), (sub ~k, x)` refines -1. `IS.simplifyLogicOfAddSub.L2011`. -/
theorem or_add_sub_not_refines (x : Val w) (k : BitVec w) (f1 f2 f3 f4 d : Bool) :
    Refines (Val.or (Val.add x (some k) f1 f2) (Val.sub (some (~~~k)) x f3 f4) d) (some (BitVec.allOnes w)) := by
  rcases Logic.add_sub_not_cases x k f1 f2 f3 f4 with h | h | ⟨t, h1, h2⟩
  · rw [h, or_none_left]; exact refines_none _
  · rw [h, or_none_right]; exact refines_none _
  · rw [h1, h2]; vfinish

/-- `xor (add x, k), (sub ~k, x)` refines -1. `IS.simplifyLogicOfAddSub.L2011`. -/
theorem xor_add_sub_not_refines (x : Val w) (k : BitVec w) (f1 f2 f3 f4 : Bool) :
    Refines (Val.xor (Val.add x (some k) f1 f2) (Val.sub (some (~~~k)) x f3 f4)) (some (BitVec.allOnes w)) := by
  rcases Logic.add_sub_not_cases x k f1 f2 f3 f4 with h | h | ⟨t, h1, h2⟩
  · rw [h, xor_none_left]; exact refines_none _
  · rw [h, xor_none_right]; exact refines_none _
  · rw [h1, h2]; vfinish

/-! ### `and` and `or` of `i1`: what an implied condition, or a `select`, gives -/

/-- `and a, b` refines `a` where `b` is true, or poison, when `a` is true. `IS.simplifyAndInst.L2229`. -/
theorem and_refines_left_of_implies (a b : Val 1) (h : a = some 1#1 → b = none ∨ b = some 1#1) :
    Refines (Val.and a b) a := by
  rcases a with _ | x
  · exact refines_none _
  · rcases bv1_cases x with rfl | rfl
    · cases b <;> vfinish
    · rcases h rfl with rfl | rfl <;> vfinish

/-- `and a, b` refines false where `b` is false, or poison, when `a` is true. `IS.simplifyAndInst.L2232`. -/
theorem and_refines_false_of_implies (a b : Val 1) (h : a = some 1#1 → b = none ∨ b = some 0#1) :
    Refines (Val.and a b) (some 0#1) := by
  rcases a with _ | x
  · exact refines_none _
  · rcases bv1_cases x with rfl | rfl
    · cases b <;> vfinish
    · rcases h rfl with rfl | rfl <;> vfinish

/-- `and a, b` refines `b` where `b` is false, or poison, when `a` is false.
`IS.simplifyAndOrWithICmpEq.Simplify.L1975`. -/
theorem and_refines_right_of_false (a b : Val 1) (h : a = some 0#1 → b = none ∨ b = some 0#1) :
    Refines (Val.and a b) b := by
  rcases a with _ | x
  · exact refines_none _
  · rcases bv1_cases x with rfl | rfl
    · rcases h rfl with rfl | rfl <;> vfinish
    · cases b <;> vfinish

/-- `or a, b` refines `a` where `b` is false, or poison, when `a` is false. `IS.simplifyOrInst.L2502`. -/
theorem or_refines_left_of_implies (a b : Val 1) (d : Bool) (h : a = some 0#1 → b = none ∨ b = some 0#1) :
    Refines (Val.or a b d) a := by
  rcases a with _ | x
  · exact refines_none _
  · rcases bv1_cases x with rfl | rfl
    · rcases h rfl with rfl | rfl <;> vfinish
    · cases b <;> vfinish

/-- `or a, b` refines true where `b` is true, or poison, when `a` is false. `IS.simplifyOrInst.L2505`. -/
theorem or_refines_true_of_implies (a b : Val 1) (d : Bool) (h : a = some 0#1 → b = none ∨ b = some 1#1) :
    Refines (Val.or a b d) (some 1#1) := by
  rcases a with _ | x
  · exact refines_none _
  · rcases bv1_cases x with rfl | rfl
    · rcases h rfl with rfl | rfl <;> vfinish
    · cases b <;> vfinish

/-- `or a, b` refines `b` where `b` is true, or poison, when `a` is true.
`IS.simplifyAndOrWithICmpEq.Simplify.L1975`. -/
theorem or_refines_right_of_true (a b : Val 1) (d : Bool) (h : a = some 1#1 → b = none ∨ b = some 1#1) :
    Refines (Val.or a b d) b := by
  rcases a with _ | x
  · exact refines_none _
  · rcases bv1_cases x with rfl | rfl
    · cases b <;> vfinish
    · rcases h rfl with rfl | rfl <;> vfinish

/-- `and a, (select a, t, false)` refines the `select`. `IS.simplifyAndInst.L2157`. -/
theorem and_select_refines (a t : Val 1) :
    Refines (Val.and a (select a t (some 0#1))) (select a t (some 0#1)) := by
  rw [refines_iff]
  rcases a with _ | x <;> rcases t with _ | y <;> (try rcases bv1_cases x with rfl | rfl) <;>
    (try rcases bv1_cases y with rfl | rfl) <;> decide

/-- `or a, (select a, true, t)` refines the `select`. `IS.simplifyOrInst.L2448`. -/
theorem or_select_refines (a t : Val 1) (d : Bool) :
    Refines (Val.or a (select a (some 1#1) t) d) (select a (some 1#1) t) := by
  rw [refines_iff]
  rcases a with _ | x <;> rcases t with _ | y <;> (try rcases bv1_cases x with rfl | rfl) <;>
    (try rcases bv1_cases y with rfl | rfl) <;> cases d <;> decide

/-! ### `or` -/

/-- `or a, (not a)` refines -1. `IS.simplifyOrLogic.L2261`. -/
theorem or_not_self_refines (a : Val w) (d : Bool) :
    Refines (Val.or a (Val.xor a (some (BitVec.allOnes w))) d) (some (BitVec.allOnes w)) := by
  cases a <;> vfinish

/-- `or a, (not (and a, b))` refines -1. `IS.simplifyOrLogic.L2265`. -/
theorem or_not_and_refines (a b : Val w) (d : Bool) :
    Refines (Val.or a (Val.xor (Val.and a b) (some (BitVec.allOnes w))) d) (some (BitVec.allOnes w)) := by
  cases a <;> cases b <;> vfinish

/-- `or a, (and a, b)` refines `a`. `IS.simplifyOrLogic.L2269`. -/
theorem or_and_absorb_refines (a b : Val w) (d : Bool) : Refines (Val.or a (Val.and a b) d) a := by
  cases a <;> cases b <;> vfinish

/-- `or (xor a, b), (or a, b)` refines `or a, b`. `IS.simplifyOrLogic.L2277`. -/
theorem or_xor_or_refines (a b : Val w) (d d' : Bool) :
    Refines (Val.or (Val.xor a b) (Val.or a b d') d) (Val.or a b d') := by
  cases a <;> cases b <;> vfinish

/-- `or (not (xor a, b)), (or a, b)` refines -1. `IS.simplifyOrLogic.L2283`. -/
theorem or_not_xor_or_refines (a b : Val w) (d d' : Bool) :
    Refines (Val.or (Val.xor (Val.xor a b) (some (BitVec.allOnes w))) (Val.or a b d') d)
      (some (BitVec.allOnes w)) := by
  cases a <;> cases b <;> vfinish

/-- `or (and a, (not b)), (xor a, b)` refines `xor a, b`. `IS.simplifyOrLogic.L2291`. -/
theorem or_and_not_xor_refines (a b : Val w) (d : Bool) :
    Refines (Val.or (Val.and a (Val.xor b (some (BitVec.allOnes w)))) (Val.xor a b) d) (Val.xor a b) := by
  cases a <;> cases b <;> vfinish

/-- `or (xor (not a), b), (and a, b)` refines `xor (not a), b`. `IS.simplifyOrLogic.L2299`. -/
theorem or_xor_not_and_refines (a b : Val w) (d : Bool) :
    Refines (Val.or (Val.xor (Val.xor a (some (BitVec.allOnes w))) b) (Val.and a b) d)
      (Val.xor (Val.xor a (some (BitVec.allOnes w))) b) := by
  cases a <;> cases b <;> vfinish

/-- `or (or (not a), b), (xor a, b)` refines -1. `IS.simplifyOrLogic.L2307`. -/
theorem or_or_not_xor_refines (a b : Val w) (d d' : Bool) :
    Refines (Val.or (Val.or (Val.xor a (some (BitVec.allOnes w))) b d') (Val.xor a b) d)
      (some (BitVec.allOnes w)) := by
  cases a <;> cases b <;> vfinish

/-- `or (and (not a), b), (not (or a, b))` refines `not a`. `IS.simplifyOrLogic.L2317`. -/
theorem or_and_not_not_or_refines (a b : Val w) (d d' : Bool) :
    Refines (Val.or (Val.and (Val.xor a (some (BitVec.allOnes w))) b)
      (Val.xor (Val.or a b d') (some (BitVec.allOnes w))) d) (Val.xor a (some (BitVec.allOnes w))) := by
  cases a <;> cases b <;> vfinish

/-- `m_c_LogicalAnd(P, Q)` on `i1` values: `and p, q` either way round, `select p, q, false` or
`select q, p, false`. -/
def IsLogicalAnd (x p q : Val 1) : Prop :=
  x = Val.and p q ∨ x = Val.and q p ∨ x = select p q (some 0#1) ∨ x = select q p (some 0#1)

/-- `m_c_LogicalOr(P, Q)` on `i1` values: `or p, q` either way round, with or without `disjoint`,
`select p, true, q` or `select q, true, p`. -/
def IsLogicalOr (y p q : Val 1) : Prop :=
  (∃ d, y = Val.or p q d ∨ y = Val.or q p d) ∨ y = select p (some 1#1) q ∨ y = select q (some 1#1) p

/-- `or (logical-and (not a), b), (not (logical-or a, b))` refines `not a`. `IS.simplifyOrLogic.L2324`. -/
theorem or_logicalAnd_not_logicalOr_refines (a b x y : Val 1) (d : Bool)
    (hx : IsLogicalAnd x (Val.xor a (some 1#1)) b) (hy : IsLogicalOr y a b) :
    Refines (Val.or x (Val.xor y (some 1#1)) d) (Val.xor a (some 1#1)) := by
  rw [refines_iff]
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with ⟨d', rfl | rfl⟩ | rfl | rfl <;>
  rcases a with _ | u <;> rcases b with _ | v <;>
  (try rcases bv1_cases u with rfl | rfl) <;> (try rcases bv1_cases v with rfl | rfl) <;>
  (try cases d') <;> cases d <;> decide

/-- `or (not (xor a, b)), (and a, b)` refines `not (xor a, b)`. `IS.simplifyOrLogic.L2332`. -/
theorem or_not_xor_and_refines (a b : Val w) (d : Bool) :
    Refines (Val.or (Val.xor (Val.xor a b) (some (BitVec.allOnes w))) (Val.and a b) d)
      (Val.xor (Val.xor a b) (some (BitVec.allOnes w))) := by
  cases a <;> cases b <;> vfinish

/-- `or (not (and a, b)), (xor a, b)` refines `not (and a, b)`. `IS.simplifyOrLogic.L2339`. -/
theorem or_not_and_xor_refines (a b : Val w) (d : Bool) :
    Refines (Val.or (Val.xor (Val.and a b) (some (BitVec.allOnes w))) (Val.xor a b) d)
      (Val.xor (Val.and a b) (some (BitVec.allOnes w))) := by
  cases a <;> cases b <;> vfinish

/-- `or (shl -1, (sub c, y)), (lshr -1, y)` refines -1 where `c ≤ w`. `IS.simplifyOrInst.L2387`. -/
theorem or_shl_lshr_allOnes_sub_left_refines (y : Val w) (c : BitVec w) (f1 f2 f3 f4 e d : Bool)
    (hc : c.toNat ≤ w) :
    Refines (Val.or (Val.shl (some (BitVec.allOnes w)) (Val.sub (some c) y f3 f4) f1 f2)
      (Val.lshr (some (BitVec.allOnes w)) y e) d) (some (BitVec.allOnes w)) := by
  cases y with
  | none => exact refines_none _
  | some v =>
    rcases sub_cases c v f3 f4 with h1 | ⟨-, h1⟩ <;> rw [h1]
    · exact refines_none _
    rcases shl_cases (BitVec.allOnes w) (c - v) f1 f2 with h2 | ⟨hx, h2⟩ <;> rw [h2]
    · exact refines_none _
    rcases lshr_cases (BitVec.allOnes w) v e with h3 | ⟨hy, h3⟩ <;> rw [h3]
    · rw [or_none_right]; exact refines_none _
    rcases or_cases (BitVec.allOnes w <<< (c - v).toNat) (BitVec.allOnes w >>> v.toNat) d with h4 | h4 <;> rw [h4]
    · exact refines_none _
    refine refines_some ?_
    rw [allOnes_shiftLeft_or_ushiftRight (by rw [toNat_sub_add_of_lt hx hy]; exact hc)]

/-- `or (shl -1, x), (lshr -1, (sub c, x))` refines -1 where `c ≤ w`. `IS.simplifyOrInst.L2387`. -/
theorem or_shl_lshr_allOnes_sub_right_refines (x : Val w) (c : BitVec w) (f1 f2 f3 f4 e d : Bool)
    (hc : c.toNat ≤ w) :
    Refines (Val.or (Val.shl (some (BitVec.allOnes w)) x f1 f2)
      (Val.lshr (some (BitVec.allOnes w)) (Val.sub (some c) x f3 f4) e) d) (some (BitVec.allOnes w)) := by
  cases x with
  | none => exact refines_none _
  | some u =>
    rcases shl_cases (BitVec.allOnes w) u f1 f2 with h2 | ⟨hx, h2⟩ <;> rw [h2]
    · exact refines_none _
    rcases sub_cases c u f3 f4 with h1 | ⟨-, h1⟩ <;> rw [h1]
    · rw [show Val.lshr (some (BitVec.allOnes w)) none e = none from rfl, or_none_right]; exact refines_none _
    rcases lshr_cases (BitVec.allOnes w) (c - u) e with h3 | ⟨hy, h3⟩ <;> rw [h3]
    · rw [or_none_right]; exact refines_none _
    rcases or_cases (BitVec.allOnes w <<< u.toNat) (BitVec.allOnes w >>> (c - u).toNat) d with h4 | h4 <;> rw [h4]
    · exact refines_none _
    refine refines_some ?_
    rw [allOnes_shiftLeft_or_ushiftRight (by rw [Nat.add_comm, toNat_sub_add_of_lt hy hx]; exact hc)]

/-- `or (fshl x, z, s), (shl x, s)` refines the `fshl`. `IS.simplifyOrInst.L2399`. -/
theorem or_fshl_shl_refines (x z s : Val w) (nuw nsw d : Bool) :
    Refines (Val.or (Val.fshl x z s) (Val.shl x s nuw nsw) d) (Val.fshl x z s) := by
  rcases x with _ | u
  · exact refines_none _
  rcases z with _ | v
  · exact refines_none _
  rcases s with _ | k
  · exact refines_none _
  rcases shl_cases u k nuw nsw with h1 | ⟨hk, h1⟩ <;> rw [h1]
  · rw [or_none_right]; exact refines_none _
  rcases or_cases (Val.fshlRaw u v k) (u <<< k.toNat) d with h2 | h2 <;>
    simp only [Val.fshl] at h2 ⊢ <;> rw [h2]
  · exact refines_none _
  · exact refines_some (fshlRaw_or_shiftLeft hk).symm

/-- `or (fshr z, x, s), (lshr x, s)` refines the `fshr`. `IS.simplifyOrInst.L2410`. -/
theorem or_fshr_lshr_refines (z x s : Val w) (exact d : Bool) :
    Refines (Val.or (Val.fshr z x s) (Val.lshr x s exact) d) (Val.fshr z x s) := by
  rcases z with _ | v
  · exact refines_none _
  rcases x with _ | u
  · exact refines_none _
  rcases s with _ | k
  · exact refines_none _
  rcases lshr_cases u k exact with h1 | ⟨hk, h1⟩ <;> rw [h1]
  · rw [or_none_right]; exact refines_none _
  rcases or_cases (Val.fshrRaw v u k) (u >>> k.toNat) d with h2 | h2 <;>
    simp only [Val.fshr] at h2 ⊢ <;> rw [h2]
  · exact refines_none _
  · exact refines_some (fshrRaw_or_ushiftRight hk).symm

/-- `or (and (add b, n), ~c), (and b, c)` refines `add b, n` where `c` is a mask of low bits and `n` has none of
them. `IS.simplifyOrInst.L2475`. -/
theorem or_and_add_and_lowMask_refines (b n : Val w) (c : BitVec w) (f1 f2 d : Bool)
    (hc : c &&& (c + 1#w) = 0#w) (hn : ∀ v, n = some v → v &&& c = 0#w) :
    Refines (Val.or (Val.and (Val.add b n f1 f2) (some (~~~c))) (Val.and b (some c)) d) (Val.add b n f1 f2) := by
  rcases b with _ | u
  · exact refines_none _
  rcases n with _ | v
  · exact refines_none _
  rcases add_cases u v f1 f2 with h1 | h1 <;> rw [h1]
  · exact refines_none _
  rw [and_some, and_some]
  rcases or_cases ((u + v) &&& ~~~c) (u &&& c) d with h2 | h2 <;> rw [h2]
  · exact refines_none _
  refine refines_some ?_
  rw [← add_and_lowMask hc (hn v rfl) (u := u)]
  bitwise

/-- `or (xor a, c), (xor a, ~c)` refines -1. `IS.simplifyOrInst.L2495`. -/
theorem or_xor_xor_not_refines (a : Val w) (c : BitVec w) (d : Bool) :
    Refines (Val.or (Val.xor a (some c)) (Val.xor a (some (~~~c))) d) (some (BitVec.allOnes w)) := by
  cases a <;> vfinish

/-! ### `xor` -/

/-- `xor (not a), a` refines -1. `IS.simplifyXorInst.L2553`. -/
theorem xor_not_self_refines (a : Val w) :
    Refines (Val.xor (Val.xor a (some (BitVec.allOnes w))) a) (some (BitVec.allOnes w)) := by
  cases a <;> vfinish

/-- `xor (and (not a), b), (or a, b)` refines `a`. `IS.simplifyXorInst.foldAndOrNot.L2560`. -/
theorem xor_and_not_or_refines (a b : Val w) (d : Bool) :
    Refines (Val.xor (Val.and (Val.xor a (some (BitVec.allOnes w))) b) (Val.or a b d)) a := by
  cases a <;> cases b <;> vfinish

/-- `xor (or (not a), b), (and a, b)` refines `not a`. `IS.simplifyXorInst.foldAndOrNot.L2569`. -/
theorem xor_or_not_and_refines (a b : Val w) (d : Bool) :
    Refines (Val.xor (Val.or (Val.xor a (some (BitVec.allOnes w))) b d) (Val.and a b))
      (Val.xor a (some (BitVec.allOnes w))) := by
  cases a <;> cases b <;> vfinish

/-- `xor (sub nuw c, x), c` refines `x` where `c` is a mask of low bits. `IS.simplifyXorInst.L2603`. -/
theorem xor_sub_nuw_lowMask_refines (x : Val w) (c : BitVec w) (nsw : Bool) (hc : c &&& (c + 1#w) = 0#w) :
    Refines (Val.xor (Val.sub (some c) x true nsw) (some c)) x := by
  rcases x with _ | u
  · exact refines_none _
  rcases sub_cases c u true nsw with h1 | ⟨hle, h1⟩ <;> rw [h1]
  · exact refines_none _
  rw [xor_some]
  refine refines_some ?_
  rw [sub_of_and_eq (and_lowMask_of_le hc (hle rfl)), BitVec.xor_assoc, BitVec.xor_comm u c,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end Peephole.Lemmas

/-! ### Counterexamples

For each hypothesis of a lemma above, the lemma without it is false: `drop_<hypothesis>` gives one input where it
fails. For each lemma with hypotheses, `sat` gives one input where they all hold. They're in the form
`store/LemmaStore/Counter/Generic.lean` has, for the store to admit with the lemmas. -/

namespace LemmaStore.Counter

open IRLean Peephole.Lemmas

/-- `and (sub 0, 3), 3` in `i2` is `1`: 3 isn't a power of two. -/
theorem Peephole.Lemmas.and_neg_self_refines.drop_h :
    ¬ ∀ {w : Nat} (a : Val w) (nuw nsw : Bool), Refines (Val.and (Val.sub (some 0#w) a nuw nsw) a) a :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 1#2 (by decide) (by decide) (@h 2 (some 3#2) false false)

theorem Peephole.Lemmas.and_neg_self_refines.sat :
    ∃ (w : Nat) (a : Val w) (_ _ : Bool), ∀ x, a = some x → x.toNat.isPowerOfTwo ∨ x = 0#w :=
  ⟨1, none, false, false, fun _ h => by cases h⟩

/-- `and (add 3, -1), 3` in `i2` is `2`. -/
theorem Peephole.Lemmas.and_add_allOnes_self_refines.drop_h :
    ¬ ∀ {w : Nat} (a : Val w) (nuw nsw : Bool),
      Refines (Val.and (Val.add a (some (BitVec.allOnes w)) nuw nsw) a) (some 0#w) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 2#2 (by decide) (by decide) (@h 2 (some 3#2) false false)

theorem Peephole.Lemmas.and_add_allOnes_self_refines.sat :
    ∃ (w : Nat) (a : Val w) (_ _ : Bool), ∀ x, a = some x → x.toNat.isPowerOfTwo ∨ x = 0#w :=
  ⟨1, none, false, false, fun _ h => by cases h⟩

/-- `and (shl 3, 0), (add (shl 3, 0), -1)` in `i4` is `2`: 3 isn't a power of two. -/
theorem Peephole.Lemmas.and_shl_shl_add_allOnes_refines.drop_h :
    ¬ ∀ {w : Nat} (a : Val w) (n m : BitVec w) (f1 f2 f3 f4 f5 f6 : Bool), m.toNat ≤ n.toNat →
      Refines (Val.and (Val.shl a (some n) f1 f2)
        (Val.add (Val.shl a (some m) f3 f4) (some (BitVec.allOnes w)) f5 f6)) (some 0#w) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 2#4 (by decide) (by decide)
    (@h 4 (some 3#4) 0#4 0#4 false false false false false false (by decide))

/-- `and (shl 1, 0), (add (shl 1, 1), -1)` in `i4` is `1`: the second shift is the larger. -/
theorem Peephole.Lemmas.and_shl_shl_add_allOnes_refines.drop_hmn :
    ¬ ∀ {w : Nat} (a : Val w) (n m : BitVec w) (f1 f2 f3 f4 f5 f6 : Bool),
      (∀ x, a = some x → x.toNat.isPowerOfTwo ∨ x = 0#w) →
      Refines (Val.and (Val.shl a (some n) f1 f2)
        (Val.add (Val.shl a (some m) f3 f4) (some (BitVec.allOnes w)) f5 f6)) (some 0#w) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 1#4 (by decide) (by decide)
    (@h 4 (some 1#4) 0#4 1#4 false false false false false false
      (fun x hx => by cases hx; exact .inl (by decide)))

theorem Peephole.Lemmas.and_shl_shl_add_allOnes_refines.sat :
    ∃ (w : Nat) (a : Val w) (n m : BitVec w) (_ _ _ _ _ _ : Bool),
      (∀ x, a = some x → x.toNat.isPowerOfTwo ∨ x = 0#w) ∧ m.toNat ≤ n.toNat :=
  ⟨1, none, 0#1, 0#1, false, false, false, false, false, false, ⟨(fun _ h => by cases h), Nat.le_refl _⟩⟩

/-- `and (shl 1, 0), 0` in `i2` is `0`, not `1`. -/
theorem Peephole.Lemmas.and_shl_mask.drop_h :
    ¬ ∀ {w : Nat} (a : Val w) (s m : BitVec w) (nuw nsw : Bool),
      Val.and (Val.shl a (some s) nuw nsw) (some m) = Val.shl a (some s) nuw nsw :=
  fun h => absurd (@h 2 (some 1#2) 0#2 0#2 false false) (by decide)

theorem Peephole.Lemmas.and_shl_mask.sat :
    ∃ (w : Nat) (_ : Val w) (s m : BitVec w) (_ _ : Bool), ~~~m >>> s.toNat = 0#w :=
  ⟨1, none, 0#1, 1#1, false, false, by decide⟩

/-- `and (lshr 1, 0), 0` in `i2` is `0`, not `1`. -/
theorem Peephole.Lemmas.and_lshr_mask.drop_h :
    ¬ ∀ {w : Nat} (a : Val w) (s m : BitVec w) (exact : Bool),
      Val.and (Val.lshr a (some s) exact) (some m) = Val.lshr a (some s) exact :=
  fun h => absurd (@h 2 (some 1#2) 0#2 0#2 false) (by decide)

theorem Peephole.Lemmas.and_lshr_mask.sat :
    ∃ (w : Nat) (_ : Val w) (s m : BitVec w) (_ : Bool), ~~~m <<< s.toNat = 0#w :=
  ⟨1, none, 0#1, 1#1, false, by decide⟩

/-- `and (add 0, -1), 1` in `i2` is `1`: 0 isn't a power of two. -/
theorem Peephole.Lemmas.and_add_allOnes_twoPow_refines.drop_ha :
    ¬ ∀ {w : Nat} (a : Val w) (c : BitVec w) (nuw nsw : Bool), c.toNat.isPowerOfTwo →
      Refines (Val.and (Val.add a (some (BitVec.allOnes w)) nuw nsw) (some c)) (some 0#w) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 1#2 (by decide) (by decide)
    (@h 2 (some 0#2) 1#2 false false (by decide))

/-- `and (add 2, -1), 3` in `i2` is `1`: 3 isn't a power of two. -/
theorem Peephole.Lemmas.and_add_allOnes_twoPow_refines.drop_hc :
    ¬ ∀ {w : Nat} (a : Val w) (c : BitVec w) (nuw nsw : Bool),
      (∀ x, a = some x → x.toNat.isPowerOfTwo ∧ x.toNat < 2 * c.toNat) →
      Refines (Val.and (Val.add a (some (BitVec.allOnes w)) nuw nsw) (some c)) (some 0#w) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 1#2 (by decide) (by decide)
    (@h 2 (some 2#2) 3#2 false false (fun x hx => by cases hx; exact ⟨by decide, by decide⟩))

theorem Peephole.Lemmas.and_add_allOnes_twoPow_refines.sat :
    ∃ (w : Nat) (a : Val w) (c : BitVec w) (_ _ : Bool),
      (∀ x, a = some x → x.toNat.isPowerOfTwo ∧ x.toNat < 2 * c.toNat) ∧ c.toNat.isPowerOfTwo :=
  ⟨1, none, 1#1, false, false, ⟨(fun _ h => by cases h), by decide⟩⟩

/-- `and (or (shl 0, 0), 1), 0` in `i2` is `0`, not `1`: the mask drops a bit of `y`. -/
theorem Peephole.Lemmas.and_or_shl_mask_refines_right.drop_hy :
    ¬ ∀ {w : Nat} (x y : Val w) (s m : BitVec w) (nuw nsw d : Bool),
      (∀ u, x = some u → (u <<< s.toNat) &&& m = 0#w) →
      Refines (Val.and (Val.or (Val.shl x (some s) nuw nsw) y d) (some m)) y :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 0#2 (by decide) (by decide)
    (@h 2 (some 0#2) (some 1#2) 0#2 0#2 false false false (fun u hu => by cases hu; decide))

/-- `and (or (shl 1, 0), 0), 3` in `i2` is `1`, not `0`: the mask keeps a bit of `x << s`. -/
theorem Peephole.Lemmas.and_or_shl_mask_refines_right.drop_hx :
    ¬ ∀ {w : Nat} (x y : Val w) (s m : BitVec w) (nuw nsw d : Bool),
      (∀ v, y = some v → v &&& m = v) →
      Refines (Val.and (Val.or (Val.shl x (some s) nuw nsw) y d) (some m)) y :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 1#2 (by decide) (by decide)
    (@h 2 (some 1#2) (some 0#2) 0#2 3#2 false false false (fun v hv => by cases hv; decide))

theorem Peephole.Lemmas.and_or_shl_mask_refines_right.sat :
    ∃ (w : Nat) (x y : Val w) (s m : BitVec w) (_ _ _ : Bool),
      (∀ v, y = some v → v &&& m = v) ∧ (∀ u, x = some u → (u <<< s.toNat) &&& m = 0#w) :=
  ⟨1, none, none, 0#1, 0#1, false, false, false, ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩⟩

/-- `and (or (shl 0, 0), 1), 1` in `i2` is `1`, not `0`: the mask keeps a bit of `y`. -/
theorem Peephole.Lemmas.and_or_shl_mask_refines_left.drop_hy :
    ¬ ∀ {w : Nat} (x y : Val w) (s m : BitVec w) (nuw nsw d : Bool),
      (∀ u, x = some u → (u <<< s.toNat) &&& m = u <<< s.toNat) →
      Refines (Val.and (Val.or (Val.shl x (some s) nuw nsw) y d) (some m)) (Val.shl x (some s) nuw nsw) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 1#2 (by decide) (by decide)
    (@h 2 (some 0#2) (some 1#2) 0#2 1#2 false false false (fun u hu => by cases hu; decide))

/-- `and (or (shl 1, 0), 0), 0` in `i2` is `0`, not `1`: the mask drops a bit of `x << s`. -/
theorem Peephole.Lemmas.and_or_shl_mask_refines_left.drop_hx :
    ¬ ∀ {w : Nat} (x y : Val w) (s m : BitVec w) (nuw nsw d : Bool),
      (∀ v, y = some v → v &&& m = 0#w) →
      Refines (Val.and (Val.or (Val.shl x (some s) nuw nsw) y d) (some m)) (Val.shl x (some s) nuw nsw) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 0#2 (by decide) (by decide)
    (@h 2 (some 1#2) (some 0#2) 0#2 0#2 false false false (fun v hv => by cases hv; decide))

theorem Peephole.Lemmas.and_or_shl_mask_refines_left.sat :
    ∃ (w : Nat) (x y : Val w) (s m : BitVec w) (_ _ _ : Bool),
      (∀ v, y = some v → v &&& m = 0#w) ∧ (∀ u, x = some u → (u <<< s.toNat) &&& m = u <<< s.toNat) :=
  ⟨1, none, none, 0#1, 0#1, false, false, false, ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩⟩

/-- `and true, false` is false. -/
theorem Peephole.Lemmas.and_refines_left_of_implies.drop_h :
    ¬ ∀ (a b : Val 1), Refines (Val.and a b) a :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 0#1 (by decide) (by decide) (h (some 1#1) (some 0#1))

theorem Peephole.Lemmas.and_refines_left_of_implies.sat :
    ∃ (a b : Val 1), a = some 1#1 → b = none ∨ b = some 1#1 := ⟨none, none, fun h => by cases h⟩

/-- `and true, true` is true. -/
theorem Peephole.Lemmas.and_refines_false_of_implies.drop_h :
    ¬ ∀ (a b : Val 1), Refines (Val.and a b) (some 0#1) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 1#1 (by decide) (by decide) (h (some 1#1) (some 1#1))

theorem Peephole.Lemmas.and_refines_false_of_implies.sat :
    ∃ (a b : Val 1), a = some 1#1 → b = none ∨ b = some 0#1 := ⟨none, none, fun h => by cases h⟩

/-- `and false, true` is false. -/
theorem Peephole.Lemmas.and_refines_right_of_false.drop_h :
    ¬ ∀ (a b : Val 1), Refines (Val.and a b) b :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 0#1 (by decide) (by decide) (h (some 0#1) (some 1#1))

theorem Peephole.Lemmas.and_refines_right_of_false.sat :
    ∃ (a b : Val 1), a = some 0#1 → b = none ∨ b = some 0#1 := ⟨none, none, fun h => by cases h⟩

/-- `or false, true` is true. -/
theorem Peephole.Lemmas.or_refines_left_of_implies.drop_h :
    ¬ ∀ (a b : Val 1) (d : Bool), Refines (Val.or a b d) a :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 1#1 (by decide) (by decide) (h (some 0#1) (some 1#1) false)

theorem Peephole.Lemmas.or_refines_left_of_implies.sat :
    ∃ (a b : Val 1) (_ : Bool), a = some 0#1 → b = none ∨ b = some 0#1 := ⟨none, none, false, fun h => by cases h⟩

/-- `or false, false` is false. -/
theorem Peephole.Lemmas.or_refines_true_of_implies.drop_h :
    ¬ ∀ (a b : Val 1) (d : Bool), Refines (Val.or a b d) (some 1#1) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 0#1 (by decide) (by decide) (h (some 0#1) (some 0#1) false)

theorem Peephole.Lemmas.or_refines_true_of_implies.sat :
    ∃ (a b : Val 1) (_ : Bool), a = some 0#1 → b = none ∨ b = some 1#1 := ⟨none, none, false, fun h => by cases h⟩

/-- `or true, false` is true. -/
theorem Peephole.Lemmas.or_refines_right_of_true.drop_h :
    ¬ ∀ (a b : Val 1) (d : Bool), Refines (Val.or a b d) b :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 1#1 (by decide) (by decide) (h (some 1#1) (some 0#1) false)

theorem Peephole.Lemmas.or_refines_right_of_true.sat :
    ∃ (a b : Val 1) (_ : Bool), a = some 1#1 → b = none ∨ b = some 1#1 := ⟨none, none, false, fun h => by cases h⟩

/-- With `a` and `b` true and `x` true, which isn't `and (not a), b`, the `or` is true and `not a` false. -/
theorem Peephole.Lemmas.or_logicalAnd_not_logicalOr_refines.drop_hx :
    ¬ ∀ (a b x y : Val 1) (d : Bool), IsLogicalOr y a b →
      Refines (Val.or x (Val.xor y (some 1#1)) d) (Val.xor a (some 1#1)) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 1#1 (by decide) (by decide)
    (h (some 1#1) (some 1#1) (some 1#1) (some 1#1) false (.inl ⟨false, .inl (by decide)⟩))

/-- With `a` true and `b` false, and `y` false, which isn't `or a, b`, the `or` is true and `not a` false. -/
theorem Peephole.Lemmas.or_logicalAnd_not_logicalOr_refines.drop_hy :
    ¬ ∀ (a b x y : Val 1) (d : Bool), IsLogicalAnd x (Val.xor a (some 1#1)) b →
      Refines (Val.or x (Val.xor y (some 1#1)) d) (Val.xor a (some 1#1)) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 1#1 (by decide) (by decide)
    (h (some 1#1) (some 0#1) (some 0#1) (some 0#1) false (.inl (by decide)))

theorem Peephole.Lemmas.or_logicalAnd_not_logicalOr_refines.sat :
    ∃ (a b x y : Val 1) (_ : Bool), IsLogicalAnd x (Val.xor a (some 1#1)) b ∧ IsLogicalOr y a b :=
  ⟨none, none, none, none, false, ⟨.inl rfl, .inl ⟨false, .inl rfl⟩⟩⟩

/-- In `i3`, `or (shl -1, (sub 4, 2)), (lshr -1, 2)` is `5`: 4 is more than the width. -/
theorem Peephole.Lemmas.or_shl_lshr_allOnes_sub_left_refines.drop_hc :
    ¬ ∀ {w : Nat} (y : Val w) (c : BitVec w) (f1 f2 f3 f4 e d : Bool),
      Refines (Val.or (Val.shl (some (BitVec.allOnes w)) (Val.sub (some c) y f3 f4) f1 f2)
        (Val.lshr (some (BitVec.allOnes w)) y e) d) (some (BitVec.allOnes w)) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 5#3 (by decide) (by decide)
    (@h 3 (some 2#3) 4#3 false false false false false false)

theorem Peephole.Lemmas.or_shl_lshr_allOnes_sub_left_refines.sat :
    ∃ (w : Nat) (_ : Val w) (c : BitVec w) (_ _ _ _ _ _ : Bool), c.toNat ≤ w :=
  ⟨1, none, 0#1, false, false, false, false, false, false, by decide⟩

/-- In `i3`, `or (shl -1, 2), (lshr -1, (sub 4, 2))` is `5`: 4 is more than the width. -/
theorem Peephole.Lemmas.or_shl_lshr_allOnes_sub_right_refines.drop_hc :
    ¬ ∀ {w : Nat} (x : Val w) (c : BitVec w) (f1 f2 f3 f4 e d : Bool),
      Refines (Val.or (Val.shl (some (BitVec.allOnes w)) x f1 f2)
        (Val.lshr (some (BitVec.allOnes w)) (Val.sub (some c) x f3 f4) e) d) (some (BitVec.allOnes w)) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 5#3 (by decide) (by decide)
    (@h 3 (some 2#3) 4#3 false false false false false false)

theorem Peephole.Lemmas.or_shl_lshr_allOnes_sub_right_refines.sat :
    ∃ (w : Nat) (_ : Val w) (c : BitVec w) (_ _ _ _ _ _ : Bool), c.toNat ≤ w :=
  ⟨1, none, 0#1, false, false, false, false, false, false, by decide⟩

/-- In `i2`, with `c = 2`, not a mask of low bits, `or (and (add 1, 1), 1), (and 1, 2)` is `0`, not `2`. -/
theorem Peephole.Lemmas.or_and_add_and_lowMask_refines.drop_hc :
    ¬ ∀ {w : Nat} (b n : Val w) (c : BitVec w) (f1 f2 d : Bool), (∀ v, n = some v → v &&& c = 0#w) →
      Refines (Val.or (Val.and (Val.add b n f1 f2) (some (~~~c))) (Val.and b (some c)) d) (Val.add b n f1 f2) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 0#2 (by decide) (by decide)
    (@h 2 (some 1#2) (some 1#2) 2#2 false false false (fun v hv => by cases hv; decide))

/-- In `i2`, with `n = 1` inside the mask `c = 1`, `or (and (add 0, 1), 2), (and 0, 1)` is `0`, not `1`. -/
theorem Peephole.Lemmas.or_and_add_and_lowMask_refines.drop_hn :
    ¬ ∀ {w : Nat} (b n : Val w) (c : BitVec w) (f1 f2 d : Bool), c &&& (c + 1#w) = 0#w →
      Refines (Val.or (Val.and (Val.add b n f1 f2) (some (~~~c))) (Val.and b (some c)) d) (Val.add b n f1 f2) :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 0#2 (by decide) (by decide)
    (@h 2 (some 0#2) (some 1#2) 1#2 false false false (by decide))

theorem Peephole.Lemmas.or_and_add_and_lowMask_refines.sat :
    ∃ (w : Nat) (_ n : Val w) (c : BitVec w) (_ _ _ : Bool),
      c &&& (c + 1#w) = 0#w ∧ ∀ v, n = some v → v &&& c = 0#w :=
  ⟨1, none, none, 0#1, false, false, false, ⟨by decide, fun _ h => by cases h⟩⟩

/-- In `i2`, `xor (sub nuw 2, 1), 2` is `3`, not `1`: 2 isn't a mask of low bits. -/
theorem Peephole.Lemmas.xor_sub_nuw_lowMask_refines.drop_hc :
    ¬ ∀ {w : Nat} (x : Val w) (c : BitVec w) (nsw : Bool), Refines (Val.xor (Val.sub (some c) x true nsw) (some c)) x :=
  fun h => _root_.Peephole.Lemmas.Logic.not_refines 3#2 (by decide) (by decide) (@h 2 (some 1#2) 2#2 false)

theorem Peephole.Lemmas.xor_sub_nuw_lowMask_refines.sat :
    ∃ (w : Nat) (_ : Val w) (c : BitVec w) (_ : Bool), c &&& (c + 1#w) = 0#w :=
  ⟨1, none, 0#1, false, by decide⟩

end LemmaStore.Counter
