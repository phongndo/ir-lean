import LlvmAPInt
import Words

/-! The word-array routines at the bottom of `llvm::APInt`, in `llvm/lib/Support/APInt.cpp`, which LLVM's constant folder and
every analysis over wide integers run on. -/

set_option linter.unusedSimpArgs false

namespace Llvm.APInt

open IRLean LlvmAPInt

variable {m : Mem} {t : List Tag} {block o : Nat} {w : Nat → BitVec 64}

abbrev effects : Effects := { other := .none, arg := .read, inaccessible := .none, errno := .none }

abbrev readTag (m : Mem) : Tag := { call := m.nextCall, readonly := true, nofree := true, expires := true, noAddress := true }

section IsZero

local notation "Z" => _ZN4llvm5APInt8tcIsZeroEPKmj

theorem isZero_loop {n : Nat} (W : Words m t block o n w) {wtc : BitVec 64} (hw : wtc.toNat = n) :
    ∀ (r i : Nat), r = n - i → i < n → (∀ j, j < i → w j = 0#64) →
      run _ZN4llvm5APInt8tcIsZeroEPKmj.step (.for_body m (some (BitVec.ofNat 64 i)) (some (bufPtr t block o 0)) (some wtc)) =
      Outcome.ok (some (BitVec.ofBool (wordsValue w n == 0)), m) := by
  have hn : n < 2 ^ 61 := by
    obtain ⟨a, ha, hsz, hmax, hd⟩ := W.bytes.alloc
    omega
  intro r
  induction r with
  | zero =>
    intro i hr hi hz
    omega
  | succ r ih =>
    intro i hr hi hz
    have h1 := W.index' hi
    have h2 := W.load hi
    rw [run]
    llvm_simp [_ZN4llvm5APInt8tcIsZeroEPKmj.step, h1, h2, add_one (show i < 2 ^ 61 by omega)]
    apply ite_cases <;> intro hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
      have hw0 : w i = 0#64 := by simpa using hc.1
      have hmore : i + 1 < n := by
        rcases Nat.lt_or_ge (i + 1) n with h | h
        · exact h
        · exact absurd (BitVec.eq_of_toNat_eq (by
            rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            omega)) hc.2
      exact ih (i + 1) (by omega) hmore (fun j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hz j hj
        · exact hw0)
    · llvm_step _ZN4llvm5APInt8tcIsZeroEPKmj.step
      by_cases hw0 : w i = 0#64
      · have hlast : ¬ i + 1 < n := by
          intro hlt
          apply hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
          refine ⟨by simpa using hw0, fun e => ?_⟩
          have := congrArg BitVec.toNat e
          rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          omega
        have hall : wordsValue w n = 0 := (wordsValue_eq_zero w n).mpr (fun j hj => by
          rcases Nat.lt_or_ge j i with h | h
          · exact hz j h
          · have : j = i := by omega
            subst this
            exact hw0)
        have e1 : (w i == 0#64) = true := by simpa using hw0
        have e2 : (wordsValue w n == 0) = true := by simpa using hall
        rw [e1, e2]
      · have hnot : wordsValue w n ≠ 0 := fun e => hw0 ((wordsValue_eq_zero w n).mp e i hi)
        have e1 : (w i == 0#64) = false := by simpa using hw0
        have e2 : (wordsValue w n == 0) = false := by simpa using hnot
        rw [e1, e2]

/-- `llvm::APInt::tcIsZero`: whether the number an array of `parts` words holds is zero. -/
theorem tcIsZero_correct {parts : BitVec 32} (W : Words m t block o parts.toNat w) :
    _ZN4llvm5APInt8tcIsZeroEPKmj (some (bufPtr t block o 0)) (some parts) m =
      Outcome.ok (some (BitVec.ofBool (wordsValue w parts.toNat == 0)), m.afterCall) := by
  have W' := W.enter (e := effects) (T := readTag m) (Or.inl rfl) rfl rfl rfl rfl
  simp only [_ZN4llvm5APInt8tcIsZeroEPKmj, noundef_some, Mem.call, Mem.tag, Option.map]
  have hrun : run _ZN4llvm5APInt8tcIsZeroEPKmj.step (.entry (m.inCall effects) (some (bufPtr (readTag m :: t) block o 0)) (some parts)) =
      Outcome.ok (some (BitVec.ofBool (wordsValue w parts.toNat == 0)), m.inCall effects) := by
    llvm_step _ZN4llvm5APInt8tcIsZeroEPKmj.step
    apply ite_cases <;> intro h0
    · have hp : parts = 0#32 := by simpa using h0
      subst hp
      llvm_step _ZN4llvm5APInt8tcIsZeroEPKmj.step
      simp [wordsValue]
    · have hpos : 0 < parts.toNat := by
        rcases Nat.eq_zero_or_pos parts.toNat with h | h
        · exact absurd (by simpa using BitVec.eq_of_toNat_eq (x := parts) (y := 0#32) (by simpa using h)) h0
        · exact h
      llvm_step _ZN4llvm5APInt8tcIsZeroEPKmj.step
      have hw : (parts.setWidth 64).toNat = parts.toNat := by
        simp only [BitVec.toNat_setWidth, Nat.reducePow]
        have := parts.isLt
        omega
      exact isZero_loop W' hw _ 0 rfl hpos (fun j hj => by omega)
  rw [show run _ZN4llvm5APInt8tcIsZeroEPKmj.step _ = _ from hrun]
  rfl

end IsZero

section Compare

variable {t' : List Tag} {block' o' : Nat} {x : Nat → BitVec 64}

/-- How `tcCompare` says two numbers compare. -/
def compareResult (a b : Nat) : BitVec 32 := if a = b then 0#32 else if b < a then 1#32 else 4294967295#32

theorem compare_ne {n i : Nat} (hi : i < n) (hsame : ∀ j, i < j → j < n → w j = x j) (hne : w i ≠ x i) :
    (if (w i).toNat > (x i).toNat then 1#32 else 4294967295#32) = compareResult (wordsValue w n) (wordsValue x n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = i + 1 + k := ⟨n - (i + 1), by omega⟩
  have hne' : (w i).toNat ≠ (x i).toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
  rcases Nat.lt_or_gt_of_ne hne' with h | h
  · have := wordsValue_lt_of_top h k hsame
    simp only [compareResult]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · have := wordsValue_lt_of_top h k (fun j hj hj' => (hsame j hj hj').symm)
    simp only [compareResult]
    rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem compare_return {r : BitVec 32} (h : r = 0#32 ∨ r = 1#32 ∨ r = 4294967295#32) :
    run _ZN4llvm5APInt9tcCompareEPKmS2_j.step (.return_1 m (some r)) = Outcome.ok (some r, m) := by
  have hr : (r - 4294967295#32).ult (2#32 - 4294967295#32) = true := by bv_decide
  rw [run]
  simp only [_ZN4llvm5APInt9tcCompareEPKmS2_j.step, Val.range, hr, ite_true, noundef_some, ret, Outcome.ok]

/-- One word, going down. -/
theorem compare_body {n i : Nat} (WL : Words m t block o n w) (WR : Words m t' block' o' n x) (hi : i < n) (hn : n < 2 ^ 60) :
    run _ZN4llvm5APInt9tcCompareEPKmS2_j.step
      (.while_body m (some (BitVec.ofNat 64 (i + 1))) (some (bufPtr t block o 0)) (some (bufPtr t' block' o' 0))) =
    if (w i == x i) = true then
      run _ZN4llvm5APInt9tcCompareEPKmS2_j.step
        (.while_cond m (some (bufPtr t block o 0)) (some (bufPtr t' block' o' 0)) (some (BitVec.ofNat 64 i)))
    else run _ZN4llvm5APInt9tcCompareEPKmS2_j.step (.if_then m (some (w i)) (some (x i))) := by
  rw [run]
  llvm_simp [_ZN4llvm5APInt9tcCompareEPKmS2_j.step, WL.index' hi, WL.load hi, WR.index' hi, WR.load hi,
    sub_one (show i < 2 ^ 61 by omega)]

/-- The loop, comparing from word `i` down. -/
theorem compare_loop {n : Nat} (WL : Words m t block o n w) (WR : Words m t' block' o' n x) (i : Nat) :
    i < n → (∀ j, i < j → j < n → w j = x j) →
      run _ZN4llvm5APInt9tcCompareEPKmS2_j.step
        (.while_body m (some (BitVec.ofNat 64 (i + 1))) (some (bufPtr t block o 0)) (some (bufPtr t' block' o' 0))) =
      Outcome.ok (some (compareResult (wordsValue w n) (wordsValue x n)), m) := by
  have hn : n < 2 ^ 60 := by
    obtain ⟨a, ha, hsz, hmax, hd⟩ := WL.bytes.alloc
    omega
  have hdiffer : ∀ i, i < n → (∀ j, i < j → j < n → w j = x j) → ¬ (w i == x i) = true →
      run _ZN4llvm5APInt9tcCompareEPKmS2_j.step (.if_then m (some (w i)) (some (x i))) =
        Outcome.ok (some (compareResult (wordsValue w n) (wordsValue x n)), m) := by
    intro i hi hsame hne
    have hne' : w i ≠ x i := by simpa using hne
    have hres := compare_ne hi hsame hne'
    llvm_step _ZN4llvm5APInt9tcCompareEPKmS2_j.step
    have hcase : (if (x i).ult (w i) = true then 1#32 else 4294967295#32) = 0#32 ∨
        (if (x i).ult (w i) = true then 1#32 else 4294967295#32) = 1#32 ∨
        (if (x i).ult (w i) = true then 1#32 else 4294967295#32) = 4294967295#32 := by
      split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    rw [compare_return hcase]
    congr 3
    rw [← hres]
    simp only [BitVec.ult, gt_iff_lt, decide_eq_true_eq]
  induction i with
  | zero =>
    intro hi hsame
    rw [compare_body WL WR hi hn]
    apply ite_cases <;> intro heq
    · llvm_step _ZN4llvm5APInt9tcCompareEPKmS2_j.step
      simp only [beq_self_eq_true, ite_true]
      rw [compare_return (Or.inl rfl)]
      have hall : wordsValue w n = wordsValue x n := wordsValue_congr n (fun j hj => by
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · simpa using heq
        · exact hsame j hj0 hj)
      simp only [compareResult, hall, ite_true]
      rfl
    · exact hdiffer 0 hi hsame heq
  | succ i ih =>
    intro hi hsame
    rw [compare_body WL WR hi hn]
    apply ite_cases <;> intro heq
    · llvm_step _ZN4llvm5APInt9tcCompareEPKmS2_j.step
      have hne : (BitVec.ofNat 64 (i + 1) == 0#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        simp at this
      simp only [hne, Bool.false_eq_true, ite_false]
      exact ih (by omega) (fun j hj hj' => by
        rcases Nat.lt_or_ge (i + 1) j with h | h
        · exact hsame j h hj'
        · have : j = i + 1 := by omega
          subst this
          simpa using heq)
    · exact hdiffer (i + 1) hi hsame heq

/-- `llvm::APInt::tcCompare`: how the numbers two arrays of `parts` words hold compare. -/
theorem tcCompare_correct {parts : BitVec 32} (WL : Words m t block o parts.toNat w)
    (WR : Words m t' block' o' parts.toNat x) :
    _ZN4llvm5APInt9tcCompareEPKmS2_j (some (bufPtr t block o 0)) (some (bufPtr t' block' o' 0)) (some parts) m =
      Outcome.ok (some (compareResult (wordsValue w parts.toNat) (wordsValue x parts.toNat)), m.afterCall) := by
  have WL' := WL.enter (e := effects) (T := readTag m) (Or.inl rfl) rfl rfl rfl rfl
  have WR' := WR.enter (e := effects) (T := readTag m) (Or.inl rfl) rfl rfl rfl rfl
  simp only [_ZN4llvm5APInt9tcCompareEPKmS2_j, noundef_some, Mem.call, Mem.tag, Option.map]
  have hrun : run _ZN4llvm5APInt9tcCompareEPKmS2_j.step (.entry (m.inCall effects)
      (some (bufPtr (readTag m :: t) block o 0)) (some (bufPtr (readTag m :: t') block' o' 0)) (some parts)) =
      Outcome.ok (some (compareResult (wordsValue w parts.toNat) (wordsValue x parts.toNat)), m.inCall effects) := by
    llvm_step _ZN4llvm5APInt9tcCompareEPKmS2_j.step
    apply ite_cases <;> intro h0
    · have hp : parts = 0#32 := by simpa using h0
      subst hp
      rw [compare_return (Or.inl rfl)]
      simp only [compareResult, BitVec.toNat_ofNat, Nat.zero_mod, wordsValue, ite_true]
      rfl
    · have hpos : 0 < parts.toNat := by
        rcases Nat.eq_zero_or_pos parts.toNat with h | h
        · exact absurd (by simpa using BitVec.eq_of_toNat_eq (x := parts) (y := 0#32) (by simpa using h)) h0
        · exact h
      llvm_step _ZN4llvm5APInt9tcCompareEPKmS2_j.step
      have hw : parts.setWidth 64 = BitVec.ofNat 64 (parts.toNat - 1 + 1) := by
        rw [Nat.sub_add_cancel (by omega)]
        apply BitVec.eq_of_toNat_eq
        have := parts.isLt
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
      rw [hw]
      exact compare_loop WL' WR' (parts.toNat - 1) (by omega) (fun j hj hj' => by omega)
  rw [show run _ZN4llvm5APInt9tcCompareEPKmS2_j.step _ = _ from hrun]
  rfl

end Compare

section Add

variable {block' o' : Nat} {x : Nat → BitVec 64}

/-- The carry out of the words below `i`, as schoolbook addition has it. -/
def carryAt (w x : Nat → BitVec 64) (c : Nat) : Nat → Nat
  | 0 => c
  | i + 1 => ((w i).toNat + (x i).toNat + carryAt w x c i) / 2 ^ 64

/-- Word `i` of the sum, as schoolbook addition has it. -/
def sumWord (w x : Nat → BitVec 64) (c : Nat) (i : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((w i).toNat + (x i).toNat + carryAt w x c i)

/-- What the array holds once the first `i` words are done. -/
def doneBelow (w x : Nat → BitVec 64) (c i : Nat) : Nat → BitVec 64 := fun j => if j < i then sumWord w x c j else w j

theorem carryAt_le {c : Nat} (hc : c ≤ 1) (i : Nat) : carryAt w x c i ≤ 1 := by
  induction i with
  | zero => exact hc
  | succ i ih =>
    have h1 := (w i).isLt
    have h2 := (x i).isLt
    simp only [carryAt]
    omega

theorem sum_value {c : Nat} (n : Nat) :
    wordsValue (sumWord w x c) n + carryAt w x c n * 2 ^ (64 * n) = wordsValue w n + wordsValue x n + c := by
  induction n with
  | zero => simp [wordsValue, carryAt]
  | succ n ih =>
    have hp : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    simp only [wordsValue, carryAt]
    have hsum : (sumWord w x c n).toNat = ((w n).toNat + (x n).toNat + carryAt w x c n) % 2 ^ 64 := by
      simp [sumWord, BitVec.toNat_ofNat]
    rw [hsum, hp]
    have hdiv := Nat.div_add_mod ((w n).toNat + (x n).toNat + carryAt w x c n) (2 ^ 64)
    generalize ((w n).toNat + (x n).toNat + carryAt w x c n) / 2 ^ 64 = q at *
    generalize ((w n).toNat + (x n).toNat + carryAt w x c n) % 2 ^ 64 = r at *
    generalize 2 ^ (64 * n) = P at *
    grind

/-- One word with no carry in, as the code does it. -/
theorem add_word0 (a b : BitVec 64) :
    b + a = BitVec.ofNat 64 (a.toNat + b.toNat + 0) ∧ (b + a).ult a = decide (2 ^ 64 ≤ a.toNat + b.toNat + 0) := by
  have ha := a.isLt
  have hb := b.isLt
  have hs : (b + a).toNat = (a.toNat + b.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_add, Nat.add_comm]
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [hs, BitVec.toNat_ofNat, Nat.add_zero]
  · simp only [BitVec.ult, hs]
    rw [decide_eq_decide]
    omega

/-- One word with a carry in, as the code does it. -/
theorem add_word1 (a b : BitVec 64) :
    a + 1#64 + b = BitVec.ofNat 64 (a.toNat + b.toNat + 1) ∧
      BitVec.ule (a + 1#64 + b) a = decide (2 ^ 64 ≤ a.toNat + b.toNat + 1) := by
  have ha := a.isLt
  have hb := b.isLt
  have hs : (a + 1#64 + b).toNat = (a.toNat + b.toNat + 1) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]
    omega
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [hs, BitVec.toNat_ofNat]
  · simp only [BitVec.ule, hs]
    rw [decide_eq_decide]
    omega

abbrev addEffects : Effects := { other := .none, arg := .readwrite, inaccessible := .none, errno := .none }

abbrev writeTag (m : Mem) : Tag := { call := m.nextCall, nofree := true, expires := true, noAddress := true }

theorem doneBelow_succ {c i : Nat} :
    Words.setWord (doneBelow w x c i) i (sumWord w x c i) = doneBelow w x c (i + 1) := by
  funext j
  simp only [Words.setWord, doneBelow]
  by_cases h : j = i
  · subst h
    simp
  · have : j < i + 1 ↔ j < i := by omega
    simp [h, this]

theorem carry_bit {s : Nat} (hs : s < 2 ^ 65) :
    (BitVec.ofBool (decide (2 ^ 64 ≤ s))).setWidth 64 = BitVec.ofNat 64 (s / 2 ^ 64) := by
  by_cases h : 2 ^ 64 ≤ s
  · have e : s / 2 ^ 64 = 1 := by omega
    rw [e]
    simp [h]
  · have e : s / 2 ^ 64 = 0 := by omega
    rw [e]
    simp [h]

/-- The loop, from word `i`, with the memory it's written so far. -/
theorem add_loop {t t' : List Tag} {n : Nat} {c : Nat} {wtc : BitVec 64} (hc : c ≤ 1) (hw : wtc.toNat = n)
    (WD : Words m t block o n w) (VD : Writable m t block) (WR : Words m t' block' o' n x) (hb : block' ≠ block) :
    ∀ (r i : Nat), r = n - i → i < n →
      run _ZN4llvm5APInt5tcAddEPmPKmmj.step
        (.for_body (m.setWords block o n (doneBelow w x c i)) (some (BitVec.ofNat 64 i))
          (some (BitVec.ofNat 64 (carryAt w x c i))) (some (bufPtr t block o 0)) (some (bufPtr t' block' o' 0)) (some wtc)) =
      Outcome.ok (some (BitVec.ofNat 64 (carryAt w x c n)), m.setWords block o n (sumWord w x c)) := by
  have hn : n < 2 ^ 60 := by
    obtain ⟨a, ha, hsz, hmax, hd⟩ := WD.bytes.alloc
    omega
  intro r
  induction r with
  | zero =>
    intro i hr hi
    omega
  | succ r ih =>
    intro i hr hi
    have WD' := WD.set VD (doneBelow w x c i)
    have WR' := WR.set_other (block := block) (o := o) (n := n) hb (doneBelow w x c i)
    have h1 := WD'.index' hi
    have h2 := WD'.load hi
    have h3 := WR'.index' hi
    have h4 := WR'.load hi
    have hdone : doneBelow w x c i i = w i := by simp [doneBelow]
    rw [hdone] at h2
    have hcarry := carryAt_le (w := w) (x := x) hc i
    have hlimit : (w i).toNat + (x i).toNat + carryAt w x c i < 2 ^ 65 := by
      have := (w i).isLt
      have := (x i).isLt
      omega
    -- What's common to both ways of adding this word.
    have hend : ∀ (sum : BitVec 64) (cb : Bool), sum = sumWord w x c i →
        cb = decide (2 ^ 64 ≤ (w i).toNat + (x i).toNat + carryAt w x c i) →
        run _ZN4llvm5APInt5tcAddEPmPKmmj.step
          (.if_end (m.setWords block o n (doneBelow w x c i)) (some sum) (some (BitVec.ofBool cb)) (some (bufPtr t block o 0))
            (some (bufPtr t' block' o' 0)) (some wtc) (some (BitVec.ofNat 64 i)) (some (bufPtr t block o (8 * i)))) =
        Outcome.ok (some (BitVec.ofNat 64 (carryAt w x c n)), m.setWords block o n (sumWord w x c)) := by
      intro sum cb hsum hcb
      have hstore := WD.store VD hi (doneBelow w x c i) sum
      rw [hsum, doneBelow_succ] at hstore
      subst hsum hcb
      rw [run]
      llvm_simp [_ZN4llvm5APInt5tcAddEPmPKmmj.step, hstore, add_one (show i < 2 ^ 61 by omega), carry_bit hlimit]
      have hi1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
        simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      apply ite_cases <;> intro hexit
      · have hlast : i + 1 = n := by
          have e : BitVec.ofNat 64 (i + 1) = wtc := by simpa using hexit
          rw [← hw, ← e, hi1]
        llvm_step _ZN4llvm5APInt5tcAddEPmPKmmj.step
        have hsame : m.setWords block o n (doneBelow w x c (i + 1)) = m.setWords block o n (sumWord w x c) :=
          Words.setWords_congr (fun j hj => by
            have : j < i + 1 := by omega
            simp [doneBelow, this])
        rw [hsame, ← hlast]
        rfl
      · have hmore : i + 1 < n := by
          rcases Nat.lt_or_ge (i + 1) n with h | h
          · exact h
          · apply absurd _ hexit
            simp only [beq_iff_eq]
            apply BitVec.eq_of_toNat_eq
            rw [hw, hi1]
            omega
        exact ih (i + 1) (by omega) hmore
    rw [run]
    llvm_simp [_ZN4llvm5APInt5tcAddEPmPKmmj.step, h1, h2, h3, h4]
    rcases (show carryAt w x c i = 0 ∨ carryAt w x c i = 1 by omega) with h0 | h0
    · rw [h0]
      simp only [Val.icmp_ok, Bool.false_and, br_ofBool, jump, Outcome.ok, beq_self_eq_true, ite_true]
      rw [run]
      llvm_simp [_ZN4llvm5APInt5tcAddEPmPKmmj.step]
      obtain ⟨ha, hb'⟩ := add_word0 (w i) (x i)
      exact hend _ _ (by rw [ha, sumWord, h0]) (by rw [hb', h0])
    · rw [h0]
      have hz : (1#64 == 0#64) = false := rfl
      simp only [Val.icmp_ok, Bool.false_and, br_ofBool, jump, Outcome.ok, hz, Bool.false_eq_true, ite_false]
      rw [run]
      llvm_simp [_ZN4llvm5APInt5tcAddEPmPKmmj.step]
      obtain ⟨ha, hb'⟩ := add_word1 (w i) (x i)
      exact hend _ _ (by rw [ha, sumWord, h0]) (by rw [hb', h0])

/-- `llvm::APInt::tcAdd`, called from outside anything that promised something about memory, for arrays of `parts` words in
different allocations: `dst` gets the sum, and the carry comes back. Its source asserts `c <= 1`. -/
theorem tcAdd_correct {parts : BitVec 32} {c : BitVec 64} (hcalls : m.calls = []) (hc : c ≤ 1#64)
    (WD : Words m [] block o parts.toNat w) (WR : Words m [] block' o' parts.toNat x) (hb : block' ≠ block)
    (hrw : ∀ a, m.allocs block = some a → a.readonly = false ∧ a.stack = false) :
    ∃ (w' : Nat → BitVec 64) (carry : BitVec 64),
      _ZN4llvm5APInt5tcAddEPmPKmmj (some (bufPtr [] block o 0)) (some (bufPtr [] block' o' 0)) (some c) (some parts) m =
        Outcome.ok (some carry, (m.setWords block o parts.toNat w').afterCall) ∧
      wordsValue w' parts.toNat + carry.toNat * 2 ^ (64 * parts.toNat) =
        wordsValue w parts.toNat + wordsValue x parts.toNat + c.toNat := by
  have hcN : c.toNat ≤ 1 := hc
  refine ⟨sumWord w x c.toNat, BitVec.ofNat 64 (carryAt w x c.toNat parts.toNat), ?_, ?_⟩
  · have WD0 := WD.enter (e := addEffects) (T := writeTag m) (Or.inr rfl) rfl rfl rfl rfl
    have WR0 := WR.enter (e := addEffects) (T := readTag m) (Or.inr rfl) rfl rfl rfl rfl
    have VD : Writable (m.inCall addEffects) [writeTag m] block := by
      refine ⟨fun a ha => (hrw a ha).1, fun a ha off => ?_, fun c hc => ?_⟩
      · have hs := (hrw a ha).2
        simp [Mem.check, Mem.tagRule, Mem.isRunning, Mem.inCall, hcalls, Mem.callRule, Mem.callAccess, hs]
      · simp only [hcalls, List.mem_singleton] at hc
        subst hc
        rfl
    have hself : (m.inCall addEffects).setWords block o parts.toNat w = m.inCall addEffects := Words.setWords_self WD0
    have hrun : run _ZN4llvm5APInt5tcAddEPmPKmmj.step (.entry (m.inCall addEffects) (some (bufPtr [writeTag m] block o 0))
        (some (bufPtr [readTag m] block' o' 0)) (some c) (some parts)) =
        Outcome.ok (some (BitVec.ofNat 64 (carryAt w x c.toNat parts.toNat)),
          (m.inCall addEffects).setWords block o parts.toNat (sumWord w x c.toNat)) := by
      llvm_step _ZN4llvm5APInt5tcAddEPmPKmmj.step
      apply ite_cases <;> intro h0
      · have hp : parts = 0#32 := by simpa using h0
        subst hp
        llvm_step _ZN4llvm5APInt5tcAddEPmPKmmj.step
        have hempty : (m.inCall addEffects).setWords block o (0#32).toNat (sumWord w x c.toNat) = m.inCall addEffects :=
          (Words.setWords_congr (g := w) (fun j hj => by simp at hj)).trans hself
        rw [hempty]
        simp [carryAt]
      · have hpos : 0 < parts.toNat := by
          rcases Nat.eq_zero_or_pos parts.toNat with h | h
          · exact absurd (by simpa using BitVec.eq_of_toNat_eq (x := parts) (y := 0#32) (by simpa using h)) h0
          · exact h
        llvm_step _ZN4llvm5APInt5tcAddEPmPKmmj.step
        have hwtc : (parts.setWidth 64).toNat = parts.toNat := by
          simp only [BitVec.toNat_setWidth, Nat.reducePow]
          have := parts.isLt
          omega
        have hloop := add_loop (w := w) (x := x) (c := c.toNat) hcN hwtc WD0 VD WR0 hb _ 0 rfl hpos
        have hd0 : (m.inCall addEffects).setWords block o parts.toNat (doneBelow w x c.toNat 0) = m.inCall addEffects :=
          (Words.setWords_congr (g := w) (fun j hj => by simp [doneBelow])).trans hself
        have hc0 : BitVec.ofNat 64 (carryAt w x c.toNat 0) = c := by simp [carryAt]
        rw [hd0, hc0] at hloop
        exact hloop
    simp only [_ZN4llvm5APInt5tcAddEPmPKmmj, noundef_some, Mem.call, Mem.tag, Option.map]
    rw [show run _ZN4llvm5APInt5tcAddEPmPKmmj.step _ = _ from hrun, Words.setWords_inCall]
    rfl
  · have hle := carryAt_le (w := w) (x := x) hcN parts.toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact sum_value _

/-- A global of zeros is an array of words, for a call from outside anything that promised something about memory. -/
theorem words_of_zeros {M : Mem} {b : Nat} (ha : M.allocs b = some { size := 8, readonly := false, bytes := Mem.globalBytes #[0, 0, 0, 0, 0, 0, 0, 0] })
    (hcalls : M.calls = []) (hfit : (M.addr (bufPtr [] b 0 0)).toNat + 8 * 1 < 2 ^ 64)
    (hal : (M.addr (bufPtr [] b 0 0)).toNat % 8 = 0) :
    Words M [] b 0 1 (fun _ => 0#64) := by
  refine ⟨⟨⟨_, ha, by simp, by simp, fun i hi => ?_⟩, hfit, fun a _ off => ?_, fun a _ i _ off => ?_, by simp, by simp [hcalls]⟩, hal⟩
  · have hi' : i < 8 := by omega
    match i, hi' with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  · simp [Mem.check, hcalls]
  · simp [Mem.unwritten, hcalls]

/-- The hypotheses can all hold at once, on real memory: 0 + 0 with a carry in is 1, with no carry out. -/
theorem tcAdd_check_value :
    let m := (LlvmAPInt.initial.addGlobal 100 8 false #[0, 0, 0, 0, 0, 0, 0, 0]).addGlobal 101 8 false #[0, 0, 0, 0, 0, 0, 0, 0]
    ∃ (w' : Nat → BitVec 64) (carry : BitVec 64),
      _ZN4llvm5APInt5tcAddEPmPKmmj (some (bufPtr [] 100 0 0)) (some (bufPtr [] 101 0 0)) (some 1#64) (some 1#32) m =
        Outcome.ok (some carry, (m.setWords 100 0 1 w').afterCall) ∧
      wordsValue w' 1 + carry.toNat * 2 ^ 64 = 1 := by
  intro m
  have WD : Words m [] 100 0 1 (fun _ => 0#64) := words_of_zeros rfl rfl (by decide) (by decide)
  have WR : Words m [] 101 0 1 (fun _ => 0#64) := words_of_zeros rfl rfl (by decide) (by decide)
  have hrw : ∀ a, m.allocs 100 = some a → a.readonly = false ∧ a.stack = false := by
    intro a ha
    have : some { size := 8, readonly := false, bytes := Mem.globalBytes #[0, 0, 0, 0, 0, 0, 0, 0] } = some a := ha
    cases this
    exact ⟨rfl, rfl⟩
  obtain ⟨w', carry, h1, h2⟩ := tcAdd_correct (parts := 1#32) (c := 1#64) rfl (by decide) WD WR (by decide) hrw
  refine ⟨w', carry, h1, ?_⟩
  simpa [wordsValue] using h2

end Add

end Llvm.APInt
