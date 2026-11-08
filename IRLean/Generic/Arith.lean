import IRLean.Refine
import IRLean.Generic.BitVec

/-! # Arithmetic rewrites at every width

Rewrites LLVM's `instsimplify` and `instcombine` make on integer arithmetic, proved for a variable width `w` and every
operand, poison included, with the flags each instruction carries. `docs/generic-rewrites.md` says where LLVM makes
each one, and what these theorems do and don't say about LLVM.

Each rewrite is one of two kinds:

- An equality, `src = tgt`: the two are the same function of their operands in IRLean's model.
- A refinement, `Refines src tgt` from `IRLean.Refine`: wherever `src` is a value, `tgt` is the same value, and where
  `src` is poison or undefined, `tgt` may be anything. These are the rewrites that aren't equalities, because `src` is
  poison or undefined somewhere `tgt` isn't.

A hypothesis on `w` or on a flag is there because the rewrite is wrong without it: `tests/generic_rewrites` has a
counterexample for each. -/

namespace IRLean.Generic

open IRLean

variable {w : Nat}

/-- A value refines itself, and anything refines poison. -/
private theorem refines_of_eq_or_none {a b : Val w} (h : a = none ∨ b = a) : Refines a b := (Refine.val_iff a b).2 h

/-! ### Identities: `x + 0`, `x - 0`, `x * 1` -/

/-- `add x, 0` is `x`, with any flags: adding zero overflows neither way. -/
theorem add_zero (a : Val w) (nuw nsw : Bool) : Val.add a (some 0#w) nuw nsw = a := by
  cases a with
  | none => rfl
  | some x =>
    have := x.isLt
    simp [Val.add, BitVec.uaddOverflow, BitVec.saddOverflow, BitVec.toInt_lt, BitVec.le_toInt]
    omega

/-- `sub x, 0` is `x`, with any flags. -/
theorem sub_zero (a : Val w) (nuw nsw : Bool) : Val.sub a (some 0#w) nuw nsw = a := by
  cases a with
  | none => rfl
  | some x => simp [Val.sub, BitVec.usubOverflow, BitVec.ssubOverflow, BitVec.toInt_lt, BitVec.le_toInt]

/-- `mul x, 1` is `x` without `nsw`, or above one bit. In `i1` the constant `1` is `-1` as a signed value, and
`mul nsw i1 1, 1` is poison: `-1 * -1` doesn't fit. -/
theorem mul_one (a : Val w) (nuw nsw : Bool) (h : nsw = false ∨ 1 < w) : Val.mul a (some 1#w) nuw nsw = a := by
  cases a with
  | none => rfl
  | some x =>
    have hu : x.umulOverflow 1#w = false := by
      simp only [BitVec.umulOverflow, decide_eq_false_iff_not, Nat.not_le]
      calc x.toNat * (1#w).toNat ≤ x.toNat * 1 :=
            Nat.mul_le_mul_left _ (by rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _)
        _ < 2 ^ w := by rw [Nat.mul_one]; exact x.isLt
    rcases h with h | h
    · subst h; simp [Val.mul, hu]
    · have hs : x.smulOverflow 1#w = false := by
        have := BitVec.toInt_lt (x := x)
        have := BitVec.le_toInt x
        simp only [BitVec.smulOverflow, BitVec.toInt_one h, Int.mul_one, Bool.or_eq_false_iff,
          decide_eq_false_iff_not]
        omega
      simp [Val.mul, hu, hs]

/-- `mul x, 1` refines `x` with any flags at any width: where `nsw` makes `i1` poison, anything is allowed. -/
theorem mul_one_refines (a : Val w) (nuw nsw : Bool) : Refines (Val.mul a (some 1#w) nuw nsw) a := by
  by_cases h : nsw = false ∨ 1 < w
  · rw [mul_one a nuw nsw h]; exact Refines.refl a
  · cases a with
    | none => exact Refine.val_none _
    | some x =>
      refine refines_of_eq_or_none ?_
      obtain ⟨rfl, hw⟩ : nsw = true ∧ w ≤ 1 := by simpa using h
      -- At one bit or none, `x * 1` is `x`, so a result that isn't poison is `x`.
      rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl <;> revert x <;> cases nuw <;> decide

/-! ### Operands that cancel: `x - x`, `x * 0` -/

/-- `sub x, x` refines `0`, with any flags. It isn't an equality: if `x` is poison, so is `x - x`. -/
theorem sub_self_refines (a : Val w) (nuw nsw : Bool) : Refines (Val.sub a a nuw nsw) (some 0#w) := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none (.inr ?_)
    have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide)
    simp [Val.sub, BitVec.usubOverflow, BitVec.ssubOverflow, this, Int.le_of_lt this]

/-- `mul x, 0` refines `0`, with any flags. Poison `x` makes it poison, so it isn't an equality. -/
theorem mul_zero_refines (a : Val w) (nuw nsw : Bool) : Refines (Val.mul a (some 0#w) nuw nsw) (some 0#w) := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none (.inr ?_)
    have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide)
    simp [Val.mul, BitVec.umulOverflow, BitVec.smulOverflow, this, Int.le_of_lt this]

/-! ### Strength reduction: `x + x` and `x * 2 ^ k` as shifts -/

/-- `add x, x` is `shl x, 1` above one bit, keeping both flags: doubling overflows exactly when shifting left by one
does. In `i1`, `shl x, 1` is poison, since the amount isn't less than the width. Both sides read one value `x`; the
model has no `undef`, which LLVM's `add undef, undef` could make two different values of. -/
theorem add_self (a : Val w) (nuw nsw : Bool) (hw : 1 < w) : Val.add a a nuw nsw = Val.shl a (some 1#w) nuw nsw := by
  cases a with
  | none => rfl
  | some x =>
    have t1 : (1#w).toNat = 1 := toNat_ofNat_of_lt hw
    have hok : Val.shiftOk (1#w) = true := by simp [shiftOk_iff, t1, hw]
    have hshl : x <<< 1 = x + x := by
      rw [← BitVec.mul_two, BitVec.shiftLeft_eq_mul_twoPow]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_twoPow, BitVec.toNat_ofNat]
    have hu : x.uaddOverflow x = !decide ((x + x) >>> 1 = x) := by
      have e := shl_lshr_eq_iff x (k := 1) (by omega)
      rw [hshl] at e
      rw [BitVec.uaddOverflow]
      by_cases h : x.toNat * 2 ^ 1 < 2 ^ w
      · simp only [e.2 h, decide_true, Bool.not_true, decide_eq_false_iff_not]; omega
      · simp only [mt e.1 h, decide_false, Bool.not_false, decide_eq_true_eq]; omega
    have hs : x.saddOverflow x = !decide ((x + x).sshiftRight 1 = x) := by
      have e := shl_sshr_eq_iff x (k := 1) (by omega)
      rw [hshl] at e
      rw [BitVec.saddOverflow]
      by_cases h : -2 ^ (w - 1) ≤ x.toInt * 2 ^ 1 ∧ x.toInt * 2 ^ 1 < 2 ^ (w - 1)
      · simp only [e.2 h, decide_true, Bool.not_true, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
      · simp only [mt e.1 h, decide_false, Bool.not_false, Bool.or_eq_true, decide_eq_true_eq]; omega
    simp only [Val.add, Val.shl, hok, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.sshiftRight_eq', t1, hshl,
      hu, hs, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases hA : (x + x) >>> 1 = x <;> by_cases hB : (x + x).sshiftRight 1 = x <;>
      cases nuw <;> cases nsw <;> simp_all

/-- `mul x, 2 ^ k` is `shl x, k`, keeping `nuw`, and keeping `nsw` while `2 ^ k` is positive as a signed value:
`k + 1 < w`. At `k + 1 = w` the constant is the signed minimum, and `instcombine` drops `nsw`, which
`mul_twoPow_refines` covers. -/
theorem mul_twoPow (a : Val w) {c : BitVec w} {k : Nat} (hc : c = BitVec.twoPow w k) (hk : k < w) (nuw nsw : Bool)
    (hs : nsw = false ∨ k + 1 < w) :
    Val.mul a (some c) nuw nsw = Val.shl a (some (BitVec.ofNat w k)) nuw nsw := by
  subst hc
  cases a with
  | none => rfl
  | some x =>
    have tk := toNat_ofNat_of_lt hk
    have hok : Val.shiftOk (BitVec.ofNat w k) = true := by simp [shiftOk_iff, tk, hk]
    simp only [Val.mul, Val.shl, hok, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.sshiftRight_eq', tk,
      BitVec.mul_twoPow_eq_shiftLeft, umulOverflow_twoPow x hk, Bool.not_true, Bool.false_eq_true, ite_false]
    rcases hs with hs | hs
    · subst hs
      by_cases hA : x <<< k >>> k = x <;> cases nuw <;> simp_all
    · rw [smulOverflow_twoPow x hs]
      by_cases hA : x <<< k >>> k = x <;> by_cases hB : (x <<< k).sshiftRight k = x <;>
        cases nuw <;> cases nsw <;> simp_all

/-- Dropping `nsw` from `mul` only removes poison. -/
private theorem mul_drop_nsw (a b : Val w) (nuw nsw : Bool) : Refines (Val.mul a b nuw nsw) (Val.mul a b nuw false) := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    cases b with
    | none => exact Refine.val_none _
    | some y =>
      refine refines_of_eq_or_none ?_
      simp only [Val.mul, Bool.false_and, Bool.or_false]
      cases nuw <;> cases nsw <;> simp <;> split <;> simp_all

/-- `mul x, 2 ^ k` refines `shl x, k` with the flags `instcombine` gives it: `nuw` if `mul` had it, and `nsw` if `mul`
had it and `k + 1 < w`. Keeping `nsw` at `k + 1 = w` would be wrong. -/
theorem mul_twoPow_refines (a : Val w) {c : BitVec w} {k : Nat} (hc : c = BitVec.twoPow w k) (hk : k < w)
    (nuw nsw : Bool) :
    Refines (Val.mul a (some c) nuw nsw) (Val.shl a (some (BitVec.ofNat w k)) nuw (nsw && decide (k + 1 < w))) := by
  by_cases h : k + 1 < w
  · rw [mul_twoPow a hc hk nuw nsw (.inr h)]
    simp only [h, decide_true, Bool.and_true]
    exact Refines.refl _
  · simp only [h, decide_false, Bool.and_false]
    rw [← mul_twoPow a hc hk nuw false (.inl rfl)]
    exact mul_drop_nsw a (some c) nuw nsw

/-! ### `or disjoint` as `add` -/

/-- `or disjoint x, y` refines `add nuw nsw x, y`: when no bit is set in both, adding carries nothing and overflows
neither way. Where they share a bit, `or disjoint` is poison. The other direction is wrong: `add nuw nsw 1, 1` is `2`,
and `or disjoint 1, 1` is poison. -/
theorem or_disjoint_refines_add (a b : Val w) : Refines (Val.or a b true) (Val.add a b true true) := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    cases b with
    | none => exact Refine.val_none _
    | some y =>
      refine refines_of_eq_or_none ?_
      by_cases h : x &&& y = 0#w
      · obtain ⟨hu, hs, hsum⟩ := add_of_and_eq_zero h
        exact .inr (by simp [Val.or, Val.add, h, hu, hs, hsum])
      · exact .inl (by simp [Val.or, h])

/-! ### Division by one -/

/-- `udiv x, 1` is `x`, with or without `exact`, at any width but zero, where `1` is `0` and dividing by it is
undefined. -/
theorem udiv_one (a : Val w) (exact : Bool) (hw : 0 < w) : Val.udiv a (some 1#w) exact = Outcome.ok a := by
  have h1 : (1#w == 0#w) = false := by
    simp [← BitVec.toNat_inj, BitVec.toNat_one hw]
  cases a with
  | none => simp [Val.udiv, h1]
  | some x => simp [Val.udiv, h1, BitVec.umod_one, BitVec.udiv_one]

/-- `urem x, 1` refines `0` at any width but zero. Poison `x` makes it poison, so it isn't an equality. -/
theorem urem_one_refines (a : Val w) (hw : 0 < w) : Refines (Val.urem a (some 1#w)) (Outcome.ok (some 0#w)) := by
  have h1 : (1#w == 0#w) = false := by
    simp [← BitVec.toNat_inj, BitVec.toNat_one hw]
  cases a with
  | none => simp only [Val.urem, h1, Bool.false_eq_true, ite_false]; exact (Refine.outcome_ok_ok _ _).2 trivial
  | some x =>
    simp only [Val.urem, h1, Bool.false_eq_true, ite_false, BitVec.umod_one]
    exact Refines.refl (α := Val w) (some 0#w) |> (Refine.outcome_ok_ok _ _).2

/-- `sdiv x, 1` is `x`, with or without `exact`, above one bit. In `i1` the constant `1` is `-1`, so `sdiv` by it is
undefined for the minimum, and for poison, which could be the minimum. -/
theorem sdiv_one (a : Val w) (exact : Bool) (hw : 1 < w) : Val.sdiv a (some 1#w) exact = Outcome.ok a := by
  have h1 : (1#w == 0#w) = false := by
    simp [← BitVec.toNat_inj, BitVec.toNat_one (Nat.lt_of_succ_lt hw)]
  have hm : (1#w == BitVec.allOnes w) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_one (Nat.lt_of_succ_lt hw),
      BitVec.toNat_allOnes]
    have := Nat.one_lt_two_pow (n := w) (by omega)
    have : 2 ≤ 2 ^ w - 1 := by
      have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.succ_le_of_lt hw)
      omega
    omega
  have ho : ∀ x : BitVec w, x.sdivOverflow 1#w = false := fun x => by
    simp only [BitVec.sdivOverflow_eq, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact .inr (by simpa using hm)
  cases a with
  | none => simp [Val.sdiv, Val.divOverflows, h1, hm]
  | some x => simp [Val.sdiv, Val.divOverflows, h1, ho, BitVec.srem_one, BitVec.sdiv_one]

/-- `sdiv x, 1` refines `x` at every width but zero, `i1` included: there, it's undefined wherever it isn't `x`. -/
theorem sdiv_one_refines (a : Val w) (exact : Bool) (hw : 0 < w) :
    Refines (Val.sdiv a (some 1#w) exact) (Outcome.ok a) := by
  by_cases h : 1 < w
  · rw [sdiv_one a exact h]; exact (Refine.outcome_ok_ok _ _).2 (Refines.refl a)
  · obtain rfl : w = 1 := by omega
    -- In `i1`, dividing by `1`, which is `-1`, is undefined for poison and `-1`, and gives `0` for `0`.
    rcases a with _ | x
    · exact Refine.outcome_ub _ _
    · rcases (by decide : ∀ x : BitVec 1, x = 0#1 ∨ x = 1#1) x with rfl | rfl
      · rw [show Val.sdiv (some 0#1) (some 1#1) exact = Outcome.ok (some 0#1) by cases exact <;> rfl]
        exact (Refine.outcome_ok_ok _ _).2 (Refines.refl (α := Val 1) _)
      · exact Refine.outcome_ub _ _

/-- `srem x, 1` refines `0` at every width but zero. Above one bit it's `0` for a value, and poison for poison; in `i1`
it's also undefined for the minimum and for poison. -/
theorem srem_one_refines (a : Val w) (hw : 0 < w) : Refines (Val.srem a (some 1#w)) (Outcome.ok (some 0#w)) := by
  by_cases h : 1 < w
  · have h1 : (1#w == 0#w) = false := by
      simp [← BitVec.toNat_inj, BitVec.toNat_one hw]
    have hm : (1#w == BitVec.allOnes w) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_one hw, BitVec.toNat_allOnes]
      have : 2 ≤ 2 ^ w - 1 := by
        have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.succ_le_of_lt h)
        omega
      omega
    cases a with
    | none =>
      simp only [Val.srem, Val.divOverflows, h1, hm, Bool.false_eq_true, ite_false]
      exact (Refine.outcome_ok_ok _ _).2 trivial
    | some x =>
      have ho : x.sdivOverflow 1#w = false := by
        simp only [BitVec.sdivOverflow_eq, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        exact .inr (by simpa using hm)
      simp only [Val.srem, Val.divOverflows, h1, ho, Bool.false_eq_true, ite_false, BitVec.srem_one]
      exact (Refine.outcome_ok_ok _ _).2 (Refines.refl (α := Val w) _)
  · obtain rfl : w = 1 := by omega
    rcases a with _ | x
    · exact Refine.outcome_ub _ _
    · rcases (by decide : ∀ x : BitVec 1, x = 0#1 ∨ x = 1#1) x with rfl | rfl
      · rw [show Val.srem (some 0#1) (some 1#1) = Outcome.ok (some 0#1) by rfl]
        exact (Refine.outcome_ok_ok _ _).2 (Refines.refl (α := Val 1) _)
      · exact Refine.outcome_ub _ _

end IRLean.Generic
