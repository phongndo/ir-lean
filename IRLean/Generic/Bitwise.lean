import IRLean.Refine
import IRLean.Generic.BitVec

/-! # Bitwise and shift rewrites at every width

Rewrites LLVM's `instsimplify` and `instcombine` make on `and`, `or`, `xor` and shifts, proved for a variable width
`w` and every operand, poison included, with each instruction's flags. As in `IRLean.Generic.Arith`, each is an
equality, or a refinement where the source is poison somewhere the target isn't. `not x` is `xor x, -1`, as LLVM
writes it. -/

namespace IRLean.Generic

open IRLean

variable {w : Nat}

private theorem refines_of_eq_or_none {a b : Val w} (h : a = none ∨ b = a) : Refines a b := (Refine.val_iff a b).2 h

/-! ### A value with itself -/

/-- `and x, x` is `x`. -/
theorem and_self (a : Val w) : Val.and a a = a := by
  cases a <;> simp [Val.and, Val.map₂]

/-- `or x, x` is `x`, without `disjoint`. -/
theorem or_self (a : Val w) : Val.or a a = a := by
  cases a <;> simp [Val.or]

/-- `or disjoint x, x` refines `x`: it's poison unless `x` is `0`. So it isn't an equality. -/
theorem or_self_disjoint_refines (a : Val w) (disjoint : Bool) : Refines (Val.or a a disjoint) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none ?_
    cases disjoint <;> by_cases h : x = 0#w <;> simp [Val.or, h]

/-- `xor x, x` refines `0`. Poison `x` makes it poison, so it isn't an equality. -/
theorem xor_self_refines (a : Val w) : Refines (Val.xor a a) (some 0#w) := by
  cases a with
  | none => exact Refine.val_none _
  | some x => exact refines_of_eq_or_none (.inr (by simp [Val.xor, Val.map₂]))

/-! ### Constants that change nothing, and constants that decide the result -/

/-- `and x, -1` is `x`. -/
theorem and_allOnes (a : Val w) : Val.and a (some (BitVec.allOnes w)) = a := by
  cases a <;> simp [Val.and, Val.map₂]

/-- `or x, 0` is `x`, even with `disjoint`: no bit is set in both. -/
theorem or_zero (a : Val w) (disjoint : Bool) : Val.or a (some 0#w) disjoint = a := by
  cases a <;> simp [Val.or]

/-- `xor x, 0` is `x`. -/
theorem xor_zero (a : Val w) : Val.xor a (some 0#w) = a := by
  cases a <;> simp [Val.xor, Val.map₂]

/-- `and x, 0` refines `0`. Poison `x` makes it poison, so it isn't an equality. -/
theorem and_zero_refines (a : Val w) : Refines (Val.and a (some 0#w)) (some 0#w) := by
  cases a with
  | none => exact Refine.val_none _
  | some x => exact refines_of_eq_or_none (.inr (by simp [Val.and, Val.map₂]))

/-- `or x, -1` refines `-1`, with or without `disjoint`. Poison `x` makes it poison, and so does `disjoint` unless `x`
is `0`. -/
theorem or_allOnes_refines (a : Val w) (disjoint : Bool) :
    Refines (Val.or a (some (BitVec.allOnes w)) disjoint) (some (BitVec.allOnes w)) := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none ?_
    cases disjoint <;> by_cases h : x = 0#w <;> simp [Val.or, h]

/-! ### De Morgan, cancellation and absorption -/

/-- `not (and x, y)` is `or (not x), (not y)`: poison if either operand is. -/
theorem not_and (a b : Val w) :
    Val.xor (Val.and a b) (some (BitVec.allOnes w)) =
      Val.or (Val.xor a (some (BitVec.allOnes w))) (Val.xor b (some (BitVec.allOnes w))) := by
  cases a <;> cases b <;> simp [Val.and, Val.or, Val.xor, Val.map₂, BitVec.not_and]

/-- `not (or x, y)` is `and (not x), (not y)`, without `disjoint`. -/
theorem not_or (a b : Val w) :
    Val.xor (Val.or a b) (some (BitVec.allOnes w)) =
      Val.and (Val.xor a (some (BitVec.allOnes w))) (Val.xor b (some (BitVec.allOnes w))) := by
  cases a <;> cases b <;> simp [Val.and, Val.or, Val.xor, Val.map₂, BitVec.not_or]

/-- With `disjoint`, `not (or disjoint x, y)` refines `and (not x), (not y)`: the source is also poison where `x` and
`y` share a bit. -/
theorem not_or_refines (a b : Val w) (disjoint : Bool) :
    Refines (Val.xor (Val.or a b disjoint) (some (BitVec.allOnes w)))
      (Val.and (Val.xor a (some (BitVec.allOnes w))) (Val.xor b (some (BitVec.allOnes w)))) := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    cases b with
    | none => exact Refine.val_none _
    | some y =>
      refine refines_of_eq_or_none ?_
      cases disjoint <;> by_cases h : x &&& y = 0#w <;> simp [Val.and, Val.or, Val.xor, Val.map₂, BitVec.not_or, h]

/-- `xor (xor x, y), y` refines `x`. If `y` is poison, the source is poison and `x` may not be, so it isn't an
equality. -/
theorem xor_xor_cancel_refines (a b : Val w) : Refines (Val.xor (Val.xor a b) b) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    cases b with
    | none => exact Refine.val_none _
    | some y => exact refines_of_eq_or_none (.inr (by simp [Val.xor, Val.map₂, BitVec.xor_assoc]))

/-- `and x, (or x, y)` refines `x`, with or without `disjoint`. If `y` is poison, the source is poison and `x` may
not be, so it isn't an equality. -/
theorem and_or_absorb_refines (a b : Val w) (disjoint : Bool) : Refines (Val.and a (Val.or a b disjoint)) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    cases b with
    | none => exact Refine.val_none _
    | some y =>
      refine refines_of_eq_or_none ?_
      have : x &&& (x ||| y) = x := by ext i hi; simp; cases x[i] <;> simp
      cases disjoint <;> by_cases h : x &&& y = 0#w <;> simp [Val.and, Val.or, Val.map₂, h, this]

/-! ### Shifts by zero -/

private theorem shiftOk_zero (hw : 0 < w) : Val.shiftOk (0#w) = true := by
  simp [shiftOk_iff, hw]

/-- `shl x, 0` is `x`, with any flags, at any width but zero, where no shift amount is in range. -/
theorem shl_zero (a : Val w) (nuw nsw : Bool) (hw : 0 < w) : Val.shl a (some 0#w) nuw nsw = a := by
  cases a <;> simp [Val.shl, shiftOk_zero hw, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.sshiftRight_eq']

/-- `lshr x, 0` is `x`, with or without `exact`, at any width but zero. -/
theorem lshr_zero (a : Val w) (exact : Bool) (hw : 0 < w) : Val.lshr a (some 0#w) exact = a := by
  cases a <;> simp [Val.lshr, shiftOk_zero hw, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']

/-- `ashr x, 0` is `x`, with or without `exact`, at any width but zero. -/
theorem ashr_zero (a : Val w) (exact : Bool) (hw : 0 < w) : Val.ashr a (some 0#w) exact = a := by
  cases a <;> simp [Val.ashr, shiftOk_zero hw, BitVec.shiftLeft_eq', BitVec.sshiftRight_eq']

/-! ### Shifting there and back

The shift amount `s` is any value, poison included, and the same one both times. -/

/-- `lshr (shl x, s), s` is `and x, (lshr -1, s)`, with or without `exact` on `lshr`: shifting a value left leaves
zeros for `lshr exact` to drop. Both are poison where `s` is poison or out of range. -/
theorem lshr_shl (a s : Val w) (exact : Bool) :
    Val.lshr (Val.shl a s) s exact = Val.and a (Val.lshr (some (BitVec.allOnes w)) s) := by
  cases s with
  | none => cases a <;> rfl
  | some y =>
    cases a with
    | none => simp [Val.shl, Val.lshr, Val.and, Val.map₂]
    | some x =>
      by_cases hy : Val.shiftOk y = true
      · simp [Val.shl, Val.lshr, Val.and, Val.map₂, hy, shl_lshr_shl]
        rw [shl_lshr_eq_and]
      · simp [Val.shl, Val.lshr, Val.and, Val.map₂, hy]

/-- `shl (lshr x, s), s` is `and x, (shl -1, s)`, without flags on either. -/
theorem shl_lshr (a s : Val w) : Val.shl (Val.lshr a s) s = Val.and a (Val.shl (some (BitVec.allOnes w)) s) := by
  cases s with
  | none => cases a <;> rfl
  | some y =>
    cases a with
    | none => simp [Val.shl, Val.lshr, Val.and, Val.map₂]
    | some x =>
      by_cases hy : Val.shiftOk y = true
      · simp [Val.shl, Val.lshr, Val.and, Val.map₂, hy, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
          BitVec.shiftLeft_ushiftRight]
      · simp [Val.shl, Val.lshr, Val.and, Val.map₂, hy]

/-- `lshr (shl nuw x, s), s` refines `x`, whatever the other flags: `nuw` says no set bit was shifted out. -/
theorem lshr_shl_nuw_refines (a s : Val w) (nsw exact : Bool) : Refines (Val.lshr (Val.shl a s true nsw) s exact) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    cases s with
    | none => exact Refine.val_none _
    | some y =>
      refine refines_of_eq_or_none ?_
      by_cases hy : Val.shiftOk y = true
      · by_cases hu : x <<< y.toNat >>> y.toNat = x <;>
          by_cases hs : (x <<< y.toNat).sshiftRight y.toNat = x <;> cases nsw <;> cases exact <;>
          simp_all [Val.shl, Val.lshr]
      · simp_all [Val.shl, Val.lshr]

/-- `ashr (shl nsw x, s), s` refines `x`, whatever the other flags: `nsw` says shifting back arithmetically gives
`x`. -/
theorem ashr_shl_nsw_refines (a s : Val w) (nuw exact : Bool) : Refines (Val.ashr (Val.shl a s nuw true) s exact) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    cases s with
    | none => exact Refine.val_none _
    | some y =>
      refine refines_of_eq_or_none ?_
      by_cases hy : Val.shiftOk y = true
      · by_cases hu : x <<< y.toNat >>> y.toNat = x <;>
          by_cases hs : (x <<< y.toNat).sshiftRight y.toNat = x <;> cases nuw <;> cases exact <;>
          simp_all [Val.shl, Val.ashr]
      · simp_all [Val.shl, Val.ashr]

/-- `shl (lshr exact x, s), s` refines `x`, whatever the flags on `shl`: `exact` says no set bit was shifted out.
`nuw` or `nsw` on `shl` can still make it poison, which only makes the source poison more often. -/
theorem shl_lshr_exact_refines (a s : Val w) (nuw nsw : Bool) : Refines (Val.shl (Val.lshr a s true) s nuw nsw) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    cases s with
    | none => exact Refine.val_none _
    | some y =>
      refine refines_of_eq_or_none ?_
      by_cases hy : Val.shiftOk y = true
      · by_cases he : x >>> y.toNat <<< y.toNat = x <;>
          by_cases hq : x.sshiftRight y.toNat = x >>> y.toNat <;> cases nuw <;> cases nsw <;>
          simp_all [Val.shl, Val.lshr]
      · simp_all [Val.shl, Val.lshr]

/-- `shl (ashr exact x, s), s` refines `x`, whatever the flags on `shl`. -/
theorem shl_ashr_exact_refines (a s : Val w) (nuw nsw : Bool) : Refines (Val.shl (Val.ashr a s true) s nuw nsw) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    cases s with
    | none => exact Refine.val_none _
    | some y =>
      refine refines_of_eq_or_none ?_
      by_cases hy : Val.shiftOk y = true
      · by_cases he : x.sshiftRight y.toNat <<< y.toNat = x <;>
          by_cases hq : x >>> y.toNat = x.sshiftRight y.toNat <;> cases nuw <;> cases nsw <;>
          simp_all [Val.shl, Val.ashr]
      · simp_all [Val.shl, Val.ashr]

end IRLean.Generic
