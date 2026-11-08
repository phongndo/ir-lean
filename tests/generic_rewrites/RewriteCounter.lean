import IRLean.Generic.Arith
import IRLean.Generic.Bitwise

/-! Counterexamples for the generic rewrites, run by `tests/generic_rewrites.sh`. Each drops one hypothesis or flag a
theorem in `IRLean.Generic` keeps, or asks for an equality where the theorem only gives a refinement, and shows one
concrete input where the result is false. So each hypothesis is needed, and each refinement isn't an equality. -/

namespace IRLean.Generic.Counter

open IRLean

/-- A source that's the value `x` only allows `x`, so a target that's poison or another value doesn't refine it. -/
theorem not_refines {w : Nat} {a b : Val w} (x : BitVec w) (ha : a = some x) (hb : b ≠ some x) : ¬ Refines a b := by
  subst ha; exact fun r => hb ((Refine.val_some x b).1 r)

/-! ### Width -/

/-- `shl_zero` needs `0 < w`: at width zero no shift amount is in range, so `shl x, 0` is poison. -/
example : Val.shl (some 0#0) (some 0#0) = none := by decide
example : Val.lshr (some 0#0) (some 0#0) = none := by decide
example : Val.ashr (some 0#0) (some 0#0) = none := by decide

/-- `udiv_one` needs `0 < w`: at width zero, `1` is `0`. -/
example : Val.udiv (some 0#0) (some 1#0) = Outcome.ub .divByZero := rfl

/-- `sdiv_one` needs `1 < w`: in `i1`, `1` is `-1`, and dividing `-1`, or poison, by it is undefined. -/
example : Val.sdiv (some 1#1) (some 1#1) = Outcome.ub .divOverflow := rfl
example : Val.sdiv (none : Val 1) (some 1#1) = Outcome.ub .divOverflow := rfl

/-- `mul_one` with `nsw` needs `w ≠ 1`: `mul nsw i1 1, 1` is poison, since `-1 * -1` doesn't fit. -/
example : Val.mul (some 1#1) (some 1#1) false true = none := by decide

/-- `add_self` needs `1 < w`, and isn't even a refinement without it: in `i1`, `add 0, 0` is `0` and `shl 0, 1` is
poison. `instcombine` turns `add i1` into `xor` before trying this. -/
example : ¬ Refines (Val.add (some 0#1) (some 0#1)) (Val.shl (some 0#1) (some 1#1)) :=
  not_refines 0#1 (by decide) (by decide)

/-- `mul_twoPow` needs `k < w`: `twoPow 8 8` is `0`, so `mul x, 0` is `0`, and `shl x, 8` is poison. -/
example : ¬ Refines (Val.mul (some 1#8) (some (BitVec.twoPow 8 8))) (Val.shl (some 1#8) (some 8#8)) :=
  not_refines 0#8 (by decide) (by decide)

/-! ### Flags -/

/-- Keeping `nsw` on `shl` at `k + 1 = w` is wrong, which is why `instcombine` drops it: `mul nsw i8 1, -128` is `-128`,
and `shl nsw i8 1, 7` is poison. -/
example : ¬ Refines (Val.mul (some 1#8) (some 128#8) false true) (Val.shl (some 1#8) (some 7#8) false true) :=
  not_refines 128#8 (by decide) (by decide)

/-- `add nuw nsw` to `or disjoint` is wrong: `1 + 1` is `2`, and `or disjoint 1, 1` is poison. -/
example : ¬ Refines (Val.add (some 1#8) (some 1#8) true true) (Val.or (some 1#8) (some 1#8) true) :=
  not_refines 2#8 (by decide) (by decide)

/-- De Morgan with `disjoint` on the new `or` is wrong: `not (and 0, 0)` is `-1`, and `or disjoint -1, -1` is
poison. -/
example : ¬ Refines (Val.xor (Val.and (some 0#8) (some 0#8)) (some 255#8))
    (Val.or (Val.xor (some 0#8) (some 255#8)) (Val.xor (some 0#8) (some 255#8)) true) :=
  not_refines 255#8 (by decide) (by decide)

/-- `lshr (shl x, s), s` to `x` needs `nuw`: shifting `255` left by one loses a bit. -/
example : ¬ Refines (Val.lshr (Val.shl (some 255#8) (some 1#8)) (some 1#8)) (some 255#8) :=
  not_refines 127#8 (by decide) (by decide)

/-- `ashr (shl x, s), s` to `x` needs `nsw`: shifting `64` left by one changes the sign. -/
example : ¬ Refines (Val.ashr (Val.shl (some 64#8) (some 1#8)) (some 1#8)) (some 64#8) :=
  not_refines 192#8 (by decide) (by decide)

/-- `shl (lshr x, s), s` to `x` needs `exact`: shifting `1` right by one loses a bit. -/
example : ¬ Refines (Val.shl (Val.lshr (some 1#8) (some 1#8)) (some 1#8)) (some 1#8) :=
  not_refines 0#8 (by decide) (by decide)

/-- `shl (ashr x, s), s` to `x` needs `exact` too. -/
example : ¬ Refines (Val.shl (Val.ashr (some 1#8) (some 1#8)) (some 1#8)) (some 1#8) :=
  not_refines 0#8 (by decide) (by decide)

/-! ### Refinements that aren't equalities

Each source is poison or undefined on some input where the target isn't. -/

example : Val.sub (none : Val 8) none ≠ some 0#8 := by decide
example : Val.mul (none : Val 8) (some 0#8) ≠ some 0#8 := by decide
example : Val.mul (some 1#1) (some 1#1) false true ≠ some 1#1 := by decide
example : Val.xor (none : Val 8) none ≠ some 0#8 := by decide
example : Val.and (none : Val 8) (some 0#8) ≠ some 0#8 := by decide
example : Val.or (none : Val 8) (some 255#8) ≠ some 255#8 := by decide
example : Val.or (some 1#8) (some 1#8) true ≠ some 1#8 := by decide
example : Val.or (some 1#8) (some 1#8) true ≠ Val.add (some 1#8) (some 1#8) true true := by decide
example : Val.xor (Val.or (some 1#8) (some 1#8) true) (some 255#8) ≠
    Val.and (Val.xor (some 1#8) (some 255#8)) (Val.xor (some 1#8) (some 255#8)) := by decide
example : Val.xor (Val.xor (some 0#8) none) none ≠ some 0#8 := by decide
example : Val.and (some 0#8) (Val.or (some 0#8) none) ≠ some 0#8 := by decide
example : Val.lshr (Val.shl (some 128#8) (some 1#8) true false) (some 1#8) ≠ some 128#8 := by decide
example : Val.urem (none : Val 8) (some 1#8) ≠ Outcome.ok (some 0#8) := by simp [Val.urem, Outcome.ok]
example : Val.srem (none : Val 8) (some 1#8) ≠ Outcome.ok (some 0#8) := by
  simp [Val.srem, Val.divOverflows, Outcome.ok]
example : Val.sdiv (some 1#1) (some 1#1) ≠ Outcome.ok (some 1#1) := by
  rw [show Val.sdiv (some 1#1) (some 1#1) = Outcome.ub .divOverflow from rfl]; simp [Outcome.ok, Outcome.ub]

end IRLean.Generic.Counter
