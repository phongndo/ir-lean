import IRLean.Generic.Arith
import IRLean.Generic.Bitwise

/-! Uses of the generic rewrites at the widths real code has, run by `tests/generic_rewrites.sh`. Each instance comes from
the theorem at that width, with no `decide` or `bv_decide` over the values, so none of it is a check of finitely many
inputs. -/

namespace IRLean.Generic.Test

open IRLean IRLean.Generic

/-! ### One rewrite, as a function of its operands

`instcombine` and `instsimplify` rewrite one instruction, and the function of its operands that a certificate states
for a binding is the shape these take. -/

/-- `add i8 %x, 0` to `%x`, the rewrite `tests/binding/AddZero.lean` proves for one IR file, here as a consequence of
`add_zero`. -/
example : Refines (fun x : Val 8 => Outcome.ok (Val.add x (some 0#8))) (fun x => Outcome.ok x) := fun x => by
  show Refine.le (Outcome.ok (Val.add x (some 0#8))) (Outcome.ok x)
  rw [add_zero]; exact (Refine.outcome_ok_ok _ _).2 (Refines.refl x)

/-- `mul nuw nsw i32 %x, 8` to `shl nuw nsw i32 %x, 3`: both flags stay, since `8` is positive. -/
example (x : Val 32) : Val.mul x (some 8#32) true true = Val.shl x (some 3#32) true true :=
  mul_twoPow x (k := 3) (by decide) (by decide) true true (.inr (by decide))

/-- `mul nsw i64 %x, -9223372036854775808` to `shl i64 %x, 63`: the constant is `2 ^ 63`, the signed minimum, so `nsw`
goes. -/
example (x : Val 64) :
    Refines (Val.mul x (some (BitVec.intMin 64)) false true) (Val.shl x (some 63#64) false false) := by
  have := mul_twoPow_refines x (k := 63) (c := BitVec.intMin 64) (by decide) (by decide) false true
  simpa using this

/-- `or disjoint i16 %x, %y` to `add nuw nsw i16 %x, %y`. -/
example : Refines (fun x y : Val 16 => Val.or x y true) (fun x y => Val.add x y true true) :=
  fun x y => or_disjoint_refines_add x y

/-- `sdiv exact i32 %x, 1` to `%x`. -/
example (x : Val 32) : Val.sdiv x (some 1#32) true = Outcome.ok x := sdiv_one x true (by decide)

/-- `lshr i64 (shl nuw i64 %x, %s), %s` to `%x`, for every shift amount, poison included. -/
example (x s : Val 64) : Refines (Val.lshr (Val.shl x s true false) s) x := lshr_shl_nuw_refines x s false false

/-- `lshr i8 (shl i8 %x, %s), %s` to `and i8 %x, (lshr i8 -1, %s)`. -/
example (x s : Val 8) : Val.lshr (Val.shl x s) s = Val.and x (Val.lshr (some 255#8) s) :=
  lshr_shl x s false

/-! ### Rewrites in context, composed with `IRLean.Refine`'s laws -/

/-- `add i32 %b, (sub i32 %a, %a)` to `%b`: `sub_self_refines` inside `add`, then `add_zero`. The first step is a
refinement, so the whole is too, not an equality: poison `%a` makes the source poison. -/
example (a b : Val 32) : Refines (Val.add b (Val.sub a a)) b := by
  have step : Refines (Val.add b (Val.sub a a)) (Val.add b (some 0#32)) :=
    Refine.val_map₂_mono (f := fun p q => Val.add p q) (fun _ => rfl) (fun p => by cases p <;> rfl)
      (Refines.refl b) (sub_self_refines a false false)
  rw [add_zero] at step
  exact step

/-- Two rewrites in a row on `i16`, joined by `Refines.trans`: `xor (xor (and %x, -1), %y), %y` to `and %x, -1`, a
refinement, then to `%x`, an equality. -/
example (x y : Val 16) : Refines (Val.xor (Val.xor (Val.and x (some (BitVec.allOnes 16))) y) y) x :=
  (xor_xor_cancel_refines (Val.and x (some (BitVec.allOnes 16))) y).trans
    (by rw [and_allOnes]; exact Refines.refl x)

/-- A run, as the emitter writes one: `udiv i32 %x, 1` then `mul nuw i32 _, 8`, to `shl nuw i32 %x, 3`. -/
def src (x : Val 32) : Outcome (Val 32) :=
  andThen (Val.udiv x (some 1#32)) fun v => Outcome.ok (Val.mul v (some 8#32) true false)

def tgt (x : Val 32) : Outcome (Val 32) := Outcome.ok (Val.shl x (some 3#32) true false)

example : Refines src tgt := fun x => by
  have h : src x = tgt x := by
    rw [src, tgt, udiv_one x false (by decide)]
    exact congrArg Outcome.ok (mul_twoPow x (c := 8#32) (k := 3) (by decide) (by decide) true false (.inl rfl))
  rw [h, tgt]
  exact (Refine.outcome_ok_ok _ _).2 (Refines.refl _)

end IRLean.Generic.Test
