import Fx.Src
import Fx.Tgt

/-! tests/replay_challenge.py's certificate for mul_nsw.ll: `instcombine` turned `mul nsw i8 %x, 2` into
`shl nsw i8 %x, 1`. Both are poison exactly when `x * 2` overflows as a signed number, so the two functions ir-lean
generated agree on every input, poison included, and the source never stops the model. -/

open IRLean

theorem Fx.cert : Fx.Src.f = Fx.Tgt.f ∧
    ∀ (x : IRLean.Val 8) (s : IRLean.ModelStop), Fx.Src.f x ≠ some (.error (.model s)) := by
  refine ⟨?_, ?_⟩
  · funext x
    cases x with
    | none => rfl
    | some x =>
      simp only [Fx.Src.f, Fx.Tgt.f, noundef]
      rw [run_ret Fx.Src.f.step (b := .bb1 (some x)) (r := Val.mul (some x) (some 2#8) (nsw := true)) rfl,
        run_ret Fx.Tgt.f.step (b := .bb1 (some x)) (r := Val.shl (some x) (some 1#8) (nsw := true)) rfl]
      -- The flags agree, and so do the values: decided on all 256 values of x.
      have poison : x.smulOverflow 2#8 = ((x <<< 1#8).sshiftRight' 1#8 != x) := by revert x; decide
      have value : x * 2#8 = x <<< 1#8 := by revert x; decide
      simp [Val.mul, Val.shl, Val.shiftOk, poison, value]
  · intro x s
    cases x with
    | none => simp [Fx.Src.f, noundef, Outcome.ub]
    | some x =>
      simp only [Fx.Src.f, noundef]
      rw [run_ret Fx.Src.f.step (b := .bb1 (some x)) (r := Val.mul (some x) (some 2#8) (nsw := true)) rfl]
      simp [Outcome.ok]
