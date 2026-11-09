import Fx.Src
import Fx.Tgt

/-! tests/replay_challenge.py's certificate for mul_nsw.ll under `default<O2>`: the pipeline turned `mul nsw i8 %x, 2`
into `shl nsw i8 %x, 1`, and `function-attrs` added `mustprogress` and `willreturn`, with a return `range` that rules
out 127. The model checks both promises: the target is undefined if it never returns, and it always does. Both are
poison exactly when `x * 2` overflows as a signed number, a doubled value is even and never 127, so the two functions
agree on every input, poison included, and the source never stops the model. -/

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
        run_ret Fx.Tgt.f.step (b := .bb1 (some x))
          (r := Val.range 128#8 127#8 (Val.shl (some x) (some 1#8) (nsw := true))) rfl, promised_ok]
      -- Decided on all 256 values of x.
      have same : Val.mul (some x) (some 2#8) (nsw := true) =
          Val.range 128#8 127#8 (Val.shl (some x) (some 1#8) (nsw := true)) := by
        revert x; decide
      rw [same]
  · intro x s
    cases x with
    | none => simp [Fx.Src.f, noundef, Outcome.ub]
    | some x =>
      simp only [Fx.Src.f, noundef]
      rw [run_ret Fx.Src.f.step (b := .bb1 (some x)) (r := Val.mul (some x) (some 2#8) (nsw := true)) rfl]
      simp [Outcome.ok]
