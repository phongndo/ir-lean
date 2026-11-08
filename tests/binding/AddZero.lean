import Fx.Src
import Fx.Tgt

/-! tests/binding.py's certificate: `instcombine` turned `add i8 %x, 0` into `%x`, the two functions ir-lean
generated agree on every input, poison included, and the source never stops the model, so the model knows what LLVM
does on every input. -/

open IRLean

theorem Fx.cert : Fx.Src.f = Fx.Tgt.f ∧
    ∀ (x : IRLean.Val 8) (s : IRLean.ModelStop), Fx.Src.f x ≠ some (.error (.model s)) := by
  refine ⟨?_, ?_⟩
  · funext x
    rw [Fx.Src.f, Fx.Tgt.f, run_ret Fx.Src.f.step (b := .bb1 x) (r := Val.add x (some 0#8)) rfl,
      run_ret Fx.Tgt.f.step (b := .bb1 x) (r := x) rfl]
    cases x <;> simp [Val.add]
  · intro x s
    rw [Fx.Src.f, run_ret Fx.Src.f.step (b := .bb1 x) (r := Val.add x (some 0#8)) rfl]
    simp [Outcome.ok]
