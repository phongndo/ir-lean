import Fx.Src
import Fx.Tgt

/-! tests/binding.py's certificate: `instcombine` turned `add i8 %x, 0` into `%x`, and the two functions ir-lean
generated agree on every input, poison included. -/

open IRLean

theorem Fx.cert : Fx.Src.f = Fx.Tgt.f := by
  funext x
  rw [Fx.Src.f, Fx.Tgt.f, run_ret Fx.Src.f.step (b := .bb1 x) (r := Val.add x (some 0#8)) rfl,
    run_ret Fx.Tgt.f.step (b := .bb1 x) (r := x) rfl]
  cases x <;> simp [Val.add]
