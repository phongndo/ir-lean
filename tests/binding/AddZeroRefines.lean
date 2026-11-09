import Fx.Src
import Fx.Tgt

/-! tests/binding.py's refinement certificate: `instcombine` turned `add i8 %x, 0` into `%x`, and the function ir-lean
generated after refines the one before, on every input, poison included, as `IRLean.Refines` says. -/

open IRLean

theorem Fx.cert : IRLean.Refines Fx.Src.f Fx.Tgt.f := by
  intro x
  cases x with
  | none =>
    simp only [Fx.Src.f, noundef]
    exact Refine.outcome_ub _ _
  | some x =>
    simp only [Fx.Src.f, Fx.Tgt.f, noundef]
    rw [run_ret Fx.Src.f.step (b := .bb1 (some x)) (r := Val.add (some x) (some 0#8)) rfl,
      run_ret Fx.Tgt.f.step (b := .bb1 (some x)) (r := some x) rfl,
      show Val.add (some x) (some 0#8) = some x by simp [Val.add]]
    exact (Refine.outcome_ok_ok _ _).2 (Refine.refl_val _)
