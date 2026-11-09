import Fx.Src
import Fx.Tgt

/-! tests/binding.py's certificate: `instcombine` dropped a `freeze` of a `noundef` argument. The source's run makes a
choice and the target's makes none, so the claim lifts the target with `Outcomes.det`: whatever the source chooses,
it allows the target, since poison is undefined there and `freeze` of a value is the value. -/

open IRLean

theorem Fx.cert : IRLean.Refines Fx.Src.f fun x => IRLean.Outcomes.det (Fx.Tgt.f x) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨default, ?_⟩
  cases x with
  | none => exact Refine.outcome_ub _ _
  | some x =>
    simp only [Fx.Src.f, Fx.Tgt.f, noundef]
    rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok]
    simp [Val.freeze, Refine.val_some]
