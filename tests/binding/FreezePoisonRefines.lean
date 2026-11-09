import Fx.Src
import Fx.Tgt

/-! tests/binding.py's certificate: `instcombine` replaced a frozen poison with 0. The source's run makes a choice and
the target's makes none, so the claim lifts the target with `Outcomes.det`, and the source chooses 0. -/

open IRLean

theorem Fx.cert : IRLean.Refines Fx.Src.f fun x => IRLean.Outcomes.det (Fx.Tgt.f x) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨fun _ => 0, ?_⟩
  cases x with
  | none => exact Refine.outcome_ub _ _
  | some x =>
    simp only [Fx.Src.f, Fx.Tgt.f, noundef]
    rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok]
    simp [Choice.pick, Val.freeze, Refine.val_some]
