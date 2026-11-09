import freeze_duplicated_wrong_ir

/-! A false claim, which has to fail to check with an error that isn't a resource limit: that one `freeze` used twice
may become two, choosing the same on both sides, as a proof would if each `freeze` read the same place. -/

open IRLean

theorem freeze_duplicated_right : Refines freeze_duplicated_wrong_ir.src freeze_duplicated_wrong_ir.tgt := by
  intro x
  refine Refine.outcomes_of_same fun c => ?_
  simp only [freeze_duplicated_wrong_ir.src, freeze_duplicated_wrong_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok]
  cases x <;> simp [Val.freeze, Val.sub, Refine.val_some]
