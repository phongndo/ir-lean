import CutCases

/-! A cut that isn't refined gives no theorem about its function. This is `CutCases.drop_nuw_cut`'s proof with the two
sides swapped, `add %x, 3` to `add nuw %x, 3`, which is wrong where the sum wraps. The cut lemma takes the cut's proof,
so it stops here, and `CutCases.drop_nuw_loop_converse` proves the loops don't refine that way either.
`tests/cut.sh` checks this fails, with an error of its own. -/

open IRLean drop_nuw_loop_ir

theorem add_nuw_cut : Refines cut_tgt cut_src := fun x => by
  rw [show cut_src x = Outcome.ok _ from run_ret _ rfl, show cut_tgt x = Outcome.ok _ from run_ret _ rfl,
    Refine.outcome_ok_ok]
  cases x with
  | none => exact Refine.val_none _
  | some x =>
    simp only [Val.add]
    split
    · exact Refine.val_none _
    · simp [Refine.val_some]
