import pure_duplicated_wrong_ir

/-! A proof that duplicating a call that accesses no memory refines, which `tests/calls.sh` requires to fail with an error
of its own. Choosing the same on both sides is how most proofs go, and here the target's two calls pick apart. -/

open IRLean

theorem pure_duplicated_refines : Refines pure_duplicated_wrong_ir.src pure_duplicated_wrong_ir.tgt := by
  intro x w t
  refine Refine.outcomes_of_same fun c => ?_
  simp only [pure_duplicated_wrong_ir.src, pure_duplicated_wrong_ir.tgt]
  rw [run.eq_1, run.eq_1]
  simp only [pure_duplicated_wrong_ir.src.step, pure_duplicated_wrong_ir.tgt.step, World.callPure, World.quiet,
    Exit.bind]
  cases w.pure ⟨"f", [Lanes.ofVal x]⟩ (c.pick 1) <;> cases w.pure ⟨"f", [Lanes.ofVal x]⟩ (c.pick 2) <;>
    simp only [andThen, ret, Outcome.ok, Outcome.ub] <;>
    first | trivial | exact ⟨_, rfl, Refine.Reflexive.refl _⟩
