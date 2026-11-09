import Opt
open IRLean

/-- `tgt` refines `src`: the rules are in docs/llvm-negative-verification.md. This is the proof that would check if
the model trusted `mustprogress`, so that `tgt` never finished at 0 either, as before SEM-07. The model checks the
promise, so `tgt` is undefined at 0, and the proof fails there. -/
theorem tgt_refines_src (x : Val 8) :
    (∃ r ∈ [IRLean.UB.branchOnPoison, IRLean.UB.switchOnPoison, IRLean.UB.assumeFailed, IRLean.UB.unreachable, IRLean.UB.divByZero, IRLean.UB.divByPoison, IRLean.UB.divOverflow, IRLean.UB.noundefPoison, IRLean.UB.badAccess, IRLean.UB.misaligned, IRLean.UB.poisonPointer, IRLean.UB.writeToConstant, IRLean.UB.overlappingCopy, IRLean.UB.badFree, IRLean.UB.forbiddenWrite, IRLean.UB.forbiddenAccess, IRLean.UB.expiredProvenance, IRLean.UB.forbiddenFree, IRLean.UB.noProgress, IRLean.UB.noReturn], Opt.src x = IRLean.Outcome.ub r) ∨ (Opt.src x = Option.none ∧ Opt.tgt x = Option.none) ∨ (Opt.src x = IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.tgt x) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok ()) ∨ (Opt.src x ≠ IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.src x) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok () ∧ Opt.tgt x = Opt.src x) := by
  cases x with
  | none =>
    left
    exact ⟨IRLean.UB.branchOnPoison, by simp, by simp [Opt.src, Opt.src.step, run, llvm]⟩
  | some a =>
    by_cases h : a = 0
    · subst h
      right; left
      constructor
      · rw [Opt.src, run_jump _ (show Opt.src.step (.entry (some 0)) = jump .loop_1 by simp [Opt.src.step, llvm])]
        exact run_forever (fun b : Opt.src.Block => b = .loop_1) (fun b hb => ⟨.loop_1, by subst hb; rfl, rfl⟩) rfl
      · rw [Opt.tgt, run_jump _ (show Opt.tgt.step (.entry (some 0)) = jump .loop_1 by simp [Opt.tgt.step, llvm])]
        exact run_forever (fun b : Opt.tgt.Block => b = .loop_1) (fun b hb => ⟨.loop_1, by subst hb; rfl, rfl⟩) rfl
    · right; right; right
      have h : a ≠ 0#8 := h
      have src : Opt.src (some a) = Outcome.ok (some a) := by
        rw [Opt.src, run_jump _ (show Opt.src.step (.entry (some a)) = jump (.done (some a)) by
          simp [Opt.src.step, llvm, h]), run_ret Opt.src.step (b := .done (some a)) (r := some a) rfl]
      have tgt : Opt.tgt (some a) = Outcome.ok (some a) := by
        rw [Opt.tgt, run_jump _ (show Opt.tgt.step (.entry (some a)) = jump (.done (some a)) by
          simp [Opt.tgt.step, llvm, h]), run_ret Opt.tgt.step (b := .done (some a)) (r := some a) rfl]
        try rfl
      rw [src, tgt]
      exact ⟨by simp [Outcome.ok], rfl, rfl⟩
