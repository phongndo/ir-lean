import Opt
open IRLean

/-- `tgt` refines `src`: the rules are in docs/llvm-negative-verification.md. `src` makes a choice, and any one does. -/
theorem tgt_refines_src (x : Val 8) :
    ∃ (cs : IRLean.Choice), (∃ r ∈ [IRLean.UB.branchOnPoison, IRLean.UB.switchOnPoison, IRLean.UB.assumeFailed, IRLean.UB.unreachable, IRLean.UB.divByZero, IRLean.UB.divByPoison, IRLean.UB.divOverflow, IRLean.UB.noundefPoison, IRLean.UB.badAccess, IRLean.UB.misaligned, IRLean.UB.poisonPointer, IRLean.UB.writeToConstant, IRLean.UB.overlappingCopy, IRLean.UB.badFree, IRLean.UB.forbiddenWrite, IRLean.UB.forbiddenAccess, IRLean.UB.expiredProvenance, IRLean.UB.forbiddenFree], Opt.src x cs = IRLean.Outcome.ub r) ∨ (Opt.src x cs = Option.none ∧ Opt.tgt x = Option.none) ∨ (Opt.src x cs = IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.tgt x) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok ()) ∨ (Opt.src x cs ≠ IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.src x cs) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok () ∧ Opt.tgt x = Opt.src x cs) := by
  refine ⟨default, ?_⟩
  cases x <;> simp [Opt.src, Opt.tgt, Opt.src.step, Opt.tgt.step, run, llvm]
