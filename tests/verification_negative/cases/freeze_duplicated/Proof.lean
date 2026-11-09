import Opt
open IRLean

/-- `tgt` refines `src`: the rules are in docs/llvm-negative-verification.md. This claim is false, so the proof, choosing
the same for `src` as `tgt` did, fails at a poison `x`. -/
theorem tgt_refines_src (x : Val 8) (ct : IRLean.Choice) :
    ∃ (cs : IRLean.Choice), (∃ r ∈ [IRLean.UB.branchOnPoison, IRLean.UB.switchOnPoison, IRLean.UB.assumeFailed, IRLean.UB.unreachable, IRLean.UB.divByZero, IRLean.UB.divByPoison, IRLean.UB.divOverflow, IRLean.UB.noundefPoison, IRLean.UB.badAccess, IRLean.UB.misaligned, IRLean.UB.poisonPointer, IRLean.UB.writeToConstant, IRLean.UB.overlappingCopy, IRLean.UB.badFree, IRLean.UB.forbiddenWrite, IRLean.UB.forbiddenAccess, IRLean.UB.expiredProvenance, IRLean.UB.forbiddenFree, IRLean.UB.noProgress, IRLean.UB.noReturn, IRLean.UB.outsideCall], Opt.src x cs = IRLean.Outcome.ub r) ∨ (Opt.src x cs = Option.none ∧ Opt.tgt x ct = Option.none) ∨ (Opt.src x cs = IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.tgt x ct) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok ()) ∨ (Opt.src x cs ≠ IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.src x cs) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok () ∧ Opt.tgt x ct = Opt.src x cs) := by
  refine ⟨ct, ?_⟩
  cases x <;> simp [Opt.src, Opt.tgt, Opt.src.step, Opt.tgt.step, run, llvm]
