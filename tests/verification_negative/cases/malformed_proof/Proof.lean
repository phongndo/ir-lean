import Opt
open IRLean

/-- `tgt` refines `src`: the rules are in docs/llvm-negative-verification.md. -/
theorem tgt_refines_src (x : Val 8) :
    (∃ r ∈ [IRLean.UB.branchOnPoison, IRLean.UB.switchOnPoison, IRLean.UB.assumeFailed, IRLean.UB.unreachable, IRLean.UB.divByZero, IRLean.UB.divByPoison, IRLean.UB.divOverflow, IRLean.UB.noundefPoison, IRLean.UB.badAccess, IRLean.UB.misaligned, IRLean.UB.poisonPointer, IRLean.UB.writeToConstant, IRLean.UB.overlappingCopy, IRLean.UB.badFree, IRLean.UB.forbiddenWrite, IRLean.UB.forbiddenAccess, IRLean.UB.expiredProvenance, IRLean.UB.forbiddenFree, IRLean.UB.noProgress, IRLean.UB.noReturn, IRLean.UB.outside], Opt.src x = IRLean.Outcome.ub r) ∨ (Opt.src x = Option.none ∧ Opt.tgt x = Option.none) ∨ (Opt.src x = IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.tgt x) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok ()) ∨ (Opt.src x ≠ IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.src x) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok () ∧ Opt.tgt x = Opt.src x) := by
  cases x <;> simp [Opt.src,
