import Opt
open IRLean

/-- `tgt` refines `src`: the rules are in docs/llvm-negative-verification.md. -/
theorem tgt_refines_src (x : BitVec 8) (h : x < 128#8) :
    (∃ r ∈ [IRLean.UB.branchOnPoison, IRLean.UB.switchOnPoison, IRLean.UB.assumeFailed, IRLean.UB.unreachable, IRLean.UB.divByZero, IRLean.UB.divByPoison, IRLean.UB.divOverflow, IRLean.UB.noundefPoison, IRLean.UB.badAccess, IRLean.UB.misaligned, IRLean.UB.poisonPointer, IRLean.UB.writeToConstant, IRLean.UB.overlappingCopy, IRLean.UB.badFree, IRLean.UB.forbiddenWrite, IRLean.UB.forbiddenAccess, IRLean.UB.expiredProvenance, IRLean.UB.forbiddenFree, IRLean.UB.noProgress, IRLean.UB.noReturn, IRLean.UB.outsideCall], Opt.src (some x) = IRLean.Outcome.ub r) ∨ (Opt.src (some x) = Option.none ∧ Opt.tgt (some x) = Option.none) ∨ (Opt.src (some x) = IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.tgt (some x)) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok ()) ∨ (Opt.src (some x) ≠ IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.src (some x)) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok () ∧ Opt.tgt (some x) = Opt.src (some x)) := by
  simp [Opt.src, Opt.tgt, Opt.src.step, Opt.tgt.step, run, llvm]
  bv_decide
