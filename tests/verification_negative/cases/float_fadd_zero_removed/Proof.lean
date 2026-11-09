import Opt
open IRLean

/-- `tgt` refines `src`: the rules are in docs/llvm-negative-verification.md. This claim is false, so the proof, choosing
for `src` a NaN that keeps `x`, fails at `x` = -0.0, where `src` gives 0.0 however it chooses. -/
theorem tgt_refines_src (x : Val 32) :
    ∃ (cs : IRLean.Choice), (∃ r ∈ [IRLean.UB.branchOnPoison, IRLean.UB.switchOnPoison, IRLean.UB.assumeFailed, IRLean.UB.unreachable, IRLean.UB.divByZero, IRLean.UB.divByPoison, IRLean.UB.divOverflow, IRLean.UB.noundefPoison, IRLean.UB.badAccess, IRLean.UB.misaligned, IRLean.UB.poisonPointer, IRLean.UB.writeToConstant, IRLean.UB.overlappingCopy, IRLean.UB.badFree, IRLean.UB.forbiddenWrite, IRLean.UB.forbiddenAccess, IRLean.UB.expiredProvenance, IRLean.UB.forbiddenFree, IRLean.UB.noProgress, IRLean.UB.noReturn], Opt.src x cs = IRLean.Outcome.ub r) ∨ (Opt.src x cs = Option.none ∧ Opt.tgt x = Option.none) ∨ (Opt.src x cs = IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.tgt x) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok ()) ∨ (Opt.src x cs ≠ IRLean.Outcome.ok Option.none ∧ IRLean.andThen (Opt.src x cs) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok () ∧ Opt.tgt x = Opt.src x cs) := by
  refine ⟨fun _ => 6, ?_⟩
  cases x <;> simp [Opt.src, Opt.tgt, Opt.src.step, Opt.tgt.step, run, llvm]
