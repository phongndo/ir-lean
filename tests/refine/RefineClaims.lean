import Lean
import RefineCases

/-! What has a `Refines` claim, checked as `tools/binding.py` checks it: memory has no instance, and the claim
`tools/binding_check.lean` builds is the statement a certificate elaborates. -/

namespace RefineClaims

open Lean Meta IRLean RefineCases

-- Memory has no instance, so a function with memory has no claim.
run_meta do
  for ty in [(← `(Mem)), (← `(PtrVal)), (← `(Outcome (Val 8 × Mem))),
      (← `(PtrVal → Mem → Outcome (Val 8 × Mem)))] do
    let t ← Elab.Term.elabTerm ty none |>.run'
    if (← synthInstance? (← mkAppM ``Refine #[t])).isSome then
      throwError "IRLean.Refine has an instance for {t}"

-- `tools/binding_check.lean` builds an `ir_instance_refinement` claim with `mkAppM`, letting Lean find the instance. It
-- has to be the same `Expr` as the statement a certificate elaborates.
run_meta do
  for (thm, src, tgt) in [(``addZero, ``addZeroSrc, ``addZeroTgt), (``dropNuw, ``addNuw, ``addPlain),
      (``poisonLane, ``keepLane0, ``identity), (``freezeOfFreeze, ``frozenTwice, ``frozen)] do
    let want ← mkAppM ``Refines #[mkConst src, mkConst tgt]
    let got := (← getConstInfo thm).type
    unless got == want do
      throwError "mkAppM gives {want}, which isn't {thm}'s type {got}"

end RefineClaims
