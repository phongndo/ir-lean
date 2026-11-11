import Lean
import RefineCases

/-! What has a `Refines` claim, checked as `tools/binding.py` checks it: what the claim is for a function with memory,
and that the claim `tools/binding_check.lean` builds is the statement a certificate elaborates. -/

namespace RefineClaims

open Lean Meta IRLean RefineCases

-- Until F4, on 2026-11-10, memory had no instance, and this checked that it had none. Now it has one: a function with
-- memory has a claim, and a part of a memory, which nothing compares on its own, doesn't. What the claim says is
-- pinned by theorems in RefineCases.lean, under "Memory".
run_meta do
  for ty in [(← `(Mem)), (← `(PtrVal)), (← `(Outcome (Val 8 × Mem))),
      (← `(PtrVal → Mem → Outcome (Val 8 × Mem))), (← `(PtrVal → Mem → Outcome (PtrVal × Mem)))] do
    let t ← Elab.Term.elabTerm ty none |>.run'
    if (← synthInstance? (← mkAppM ``Refine #[t])).isNone then
      throwError "IRLean.Refine has no instance for {t}"
  for ty in [(← `(IRLean.Ptr)), (← `(IRLean.Byte)), (← `(IRLean.Alloc)), (← `(IRLean.Call))] do
    let t ← Elab.Term.elabTerm ty none |>.run'
    if (← synthInstance? (← mkAppM ``Refine #[t])).isSome then
      throwError "IRLean.Refine has an instance for {t}, which only a whole memory or a pointer value should"

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
