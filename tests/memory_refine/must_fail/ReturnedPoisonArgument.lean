import IRLean.MemRefineOps

/-! `returned` keeps refinement only for an argument that isn't poison: for a poison argument the source may return
poison, and the target a value, which isn't the argument. This states `IRLean.Mono.returnedInt` for any argument,
and its proof stops at a poison one. `tests/memory_refine.sh` checks this fails, there. -/

open IRLean

theorem returnedInt_any {arg : Val w} {res res' : Val w} (hr : Refine.le res res') {r : α → β → Prop}
    {k : Outcome α} {k' : Outcome β} (hk : Outcome.Sim r k k') :
    Outcome.Sim r (Mem.returnedInt arg res k) (Mem.returnedInt arg res' k') := by
  simp only [Mem.returnedInt]
  cases res with
  | none =>
    cases arg with
    | none => exact hk
    | some x => simp only [beq_iff_eq, reduceCtorEq, ite_false]; trivial
  | some y =>
    cases hr
    split
    · exact hk
    · trivial
