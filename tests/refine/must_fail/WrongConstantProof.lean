import RefineCases

/-! Must fail to check, with an error that isn't a resource limit: `add i8 %x, 0` to `add i8 %x, 1` changes every
value, so no proof that it refines can go through. `tests/refine.sh` runs this. -/

open IRLean RefineCases

theorem wrong_constant_refines : Refines addZeroSrc addOne := by
  intro x
  cases x with
  | none => exact Refine.outcome_ok _ _ |>.2 ⟨none, rfl, Refine.val_none _⟩
  | some x =>
    refine (Refine.outcome_ok_ok _ _).2 ((Refine.val_some _ _).2 ?_)
    simp only [Val.add, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
    bv_decide
