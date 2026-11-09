import Fx.Src
import Fx.Tgt

/-! tests/binding.py's certificate for `freeze` in the model: `instcombine` dropped an `add %a, 0` after a `freeze` of
a shift that's poison for `x` of 8 or more, and the function ir-lean generated after refines the one before. Both
freeze the same shift at the same place, so each side choosing the same is enough. -/

open IRLean

/-- `instcombine` added `nuw` to the shift: shifting 1 left by less than 8 never drops a set bit. -/
theorem Fx.shl_nuw (x : BitVec 8) : Val.shl (some 1#8) (some x) (nuw := true) = Val.shl (some 1#8) (some x) := by
  have : ∀ y : BitVec 8, Val.shl (some 1#8) (some y) (nuw := true) = Val.shl (some 1#8) (some y) := by decide
  exact this x

theorem Fx.cert : IRLean.Refines Fx.Src.f Fx.Tgt.f := by
  intro x
  refine Refine.outcomes_of_same fun c => ?_
  cases x with
  | none => exact Refine.outcome_ub _ _
  | some x =>
    simp only [Fx.Src.f, Fx.Tgt.f, noundef]
    rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Fx.shl_nuw]
    cases Val.shl (some 1#8) (some x) <;> simp [Val.freeze, Val.add, Refine.val_some]
