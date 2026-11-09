import select_zero_wrong_ir

/-! A false claim, which has to fail to check with an error that isn't a resource limit: that replacing
`select (fcmp oeq x, 0.0), 0.0, x` by `x` refines, as it would if `-0.0` and `0.0` were one value. -/

open IRLean

-- Every proof unfolds with the same set, whatever each one needs of it.
set_option linter.unusedSimpArgs false

/-- Moves `some` out of an `if`, so that what `simp` leaves of a result is about bit vectors, which `bv_decide` reads. -/
theorem ite_some {α : Type} {c : Prop} [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) := by
  split <;> rfl

theorem select_zero_right : Refines select_zero_wrong_ir.src select_zero_wrong_ir.tgt := by
  intro x
  simp only [select_zero_wrong_ir.src, select_zero_wrong_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide
