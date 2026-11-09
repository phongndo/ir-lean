import bitcast_fneg_right_ir
import copysign_dropped_wrong_ir
import copysign_fabs_sign_right_ir
import fabs_fneg_right_ir
import fcmp_fabs_olt_zero_right_ir
import fcmp_fneg_both_right_ir
import fcmp_oeq_negzero_right_ir
import fcmp_oeq_self_true_wrong_ir
import fcmp_oeq_zero_to_icmp_wrong_ir
import fcmp_olt_to_ult_wrong_ir
import fcmp_swap_right_ir
import fcmp_uno_self_right_ir
import fcmp_uno_to_fpclass_right_ir
import fneg_fneg_right_ir
import fneg_nnan_added_wrong_ir
import fneg_nnan_dropped_right_ir
import fpclass_snan_wrong_ir
import select_zero_wrong_ir

/-! Floating point's bit-level operations in the model, SEM-05's first slice: each rewrite in `tests/float`, as ir-lean
emits it, with a theorem of the case's name proving its verdict. A `_right` case refines, for every input, poison
included, and a `_wrong` one provably doesn't, at the input given. `tests/float.sh` builds this with warnings as
errors, checks its axioms, replays it, and has Alive2 give each case's verdict too. See `docs/float.md`.

Each proof unfolds both functions with `simp`, which reads `IRLean/Float.lean` through the `llvm` set, and closes what's
left with `bv_decide`, for each argument poison or a value. No operation here makes a choice, so each side returns an
`Outcome`. -/

open IRLean

-- Every proof unfolds with the same set, whatever each one needs of it.
set_option linter.unusedSimpArgs false

/-- Moves `some` out of an `if`, so that what `simp` leaves of a result is about bit vectors, which `bv_decide` reads. -/
theorem ite_some {α : Type} {c : Prop} [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) := by
  split <;> rfl

/-! ### Right -/

/-- `bitcast (fneg x)` to `xor (bitcast x), sign`: fneg flips the sign bit and keeps every NaN as it was. -/
theorem bitcast_fneg_right : Refines bitcast_fneg_right_ir.src bitcast_fneg_right_ir.tgt := by
  intro x0
  simp only [bitcast_fneg_right_ir.src, bitcast_fneg_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `copysign(x, fabs y)` to `fabs x`: the sign it copies is clear. -/
theorem copysign_fabs_sign_right : Refines copysign_fabs_sign_right_ir.src copysign_fabs_sign_right_ir.tgt := by
  intro x0 x1
  simp only [copysign_fabs_sign_right_ir.src, copysign_fabs_sign_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> cases x1 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fabs (fneg x)` to `fabs x`, as fabs.ll folds it. -/
theorem fabs_fneg_right : Refines fabs_fneg_right_ir.src fabs_fneg_right_ir.tgt := by
  intro x0
  simp only [fabs_fneg_right_ir.src, fabs_fneg_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp olt (fabs x), 0.0` to `false`: no magnitude is below zero. -/
theorem fcmp_fabs_olt_zero_right : Refines fcmp_fabs_olt_zero_right_ir.src fcmp_fabs_olt_zero_right_ir.tgt := by
  intro x0
  simp only [fcmp_fabs_olt_zero_right_ir.src, fcmp_fabs_olt_zero_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp olt (fneg x), (fneg y)` to `fcmp ogt x, y`, as fcmp.ll folds it, NaNs and zeros included. -/
theorem fcmp_fneg_both_right : Refines fcmp_fneg_both_right_ir.src fcmp_fneg_both_right_ir.tgt := by
  intro x0 x1
  simp only [fcmp_fneg_both_right_ir.src, fcmp_fneg_both_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> cases x1 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp oeq x, -0.0` to `fcmp oeq x, 0.0`: zeros of either sign are equal. -/
theorem fcmp_oeq_negzero_right : Refines fcmp_oeq_negzero_right_ir.src fcmp_oeq_negzero_right_ir.tgt := by
  intro x0
  simp only [fcmp_oeq_negzero_right_ir.src, fcmp_oeq_negzero_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp olt 1.0, x` to `fcmp ogt x, 1.0`, the constant moved right, as InstCombine canonicalizes. -/
theorem fcmp_swap_right : Refines fcmp_swap_right_ir.src fcmp_swap_right_ir.tgt := by
  intro x0
  simp only [fcmp_swap_right_ir.src, fcmp_swap_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp uno x, x` to `fcmp uno x, 0.0`, as InstCombine canonicalizes: both say whether x is a NaN. -/
theorem fcmp_uno_self_right : Refines fcmp_uno_self_right_ir.src fcmp_uno_self_right_ir.tgt := by
  intro x0
  simp only [fcmp_uno_self_right_ir.src, fcmp_uno_self_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp uno x, 0.0` to `is.fpclass(x, nan)`, where 3 names both kinds of NaN. -/
theorem fcmp_uno_to_fpclass_right : Refines fcmp_uno_to_fpclass_right_ir.src fcmp_uno_to_fpclass_right_ir.tgt := by
  intro x0
  simp only [fcmp_uno_to_fpclass_right_ir.src, fcmp_uno_to_fpclass_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fneg (fneg x)` to `x`, as InstCombine's fneg.ll folds it: both flip the sign bit and nothing else. -/
theorem fneg_fneg_right : Refines fneg_fneg_right_ir.src fneg_fneg_right_ir.tgt := by
  intro x0
  simp only [fneg_fneg_right_ir.src, fneg_fneg_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fneg nnan x` to `fneg x`: dropping a flag only takes poison away. -/
theorem fneg_nnan_dropped_right : Refines fneg_nnan_dropped_right_ir.src fneg_nnan_dropped_right_ir.tgt := by
  intro x0
  simp only [fneg_nnan_dropped_right_ir.src, fneg_nnan_dropped_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-! ### Wrong -/

/-- `copysign(x, y)` to `x`: the sign comes from y. -/
theorem copysign_dropped_wrong : ¬ Refines copysign_dropped_wrong_ir.src copysign_dropped_wrong_ir.tgt := fun h => by
  have hc := h (some 0x3C00#16) (some 0x8000#16)
  simp only [copysign_dropped_wrong_ir.src, copysign_dropped_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `fcmp oeq x, x` to `true`: a NaN isn't equal to itself. -/
theorem fcmp_oeq_self_true_wrong : ¬ Refines fcmp_oeq_self_true_wrong_ir.src fcmp_oeq_self_true_wrong_ir.tgt := fun h => by
  have hc := h (some 0x7FF8000000000000#64)
  simp only [fcmp_oeq_self_true_wrong_ir.src, fcmp_oeq_self_true_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `fcmp oeq x, 0.0` to `icmp eq (bitcast x), 0`: -0.0 equals 0.0, but its bits are not zero. -/
theorem fcmp_oeq_zero_to_icmp_wrong : ¬ Refines fcmp_oeq_zero_to_icmp_wrong_ir.src fcmp_oeq_zero_to_icmp_wrong_ir.tgt := fun h => by
  have hc := h (some 0x80000000#32)
  simp only [fcmp_oeq_zero_to_icmp_wrong_ir.src, fcmp_oeq_zero_to_icmp_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `fcmp olt x, y` to `fcmp ult x, y`: at a NaN the source is false and the target true. -/
theorem fcmp_olt_to_ult_wrong : ¬ Refines fcmp_olt_to_ult_wrong_ir.src fcmp_olt_to_ult_wrong_ir.tgt := fun h => by
  have hc := h (some 0x7FC00000#32) (some 0#32)
  simp only [fcmp_olt_to_ult_wrong_ir.src, fcmp_olt_to_ult_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `fneg x` to `fneg nnan x`: the target is poison at a NaN, where the source has a value. -/
theorem fneg_nnan_added_wrong : ¬ Refines fneg_nnan_added_wrong_ir.src fneg_nnan_added_wrong_ir.tgt := fun h => by
  have hc := h (some 0x7FC00000#32)
  simp only [fneg_nnan_added_wrong_ir.src, fneg_nnan_added_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `is.fpclass(x, snan)` to `fcmp uno x, 0.0`: a quiet NaN is unordered but not signaling. -/
theorem fpclass_snan_wrong : ¬ Refines fpclass_snan_wrong_ir.src fpclass_snan_wrong_ir.tgt := fun h => by
  have hc := h (some 0x7FC00000#32)
  simp only [fpclass_snan_wrong_ir.src, fpclass_snan_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `select (fcmp oeq x, 0.0), 0.0, x` to `x`: at -0.0 the source gives 0.0 and the target -0.0. -/
theorem select_zero_wrong : ¬ Refines select_zero_wrong_ir.src select_zero_wrong_ir.tgt := fun h => by
  have hc := h (some 0x80000000#32)
  simp only [select_zero_wrong_ir.src, select_zero_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)
