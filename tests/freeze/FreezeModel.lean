import freeze_added_right_ir
import freeze_duplicated_wrong_ir
import freeze_noundef_removed_right_ir
import freeze_removed_wrong_ir
import freeze_duplicated_of_value_right_ir
import freeze_of_condition_added_right_ir
import freeze_of_condition_removed_wrong_ir
import freeze_of_freeze_right_ir
import freeze_of_value_removed_right_ir
import freeze_poison_to_constant_right_ir

/-! `freeze` in the model, F3: each rewrite in `tests/freeze` and each in `tests/undef_freeze/alive2` that has a `freeze`
and no `undef`, as ir-lean emits it, with a theorem of the case's name proving its verdict. A `_right` case refines,
and a `_wrong` one provably doesn't, at the input and the target's choice given. `tests/freeze.sh` builds this with
warnings as errors, checks its axioms, replays it, and has Alive2 give each case's verdict too.

A function whose run makes a choice returns `Outcomes`, an outcome for each `Choice`, and one whose run makes none
returns `Outcome`. A claim relating the two lifts the second with `Outcomes.det`, as `tools/binding_check.lean` does. -/

open IRLean

/-! ### Right -/

/-- `%x` to `freeze %x`. -/
theorem freeze_added_right :
    Refines (fun x => Outcomes.det (freeze_added_right_ir.src x)) freeze_added_right_ir.tgt := by
  intro x
  refine (Refine.outcomes_det_left _ _).2 fun ct => ?_
  simp only [freeze_added_right_ir.src, freeze_added_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok]
  cases x <;> simp [Val.freeze, Refine.val_none, Refine.val_some]

/-- `freeze %x` to `%x` for a `noundef` `%x`. -/
theorem freeze_noundef_removed_right :
    Refines freeze_noundef_removed_right_ir.src (fun x => Outcomes.det (freeze_noundef_removed_right_ir.tgt x)) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨default, ?_⟩
  cases x with
  | none => exact Refine.outcome_ub _ _
  | some x =>
    simp only [freeze_noundef_removed_right_ir.src, freeze_noundef_removed_right_ir.tgt, noundef]
    rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok]
    simp [Val.freeze, Refine.val_some]

/-- `freeze (freeze %x)` to `freeze %x`: both choose the same. -/
theorem freeze_of_freeze_right : Refines freeze_of_freeze_right_ir.src freeze_of_freeze_right_ir.tgt := by
  intro x
  refine Refine.outcomes_of_same fun c => ?_
  simp only [freeze_of_freeze_right_ir.src, freeze_of_freeze_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok]
  cases x <;> simp [Val.freeze, Refine.val_some]

/-- `freeze %y` to `%y`, where `%y = add (freeze %x), 1` can't be poison. -/
theorem freeze_of_value_removed_right :
    Refines freeze_of_value_removed_right_ir.src freeze_of_value_removed_right_ir.tgt := by
  intro x
  refine Refine.outcomes_of_same fun c => ?_
  simp only [freeze_of_value_removed_right_ir.src, freeze_of_value_removed_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok]
  cases x <;> simp [Val.freeze, Val.add, Refine.val_some]

/-- `freeze poison` to `42`: the source chooses 42. -/
theorem freeze_poison_to_constant_right :
    Refines freeze_poison_to_constant_right_ir.src
      (fun x => Outcomes.det (freeze_poison_to_constant_right_ir.tgt x)) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨fun _ => 42, ?_⟩
  simp only [freeze_poison_to_constant_right_ir.src, freeze_poison_to_constant_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok]
  simp [Choice.pick, Val.freeze, Refine.val_some]

/-- Duplicating `freeze %y`, where `%y` can't be poison: both choose the same. -/
theorem freeze_duplicated_of_value_right :
    Refines freeze_duplicated_of_value_right_ir.src freeze_duplicated_of_value_right_ir.tgt := by
  intro x
  refine Refine.outcomes_of_same fun c => ?_
  simp only [freeze_duplicated_of_value_right_ir.src, freeze_duplicated_of_value_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok]
  cases x <;> simp [Val.freeze, Val.add, Val.sub, Refine.val_some]

/-- Freezing a branch condition: where the source branches on poison, which is undefined, the target branches either
way. -/
theorem freeze_of_condition_added_right :
    Refines (fun c => Outcomes.det (freeze_of_condition_added_right_ir.src c))
      freeze_of_condition_added_right_ir.tgt := by
  intro c
  refine (Refine.outcomes_det_left _ _).2 fun ct => ?_
  cases c with
  | none =>
    simp only [freeze_of_condition_added_right_ir.src]
    rw [run.eq_1]
    exact Refine.outcome_ub _ _
  | some b =>
    simp only [freeze_of_condition_added_right_ir.src, freeze_of_condition_added_right_ir.tgt]
    by_cases hb : b = 1#1
    · subst hb
      rw [run_jump _ (by rfl), run_ret _ (by rfl), run_jump _ (by rfl), run_ret _ (by rfl)]
      exact (Refine.outcome_ok_ok _ _).2 (Refine.refl_val _)
    · have : b = 0#1 := by revert hb; generalize b = b; decide +revert
      subst this
      rw [run_jump _ (by rfl), run_ret _ (by rfl), run_jump _ (by rfl), run_ret _ (by rfl)]
      exact (Refine.outcome_ok_ok _ _).2 (Refine.refl_val _)

/-! ### Wrong -/

/-- `freeze %x` to `%x`: at poison the source is a value, however it chooses, and the target is poison. -/
theorem freeze_removed_wrong :
    ¬ Refines freeze_removed_wrong_ir.src (fun x => Outcomes.det (freeze_removed_wrong_ir.tgt x)) := fun h => by
  obtain ⟨cs, hcs⟩ := (Refine.outcomes_det_right _ _).1 (h none)
  simp only [freeze_removed_wrong_ir.src, freeze_removed_wrong_ir.tgt] at hcs
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hcs
  simp [Val.freeze] at hcs

/-- One `freeze` used twice, to two `freeze`s: at poison the target chooses 0 and 1 and gives 255, and the source gives
0 however it chooses. -/
theorem freeze_duplicated_wrong : ¬ Refines freeze_duplicated_wrong_ir.src freeze_duplicated_wrong_ir.tgt := fun h => by
  obtain ⟨cs, hcs⟩ := h none fun p => if p = [2] then 1 else 0
  simp only [freeze_duplicated_wrong_ir.src, freeze_duplicated_wrong_ir.tgt] at hcs
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hcs
  simp [Choice.pick, Val.freeze, Val.sub] at hcs

/-- Dropping the `freeze` of a branch condition: at poison the source branches, however it chooses, and returns 1 or 2,
and the target's branch on poison is undefined, which a result doesn't allow. -/
theorem freeze_of_condition_removed_wrong :
    ¬ Refines freeze_of_condition_removed_wrong_ir.src
      (fun c => Outcomes.det (freeze_of_condition_removed_wrong_ir.tgt c)) := fun h => by
  obtain ⟨cs, hcs⟩ := (Refine.outcomes_det_right _ _).1 (h none)
  simp only [freeze_of_condition_removed_wrong_ir.src, freeze_of_condition_removed_wrong_ir.tgt] at hcs
  rw [run.eq_1 freeze_of_condition_removed_wrong_ir.tgt.step] at hcs
  simp only [freeze_of_condition_removed_wrong_ir.tgt.step, br] at hcs
  by_cases hb : BitVec.ofNat 1 (cs.pick 1) = 1#1
  · rw [run_jump _ (by simp [freeze_of_condition_removed_wrong_ir.src.step, Val.freeze, br, hb]; rfl),
      run_ret _ (by rfl)] at hcs
    obtain ⟨_, hy, _⟩ := (Refine.outcome_ok _ _).1 hcs
    cases hy
  · rw [run_jump _ (by simp [freeze_of_condition_removed_wrong_ir.src.step, Val.freeze, br, hb]; rfl),
      run_ret _ (by rfl)] at hcs
    obtain ⟨_, hy, _⟩ := (Refine.outcome_ok _ _).1 hcs
    cases hy
