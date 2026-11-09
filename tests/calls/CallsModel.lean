import pure_dropped_right_ir
import pure_merged_right_ir
import pure_argument_simplified_right_ir
import pure_reordered_right_ir
import pure_dropped_without_willreturn_wrong_ir
import pure_dropped_without_nounwind_wrong_ir
import pure_added_wrong_ir
import pure_argument_changed_wrong_ir
import pure_duplicated_wrong_ir
import pure_reordered_without_nounwind_wrong_ir

/-! Calls outside the module, as ir-lean emits them: each rewrite in `tests/calls`, with a theorem of the case's name
proving its verdict. A `_right` case refines, and a `_wrong` one provably doesn't, in the world, input and target
choice given. `tests/calls.sh` builds this with warnings as errors, checks its axioms, replays it, and has Alive2 give
each case its verdict. [`docs/calls.md`](../../docs/calls.md) has the design.

A function that calls outside the module takes the world and the trace before it, and ends as an `Exit`. One that
calls outside the module without effects also makes choices: which of the callee's answers each call gets. A claim
relating a function that calls outside the module to one that doesn't lifts the second with `Exit.lift`, and one whose
run makes choices to one that makes none with `Outcomes.det`. -/

open IRLean

/-- A world where every call that accesses no memory answers `a`. -/
def answering (a : Event → Nat → Answer) : World := ⟨fun _ => .ret [], fun _ _ _ => .ret [], a⟩

/-! ### Right -/

/-- An unused call that will return and can't unwind, dropped: every answer either returns or is undefined. -/
theorem pure_dropped_right :
    Refines pure_dropped_right_ir.src
      (fun x _ t => Outcomes.det (Exit.lift (pure_dropped_right_ir.tgt x) t)) := by
  intro x w t ct
  refine ⟨ct, ?_⟩
  simp only [pure_dropped_right_ir.src, pure_dropped_right_ir.tgt, Outcomes.det]
  rw [run_ret pure_dropped_right_ir.tgt.step (by rfl), run.eq_1]
  simp only [pure_dropped_right_ir.src.step, World.callPure, World.quiet, Exit.bind]
  cases w.pure ⟨"f", [Lanes.ofVal x]⟩ (ct.pick 1) <;> simp only [andThen, ret, Outcome.ok, Outcome.ub, Exit.lift] <;>
    first | trivial | exact ⟨_, rfl, Refine.Reflexive.refl _⟩

/-- Two calls with the same argument, merged: the source picks the target's answer for both, so `a - b` is `a - a`. -/
theorem pure_merged_right : Refines pure_merged_right_ir.src pure_merged_right_ir.tgt := by
  intro x w t ct
  refine ⟨fun p => if p = [2] then ct [1] else ct p, ?_⟩
  simp only [pure_merged_right_ir.src, pure_merged_right_ir.tgt]
  rw [run.eq_1, run.eq_1]
  simp +decide only [pure_merged_right_ir.src.step, pure_merged_right_ir.tgt.step, World.callPure, World.quiet,
    Exit.bind, Choice.pick, ite_true, ite_false]
  cases w.pure ⟨"f", [Lanes.ofVal x]⟩ (ct [1]) with
  | ret v =>
    simp only [andThen, ret, Outcome.ok]
    refine ⟨_, rfl, ⟨_, rfl, ?_⟩⟩
    cases h : Lanes.toVal 8 v with
    | none => trivial
    | some a => simp [Val.sub, Refine.val_some]
  | undefined => trivial
  | stays => rfl
  | unwinds => exact ⟨_, rfl, rfl⟩

/-- The argument simplified to the same value, `~~x` to `x`, and `add %r, 0` to `%r`. -/
theorem pure_argument_simplified_right :
    Refines pure_argument_simplified_right_ir.src pure_argument_simplified_right_ir.tgt := by
  intro x w t ct
  refine ⟨ct, ?_⟩
  have hz : Val.xor (Val.xor x (some 255#8)) (some 255#8) = x := by
    cases x with
    | none => rfl
    | some v => simp only [Val.xor, Val.map₂, Option.some.injEq]; bv_decide
  simp only [pure_argument_simplified_right_ir.src, pure_argument_simplified_right_ir.tgt]
  rw [run.eq_1, run.eq_1]
  simp only [pure_argument_simplified_right_ir.src.step, pure_argument_simplified_right_ir.tgt.step, World.callPure,
    World.quiet, Exit.bind, hz]
  cases w.pure ⟨"f", [Lanes.ofVal x]⟩ (ct.pick 1) with
  | ret v =>
    simp only [andThen, ret, Outcome.ok]
    refine ⟨_, rfl, ⟨_, rfl, ?_⟩⟩
    cases Lanes.toVal 8 v with
    | none => trivial
    | some a => simp [Val.add, Refine.val_some]
  | undefined => trivial
  | stays => rfl
  | unwinds => exact ⟨_, rfl, rfl⟩

/-- Two calls that will return and can't unwind, swapped: the source picks for each call the answer the target got
for it. -/
theorem pure_reordered_right : Refines pure_reordered_right_ir.src pure_reordered_right_ir.tgt := by
  intro x w t ct
  refine ⟨fun p => if p = [1] then ct [2] else if p = [2] then ct [1] else ct p, ?_⟩
  simp only [pure_reordered_right_ir.src, pure_reordered_right_ir.tgt]
  rw [run.eq_1, run.eq_1]
  simp +decide only [pure_reordered_right_ir.src.step, pure_reordered_right_ir.tgt.step, World.callPure,
    World.quiet, Exit.bind, Choice.pick, ite_true, ite_false]
  cases w.pure ⟨"f", [Lanes.ofVal x]⟩ (ct [2]) <;> cases w.pure ⟨"g", [Lanes.ofVal x]⟩ (ct [1]) <;>
    simp only [andThen, ret, Outcome.ok, Outcome.ub] <;>
    first | trivial | exact ⟨_, rfl, Refine.Reflexive.refl _⟩

/-! ### Wrong -/

/-- Dropping a call that may never come back: where it doesn't, the source never finishes, and the target returns. -/
theorem pure_dropped_without_willreturn_wrong :
    ¬ Refines pure_dropped_without_willreturn_wrong_ir.src
      (fun x _ t => Outcomes.det (Exit.lift (pure_dropped_without_willreturn_wrong_ir.tgt x) t)) := fun h => by
  obtain ⟨cs, hcs⟩ := h none (answering fun _ _ => .stays) [] default
  simp only [pure_dropped_without_willreturn_wrong_ir.src, pure_dropped_without_willreturn_wrong_ir.tgt,
    Outcomes.det] at hcs
  rw [run_ret pure_dropped_without_willreturn_wrong_ir.tgt.step (by rfl), run.eq_1] at hcs
  simp [pure_dropped_without_willreturn_wrong_ir.src.step, answering, World.callPure, World.quiet, Exit.bind, andThen,
    Exit.lift, Outcome.ok, Refine.outcome_none] at hcs

/-- Dropping a call that may unwind: where it does, the source unwinds, and the target returns. -/
theorem pure_dropped_without_nounwind_wrong :
    ¬ Refines pure_dropped_without_nounwind_wrong_ir.src
      (fun x _ t => Outcomes.det (Exit.lift (pure_dropped_without_nounwind_wrong_ir.tgt x) t)) := fun h => by
  obtain ⟨cs, hcs⟩ := h none (answering fun _ _ => .unwinds) [] default
  simp only [pure_dropped_without_nounwind_wrong_ir.src, pure_dropped_without_nounwind_wrong_ir.tgt,
    Outcomes.det] at hcs
  rw [run_ret pure_dropped_without_nounwind_wrong_ir.tgt.step (by rfl), run.eq_1] at hcs
  obtain ⟨_, hy, hle⟩ := (Refine.outcome_ok _ _).1 (by
    simpa [pure_dropped_without_nounwind_wrong_ir.src.step, answering, World.callPure, World.quiet, Exit.bind,
      andThen, ret, Outcome.ok] using hcs)
  simp only [Exit.lift, andThen, Outcome.ok, Option.some.injEq, Except.ok.injEq] at hy
  subst hy
  cases hle

/-- Adding a call that isn't `speculatable`: where it's undefined, the target is and the source isn't. -/
theorem pure_added_wrong :
    ¬ Refines (fun x _ t => Outcomes.det (Exit.lift (pure_added_wrong_ir.src x) t)) pure_added_wrong_ir.tgt :=
  fun h => by
  have hcs := (Refine.outcomes_det_left _ _).1 (h none (answering fun _ _ => .undefined) []) default
  simp only [pure_added_wrong_ir.src, pure_added_wrong_ir.tgt] at hcs
  rw [run_ret pure_added_wrong_ir.src.step (by rfl), run.eq_1] at hcs
  obtain ⟨_, hy, _⟩ := (Refine.outcome_ok _ _).1 (by simpa [Exit.lift, andThen, Outcome.ok] using hcs)
  simp [pure_added_wrong_ir.tgt.step, answering, World.callPure, World.quiet, Exit.bind, andThen, Outcome.ub] at hy

/-- Changing the argument from `x` to `x + 1`: in a world where the callee answers 0 for 0 and 1 for anything else,
at 0 the source returns 0 and the target 1. -/
theorem pure_argument_changed_wrong :
    ¬ Refines pure_argument_changed_wrong_ir.src pure_argument_changed_wrong_ir.tgt := fun h => by
  obtain ⟨cs, hcs⟩ := h (some 0#8)
    (answering fun e _ => .ret [some (if e = ⟨"f", [[some 0]]⟩ then 0 else 1)]) [] default
  simp only [pure_argument_changed_wrong_ir.src, pure_argument_changed_wrong_ir.tgt] at hcs
  rw [run.eq_1, run.eq_1] at hcs
  simp [pure_argument_changed_wrong_ir.src.step, pure_argument_changed_wrong_ir.tgt.step, answering, World.callPure,
    World.quiet, Exit.bind, andThen, ret, Outcome.ok, Lanes.ofVal, Lanes.toVal, Lanes.lane, Val.add, Refine.le] at hcs

/-- One call used twice, to two calls: in a world where each answer is the number the run picks, the target picks 0
and 1 and gives 255, and the source gives 0 however it picks. LangRef's `memory(none)` doesn't promise the same answer
twice. -/
theorem pure_duplicated_wrong : ¬ Refines pure_duplicated_wrong_ir.src pure_duplicated_wrong_ir.tgt := fun h => by
  obtain ⟨cs, hcs⟩ := h none (answering fun _ i => .ret [some i]) [] fun p => if p = [2] then 1 else 0
  simp only [pure_duplicated_wrong_ir.src, pure_duplicated_wrong_ir.tgt] at hcs
  rw [run.eq_1, run.eq_1] at hcs
  simp [pure_duplicated_wrong_ir.src.step, pure_duplicated_wrong_ir.tgt.step, answering, World.callPure, World.quiet,
    Exit.bind, andThen, ret, Outcome.ok, Choice.pick, Lanes.toVal, Lanes.lane, Val.sub, Refine.le] at hcs

/-- Swapping two calls that may unwind: where both do, the source ends unwinding from `@f`, and the target from
`@g`. -/
theorem pure_reordered_without_nounwind_wrong :
    ¬ Refines pure_reordered_without_nounwind_wrong_ir.src pure_reordered_without_nounwind_wrong_ir.tgt :=
  fun h => by
  obtain ⟨cs, hcs⟩ := h none (answering fun _ _ => .unwinds) [] default
  simp only [pure_reordered_without_nounwind_wrong_ir.src, pure_reordered_without_nounwind_wrong_ir.tgt] at hcs
  rw [run.eq_1, run.eq_1] at hcs
  simp [pure_reordered_without_nounwind_wrong_ir.src.step, pure_reordered_without_nounwind_wrong_ir.tgt.step,
    answering, World.callPure, World.quiet, Exit.bind, andThen, ret, Outcome.ok, Refine.le] at hcs
