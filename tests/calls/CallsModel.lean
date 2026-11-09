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
import nounwind_call_added_wrong_ir
import effect_kept_right_ir
import effect_then_undefined_right_ir
import read_dropped_right_ir
import read_merged_right_ir
import effect_added_wrong_ir
import effect_dropped_wrong_ir
import effect_dropped_willreturn_wrong_ir
import effect_reordered_wrong_ir
import effect_argument_changed_wrong_ir
import effect_twice_wrong_ir
import read_moved_across_effect_wrong_ir
import effect_dropped_before_undefined_wrong_ir
import effect_dropped_before_loop_wrong_ir
import effect_then_spin_for_spin_or_return_wrong_ir

/-! Calls outside the module, as ir-lean emits them: each rewrite in `tests/calls`, with a theorem of the case's name
proving its verdict. A `_right` case refines, and a `_wrong` one provably doesn't, in the world, input and target
choice given. `tests/calls.sh` builds this with warnings as errors, checks its axioms, replays it, and has Alive2 give
each case its verdict. [`docs/calls.md`](../../docs/calls.md) has the design.

A function that calls outside the module takes the world and the trace before it, and returns `Talks`: how its run
ends, as an `Exit`, for each way it chooses and each number of calls with effects it's watched for. A call with
effects goes in the trace, and is cut off past the number watched for. A call without effects makes a choice: which of
the callee's answers it gets. A claim relating a function that calls outside the module to one that doesn't lifts the
second with `Talks.lift`. -/

open IRLean

/-- A world where every call that accesses no memory answers `a`. -/
def answering (a : Event → Nat → Answer) : World := ⟨fun _ => .ret [], fun _ _ _ => .ret [], a⟩

/-- A world where every call with effects answers `a`, and every call that only reads answers `r`. -/
def effecting (a : Trace → Answer) (r : Trace → Event → Nat → Answer := fun _ _ _ => .ret []) : World :=
  ⟨a, r, fun _ _ => .ret []⟩

/-! ### Right -/

/-- An unused call that will return and can't unwind, dropped: every answer either returns or is undefined. -/
theorem pure_dropped_right :
    Refines pure_dropped_right_ir.src
      (fun x _ t => Talks.lift (pure_dropped_right_ir.tgt x) t) := by
  intro x w t ct
  refine ⟨ct, fun n => ?_⟩
  simp only [pure_dropped_right_ir.src, pure_dropped_right_ir.tgt, Talks.lift]
  rw [run_ret pure_dropped_right_ir.tgt.step (by rfl), run.eq_1]
  simp only [pure_dropped_right_ir.src.step, World.callPure, World.quiet, Exit.bind]
  cases w.pure ⟨"f", [("i8", Lanes.ofVal x)]⟩ (ct.pick 1) <;> simp only [andThen, ret, Outcome.ok, Outcome.ub, Exit.lift] <;>
    first | trivial | exact ⟨_, rfl, Refine.Reflexive.refl _⟩

/-- Two calls with the same argument, merged: the source picks the target's answer for both, so `a - b` is `a - a`. -/
theorem pure_merged_right : Refines pure_merged_right_ir.src pure_merged_right_ir.tgt := by
  intro x w t ct
  refine ⟨fun p => if p = [2] then ct [1] else ct p, fun n => ?_⟩
  simp only [pure_merged_right_ir.src, pure_merged_right_ir.tgt]
  rw [run.eq_1, run.eq_1]
  simp +decide only [pure_merged_right_ir.src.step, pure_merged_right_ir.tgt.step, World.callPure, World.quiet,
    Exit.bind, Choice.pick, ite_true, ite_false]
  cases w.pure ⟨"f", [("i8", Lanes.ofVal x)]⟩ (ct [1]) with
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
  refine ⟨ct, fun n => ?_⟩
  have hz : Val.xor (Val.xor x (some 255#8)) (some 255#8) = x := by
    cases x with
    | none => rfl
    | some v => simp only [Val.xor, Val.map₂, Option.some.injEq]; bv_decide
  simp only [pure_argument_simplified_right_ir.src, pure_argument_simplified_right_ir.tgt]
  rw [run.eq_1, run.eq_1]
  simp only [pure_argument_simplified_right_ir.src.step, pure_argument_simplified_right_ir.tgt.step, World.callPure,
    World.quiet, Exit.bind, hz]
  cases w.pure ⟨"f", [("i8", Lanes.ofVal x)]⟩ (ct.pick 1) with
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
  refine ⟨fun p => if p = [1] then ct [2] else if p = [2] then ct [1] else ct p, fun n => ?_⟩
  simp only [pure_reordered_right_ir.src, pure_reordered_right_ir.tgt]
  rw [run.eq_1, run.eq_1]
  simp +decide only [pure_reordered_right_ir.src.step, pure_reordered_right_ir.tgt.step, World.callPure,
    World.quiet, Exit.bind, Choice.pick, ite_true, ite_false]
  cases w.pure ⟨"f", [("i8", Lanes.ofVal x)]⟩ (ct [2]) <;> cases w.pure ⟨"g", [("i8", Lanes.ofVal x)]⟩ (ct [1]) <;>
    simp only [andThen, ret, Outcome.ok, Outcome.ub] <;>
    first | trivial | exact ⟨_, rfl, Refine.Reflexive.refl _⟩

/-! ### Wrong -/

/-- Dropping a call that may never come back: where it doesn't, the source never finishes, and the target returns. -/
theorem pure_dropped_without_willreturn_wrong :
    ¬ Refines pure_dropped_without_willreturn_wrong_ir.src
      (fun x _ t => Talks.lift (pure_dropped_without_willreturn_wrong_ir.tgt x) t) := fun h => by
  obtain ⟨cs, hcs⟩ := h none (answering fun _ _ => .stays) [] default
  have hcs := hcs 0
  simp only [pure_dropped_without_willreturn_wrong_ir.src, pure_dropped_without_willreturn_wrong_ir.tgt,
    Talks.lift] at hcs
  rw [run_ret pure_dropped_without_willreturn_wrong_ir.tgt.step (by rfl), run.eq_1] at hcs
  simp [pure_dropped_without_willreturn_wrong_ir.src.step, answering, World.callPure, World.quiet, Exit.bind, andThen,
    Exit.lift, Outcome.ok, Refine.outcome_none] at hcs

/-- Dropping a call that may unwind: where it does, the source unwinds, and the target returns. -/
theorem pure_dropped_without_nounwind_wrong :
    ¬ Refines pure_dropped_without_nounwind_wrong_ir.src
      (fun x _ t => Talks.lift (pure_dropped_without_nounwind_wrong_ir.tgt x) t) := fun h => by
  obtain ⟨cs, hcs⟩ := h none (answering fun _ _ => .unwinds) [] default
  have hcs := hcs 0
  simp only [pure_dropped_without_nounwind_wrong_ir.src, pure_dropped_without_nounwind_wrong_ir.tgt,
    Talks.lift] at hcs
  rw [run_ret pure_dropped_without_nounwind_wrong_ir.tgt.step (by rfl), run.eq_1] at hcs
  obtain ⟨_, hy, hle⟩ := (Refine.outcome_ok _ _).1 (by
    simpa [pure_dropped_without_nounwind_wrong_ir.src.step, answering, World.callPure, World.quiet, Exit.bind,
      andThen, ret, Outcome.ok] using hcs)
  simp only [Exit.lift, andThen, Outcome.ok, Option.some.injEq, Except.ok.injEq] at hy
  subst hy
  cases hle

/-- Adding a call that isn't `speculatable`: where it's undefined, the target is and the source isn't. -/
theorem pure_added_wrong :
    ¬ Refines (fun x _ t => Talks.lift (pure_added_wrong_ir.src x) t) pure_added_wrong_ir.tgt :=
  fun h => by
  obtain ⟨cs, hcs⟩ := h none (answering fun _ _ => .undefined) [] default
  have hcs := hcs 0
  simp only [pure_added_wrong_ir.src, pure_added_wrong_ir.tgt, Talks.lift] at hcs
  rw [run_ret pure_added_wrong_ir.src.step (by rfl), run.eq_1] at hcs
  obtain ⟨_, hy, _⟩ := (Refine.outcome_ok _ _).1 (by simpa [Exit.lift, andThen, Outcome.ok] using hcs)
  simp [pure_added_wrong_ir.tgt.step, answering, World.callPure, World.quiet, Exit.bind, andThen, Outcome.ub] at hy

/-- Changing the argument from `x` to `x + 1`: in a world where the callee answers 0 for 0 and 1 for anything else,
at 0 the source returns 0 and the target 1. -/
theorem pure_argument_changed_wrong :
    ¬ Refines pure_argument_changed_wrong_ir.src pure_argument_changed_wrong_ir.tgt := fun h => by
  obtain ⟨cs, hcs⟩ := h (some 0#8)
    (answering fun e _ => .ret [some (if e = ⟨"f", [("i8", [some 0])]⟩ then 0 else 1)]) [] default
  have hcs := hcs 0
  simp only [pure_argument_changed_wrong_ir.src, pure_argument_changed_wrong_ir.tgt] at hcs
  rw [run.eq_1, run.eq_1] at hcs
  simp [pure_argument_changed_wrong_ir.src.step, pure_argument_changed_wrong_ir.tgt.step, answering, World.callPure,
    World.quiet, Exit.bind, andThen, ret, Outcome.ok, Lanes.ofVal, Lanes.toVal, Lanes.lane, Val.add, Refine.le] at hcs

/-- One call used twice, to two calls: in a world where each answer is the number the run picks, the target picks 0
and 1 and gives 255, and the source gives 0 however it picks. LangRef's `memory(none)` doesn't promise the same answer
twice. -/
theorem pure_duplicated_wrong : ¬ Refines pure_duplicated_wrong_ir.src pure_duplicated_wrong_ir.tgt := fun h => by
  obtain ⟨cs, hcs⟩ := h none (answering fun _ i => .ret [some i]) [] fun p => if p = [2] then 1 else 0
  have hcs := hcs 0
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
  have hcs := hcs 0
  simp only [pure_reordered_without_nounwind_wrong_ir.src, pure_reordered_without_nounwind_wrong_ir.tgt] at hcs
  rw [run.eq_1, run.eq_1] at hcs
  simp [pure_reordered_without_nounwind_wrong_ir.src.step, pure_reordered_without_nounwind_wrong_ir.tgt.step,
    answering, World.callPure, World.quiet, Exit.bind, andThen, ret, Outcome.ok, Refine.le] at hcs

/-- Marking a call to a function that calls outside the module `nounwind`: in a world where the call outside unwinds,
the source unwinds and the target is undefined. -/
theorem nounwind_call_added_wrong :
    ¬ Refines nounwind_call_added_wrong_ir.src nounwind_call_added_wrong_ir.tgt := fun h => by
  obtain ⟨cs, hcs⟩ := h none (answering fun _ _ => .unwinds) [] default
  have hcs := hcs 0
  simp only [nounwind_call_added_wrong_ir.src, nounwind_call_added_wrong_ir.tgt] at hcs
  rw [run.eq_1, run.eq_1] at hcs
  simp only [nounwind_call_added_wrong_ir.src.step, nounwind_call_added_wrong_ir.tgt.step,
    nounwind_call_added_wrong_ir.g] at hcs
  rw [run.eq_1, run.eq_1] at hcs
  simp [nounwind_call_added_wrong_ir.g.step, answering, World.callPure, World.quiet, Exit.bind, andThen, ret,
    Outcome.ok, Outcome.ub, Refine.le] at hcs

/-! ### Calls with effects, and calls that only read -/

/-- `0 - (0 - x)` to `x` around a call with effects, which stays: cut off at it, both have the same trace, and past
it, the same trace and a result that refines. -/
theorem effect_kept_right : Refines effect_kept_right_ir.src effect_kept_right_ir.tgt := by
  intro x w t ct
  refine ⟨ct, fun n => ?_⟩
  have hr : Refine.le (Val.sub (some 0#8) (Val.sub (some 0#8) x)) x := by
    cases x with
    | none => trivial
    | some v => simp only [Val.sub, Bool.false_and, Bool.or_self, Bool.false_eq_true, ite_false,
        Refine.val_some, Option.some.injEq]; bv_decide
  simp only [effect_kept_right_ir.src, effect_kept_right_ir.tgt]
  rw [run.eq_1, run.eq_1]
  simp only [effect_kept_right_ir.src.step, effect_kept_right_ir.tgt.step, World.callEffect, Exit.bind]
  by_cases hn : n ≤ t.length
  · simp only [hn, ite_true, andThen, ret, Outcome.ok]
    exact ⟨_, rfl, rfl⟩
  · simp only [hn, ite_false]
    cases w.effect (⟨"use", [("i8", Lanes.ofVal (Val.sub (some 0#8) x))]⟩ :: t) <;>
      simp only [andThen, ret, Outcome.ok, Outcome.ub, Bool.false_eq_true, ite_false]
    · exact ⟨_, rfl, ⟨_, rfl, hr⟩⟩
    all_goals first | trivial | exact ⟨_, rfl, Refine.Reflexive.refl _⟩

/-- Undefined behavior after a call with effects, to poison: watched past the call, where it comes back, the source is
undefined, and where it doesn't, both end in it; watched no further, both are cut off at it. -/
theorem effect_then_undefined_right :
    Refines effect_then_undefined_right_ir.src effect_then_undefined_right_ir.tgt := by
  intro x w t ct
  refine ⟨ct, fun n => ?_⟩
  simp only [effect_then_undefined_right_ir.src, effect_then_undefined_right_ir.tgt]
  rw [run.eq_1, run.eq_1]
  simp only [effect_then_undefined_right_ir.src.step, effect_then_undefined_right_ir.tgt.step, World.callEffect,
    Exit.bind]
  by_cases hn : n ≤ t.length
  · simp only [hn, ite_true, andThen, ret, Outcome.ok]
    exact ⟨_, rfl, rfl⟩
  · simp only [hn, ite_false]
    cases w.effect (⟨"use", [("i8", Lanes.ofVal x)]⟩ :: t) <;>
      simp only [andThen, ret, Outcome.ok, Outcome.ub, Bool.false_eq_true, ite_false]
    · cases x <;> simp only [Val.udiv, Outcome.ub] <;> trivial
    all_goals first | trivial | exact ⟨_, rfl, Refine.Reflexive.refl _⟩

/-- An unused call that only reads, will return and can't unwind, dropped. -/
theorem read_dropped_right :
    Refines read_dropped_right_ir.src (fun x _ t => Talks.lift (read_dropped_right_ir.tgt x) t) := by
  intro x w t ct
  refine ⟨ct, fun n => ?_⟩
  simp only [read_dropped_right_ir.src, read_dropped_right_ir.tgt, Talks.lift]
  rw [run_ret read_dropped_right_ir.tgt.step (by rfl), run.eq_1]
  simp only [read_dropped_right_ir.src.step, World.callRead, World.quiet, Exit.bind]
  cases w.read t ⟨"peek", [("i8", Lanes.ofVal x)]⟩ (ct.pick 1) <;>
    simp only [andThen, ret, Outcome.ok, Outcome.ub, Exit.lift] <;>
    first | trivial | exact ⟨_, rfl, Refine.Reflexive.refl _⟩

/-- Two calls that only read, with no call with effects between, merged: they read after the same trace, and the
source picks the target's answer for both. -/
theorem read_merged_right : Refines read_merged_right_ir.src read_merged_right_ir.tgt := by
  intro x w t ct
  refine ⟨fun p => if p = [2] then ct [1] else ct p, fun n => ?_⟩
  simp only [read_merged_right_ir.src, read_merged_right_ir.tgt]
  rw [run.eq_1, run.eq_1]
  simp +decide only [read_merged_right_ir.src.step, read_merged_right_ir.tgt.step, World.callRead, World.quiet,
    Exit.bind, Choice.pick, ite_true, ite_false]
  -- The second read is under the first's continuation, so its answer is rewritten once the first has returned.
  cases hA : w.read t ⟨"peek", [("i8", Lanes.ofVal x)]⟩ (ct [1]) with
  | ret v =>
    simp only [andThen, ret, Outcome.ok, hA]
    refine ⟨_, rfl, ⟨_, rfl, ?_⟩⟩
    cases Lanes.toVal 8 v with
    | none => trivial
    | some a => simp [Val.sub, Refine.val_some]
  | undefined => trivial
  | stays => rfl
  | unwinds => exact ⟨_, rfl, rfl⟩

/-- Adding a call with effects: in a world where it returns, watched past it, the target's trace has it and the
source's doesn't. -/
theorem effect_added_wrong :
    ¬ Refines (fun x _ t => Talks.lift (effect_added_wrong_ir.src x) t) effect_added_wrong_ir.tgt := fun h => by
  obtain ⟨cs, hcs⟩ := h none (effecting fun _ => .ret []) [] default
  have hcs := hcs 1
  simp only [effect_added_wrong_ir.src, effect_added_wrong_ir.tgt, Talks.lift] at hcs
  rw [run_ret effect_added_wrong_ir.src.step (by rfl), run.eq_1] at hcs
  simp [effect_added_wrong_ir.tgt.step, effecting, World.callEffect, Exit.bind, Exit.lift, andThen, ret, Outcome.ok,
    Refine.le] at hcs

/-- Dropping a call with effects: in a world where it returns, watched past it, the source's trace has it and the
target's doesn't. -/
theorem effect_dropped_wrong :
    ¬ Refines effect_dropped_wrong_ir.src (fun x _ t => Talks.lift (effect_dropped_wrong_ir.tgt x) t) := fun h => by
  obtain ⟨cs, hcs⟩ := h none (effecting fun _ => .ret []) [] default
  have hcs := hcs 1
  simp only [effect_dropped_wrong_ir.src, effect_dropped_wrong_ir.tgt, Talks.lift] at hcs
  rw [run_ret effect_dropped_wrong_ir.tgt.step (by rfl), run.eq_1] at hcs
  simp [effect_dropped_wrong_ir.src.step, effecting, World.callEffect, Exit.bind, Exit.lift, andThen, ret, Outcome.ok,
    Refine.le] at hcs

/-- Dropping a call with effects that will return and can't unwind: its effects are still the caller's caller's to
see, so the traces differ in a world where it returns. -/
theorem effect_dropped_willreturn_wrong :
    ¬ Refines effect_dropped_willreturn_wrong_ir.src
      (fun x _ t => Talks.lift (effect_dropped_willreturn_wrong_ir.tgt x) t) := fun h => by
  obtain ⟨cs, hcs⟩ := h none (effecting fun _ => .ret []) [] default
  have hcs := hcs 1
  simp only [effect_dropped_willreturn_wrong_ir.src, effect_dropped_willreturn_wrong_ir.tgt, Talks.lift] at hcs
  rw [run_ret effect_dropped_willreturn_wrong_ir.tgt.step (by rfl), run.eq_1] at hcs
  simp [effect_dropped_willreturn_wrong_ir.src.step, effecting, World.callEffect, Exit.bind, Exit.lift, andThen, ret,
    Outcome.ok, Refine.le] at hcs

/-- Swapping two calls with effects: at 0 and 1, the traces differ in order. -/
theorem effect_reordered_wrong : ¬ Refines effect_reordered_wrong_ir.src effect_reordered_wrong_ir.tgt := fun h => by
  obtain ⟨cs, hcs⟩ := h (some 0#8) (some 1#8) (effecting fun _ => .ret []) [] default
  have hcs := hcs 2
  simp only [effect_reordered_wrong_ir.src, effect_reordered_wrong_ir.tgt] at hcs
  rw [run.eq_1, run.eq_1] at hcs
  simp [effect_reordered_wrong_ir.src.step, effect_reordered_wrong_ir.tgt.step, effecting, World.callEffect, Exit.bind,
    andThen, ret, Outcome.ok, Lanes.ofVal, Refine.le] at hcs

/-- Changing the argument of a call with effects from `x` to `x + 1`: at 0, the traces differ in it. -/
theorem effect_argument_changed_wrong :
    ¬ Refines effect_argument_changed_wrong_ir.src effect_argument_changed_wrong_ir.tgt := fun h => by
  obtain ⟨cs, hcs⟩ := h (some 0#8) (effecting fun _ => .ret []) [] default
  have hcs := hcs 1
  simp only [effect_argument_changed_wrong_ir.src, effect_argument_changed_wrong_ir.tgt] at hcs
  rw [run.eq_1, run.eq_1] at hcs
  simp [effect_argument_changed_wrong_ir.src.step, effect_argument_changed_wrong_ir.tgt.step, effecting,
    World.callEffect, Exit.bind, andThen, ret, Outcome.ok, Lanes.ofVal, Val.add, Refine.le] at hcs

/-- Calling a function with effects twice where the source calls it once: the target's trace has one more call. -/
theorem effect_twice_wrong : ¬ Refines effect_twice_wrong_ir.src effect_twice_wrong_ir.tgt := fun h => by
  obtain ⟨cs, hcs⟩ := h none (effecting fun _ => .ret []) [] default
  have hcs := hcs 2
  simp only [effect_twice_wrong_ir.src, effect_twice_wrong_ir.tgt] at hcs
  rw [run.eq_1, run.eq_1] at hcs
  simp [effect_twice_wrong_ir.src.step, effect_twice_wrong_ir.tgt.step, effecting, World.callEffect, Exit.bind,
    andThen, ret, Outcome.ok, Refine.le] at hcs

/-- Moving a call that only reads after a call with effects: in a world where it reads how many calls with effects came
before it, the source returns 0 however it picks, and the target 1. -/
theorem read_moved_across_effect_wrong :
    ¬ Refines read_moved_across_effect_wrong_ir.src read_moved_across_effect_wrong_ir.tgt := fun h => by
  obtain ⟨cs, hcs⟩ := h none (effecting (fun _ => .ret []) fun t _ _ => .ret [some t.length]) [] default
  have hcs := hcs 1
  simp only [read_moved_across_effect_wrong_ir.src, read_moved_across_effect_wrong_ir.tgt] at hcs
  rw [run.eq_1, run.eq_1] at hcs
  simp [read_moved_across_effect_wrong_ir.src.step, read_moved_across_effect_wrong_ir.tgt.step, effecting,
    World.callEffect, World.callRead, World.quiet, Exit.bind, andThen, ret, Outcome.ok, Lanes.toVal, Lanes.lane,
    Refine.le] at hcs

/-- Dropping a call with effects before undefined behavior: watched for no calls, the source is cut off at the call,
defined, and the target returns poison. -/
theorem effect_dropped_before_undefined_wrong :
    ¬ Refines effect_dropped_before_undefined_wrong_ir.src
      (fun x _ t => Talks.lift (effect_dropped_before_undefined_wrong_ir.tgt x) t) := fun h => by
  obtain ⟨cs, hcs⟩ := h none (effecting fun _ => .ret []) [] default
  have hcs := hcs 0
  simp only [effect_dropped_before_undefined_wrong_ir.src, effect_dropped_before_undefined_wrong_ir.tgt,
    Talks.lift] at hcs
  rw [run_ret effect_dropped_before_undefined_wrong_ir.tgt.step (by rfl), run.eq_1] at hcs
  simp [effect_dropped_before_undefined_wrong_ir.src.step, World.callEffect, Exit.bind, Exit.lift, andThen,
    ret, Outcome.ok, Refine.le] at hcs

/-- Dropping a call with effects before a loop that never ends: watched for no calls, the source is cut off at the
call, and the target runs forever. Neither finishes, and watching tells them apart. -/
theorem effect_dropped_before_loop_wrong :
    ¬ Refines effect_dropped_before_loop_wrong_ir.src
      (fun x _ t => Talks.lift (effect_dropped_before_loop_wrong_ir.tgt x) t) := fun h => by
  obtain ⟨cs, hcs⟩ := h none (effecting fun _ => .ret []) [] default
  have hcs := hcs 0
  have forever : run effect_dropped_before_loop_wrong_ir.tgt.step .entry = none :=
    run_forever (fun _ => True) (fun b _ => by cases b <;> exact ⟨_, rfl, trivial⟩) trivial
  simp only [effect_dropped_before_loop_wrong_ir.src, effect_dropped_before_loop_wrong_ir.tgt, Talks.lift,
    forever] at hcs
  rw [run.eq_1] at hcs
  simp [effect_dropped_before_loop_wrong_ir.src.step, World.callEffect, Exit.bind, Exit.lift, andThen,
    ret, Outcome.ok, Refine.le] at hcs

/-- A source that chooses between spinning silently and calling `@use` then returning, for a target that calls `@use`
then spins. In a world where `@use` returns, every prefix of the target's trace is one of some source run's, and no
one source run does what the target does: watched for no calls, the target is cut off and a spinning source isn't,
and watched for one, the target spins and a calling source returns. -/
theorem effect_then_spin_for_spin_or_return_wrong :
    ¬ Refines effect_then_spin_for_spin_or_return_wrong_ir.src effect_then_spin_for_spin_or_return_wrong_ir.tgt :=
  fun h => by
  obtain ⟨cs, hcs⟩ := h none (effecting fun _ => .ret []) [] default
  have tgt_spins : ∀ c w t n,
      run effect_then_spin_for_spin_or_return_wrong_ir.tgt.step (.spin c w t n) = none := fun c w t n =>
    run_forever (fun b => ∃ c w t n, b = .spin c w t n)
      (fun _ ⟨c, w, t, n, hb⟩ => ⟨.spin (c.sub 0) w t n, by subst hb; rfl, c.sub 0, w, t, n, rfl⟩)
      ⟨c, w, t, n, rfl⟩
  have src_spins : ∀ c w t n,
      run effect_then_spin_for_spin_or_return_wrong_ir.src.step (.spin c w t n) = none := fun c w t n =>
    run_forever (fun b => ∃ c w t n, b = .spin c w t n)
      (fun _ ⟨c, w, t, n, hb⟩ => ⟨.spin (c.sub 0) w t n, by subst hb; rfl, c.sub 0, w, t, n, rfl⟩)
      ⟨c, w, t, n, rfl⟩
  simp only [effect_then_spin_for_spin_or_return_wrong_ir.src, effect_then_spin_for_spin_or_return_wrong_ir.tgt]
    at hcs
  by_cases hb : BitVec.ofNat 1 (cs.pick 1) = 1#1
  · -- The source spins: watched for no calls, the target is cut off at its call.
    have h0 := hcs 0
    rw [run_jump effect_then_spin_for_spin_or_return_wrong_ir.src.step
      (by simp [effect_then_spin_for_spin_or_return_wrong_ir.src.step, Val.freeze, br, hb]; rfl), src_spins,
      run.eq_1] at h0
    simp [effect_then_spin_for_spin_or_return_wrong_ir.tgt.step, World.callEffect, Exit.bind, andThen, ret,
      Outcome.ok, Refine.le] at h0
  · -- The source calls and returns: watched for one call, the target spins after it.
    have h1 := hcs 1
    rw [run_jump effect_then_spin_for_spin_or_return_wrong_ir.src.step
      (by simp [effect_then_spin_for_spin_or_return_wrong_ir.src.step, Val.freeze, br, hb]; rfl), run.eq_1,
      run_jump effect_then_spin_for_spin_or_return_wrong_ir.tgt.step
      (by simp [effect_then_spin_for_spin_or_return_wrong_ir.tgt.step, effecting, World.callEffect, Exit.bind,
        andThen]; rfl), tgt_spins] at h1
    simp [effect_then_spin_for_spin_or_return_wrong_ir.src.step, effecting, World.callEffect, Exit.bind, andThen, ret,
      Outcome.ok, Refine.le] at h1
