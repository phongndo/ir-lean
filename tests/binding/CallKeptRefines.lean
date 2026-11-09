import Fx.Src
import Fx.Tgt

/-! tests/binding.py's certificate: `instcombine` rewrote `0 - (0 - x)` to `x` around a call outside the module with
effects, which stays. Both functions take the world and the trace before them, and return `Talks`: watched for no
more calls than the trace has, both are cut off at the call, and past it, both make the same call, so they end with
the same trace, and the target's result refines the source's. See docs/calls.md. -/

open IRLean

theorem Fx.cert : IRLean.Refines Fx.Src.f Fx.Tgt.f := by
  intro x w t ct
  refine ⟨ct, fun n => ?_⟩
  cases x with
  | none => exact Refine.outcome_ub _ _
  | some v =>
    simp only [Fx.Src.f, Fx.Tgt.f, noundef]
    rw [run.eq_1, run.eq_1]
    simp only [Fx.Src.f.step, Fx.Tgt.f.step, World.callEffect, Exit.bind]
    by_cases hn : n ≤ t.length
    · simp only [hn, ite_true, andThen, ret, Outcome.ok]
      exact ⟨_, rfl, rfl⟩
    · simp only [hn, ite_false]
      cases w.effect (⟨"use", [("i8", Lanes.ofVal (Val.sub (some 0#8) (some v)))]⟩ :: t) <;>
        simp only [andThen, ret, Outcome.ok, Outcome.ub, Bool.false_eq_true, ite_false]
      · refine ⟨_, rfl, ⟨_, rfl, ?_⟩⟩
        simp only [Val.sub, Bool.false_and, Bool.or_self, Bool.false_eq_true, ite_false, Refine.val_some,
          Option.some.injEq]
        bv_decide
      all_goals first | trivial | exact ⟨_, rfl, Refine.Reflexive.refl _⟩
