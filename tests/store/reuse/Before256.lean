import Src256
import Tgt256
import Std.Tactic.BVDecide

/-! The reuse example, proved without the store: `docs/lemma-store.md` compares it with `After256.lean`. Each case
of the two runs is a bit-vector problem at width 256, which `bv_decide` hands to a SAT solver, so the proof holds at
this width only and rests on the axioms `bv_decide` adds. At this width the solver can take longer than its default
10 s, so it gets 300. -/

open IRLean

theorem round_trip_256 : Refines Src256.f Tgt256.f := by
  intro x s
  simp only [Src256.f, Tgt256.f]
  rw [run_ret Src256.f.step (b := .bb1 x s) (r := Val.lshr (Val.shl x s true false) s) rfl,
    run_ret Tgt256.f.step (b := .bb1 x) (r := x) rfl]
  refine (Refine.outcome_ok_ok _ _).2 ((Refine.val_iff _ _).2 ?_)
  cases x with
  | none => exact .inl rfl
  | some x =>
    cases s with
    | none => exact .inl rfl
    | some s =>
      simp only [Val.shl, Val.lshr, Val.shiftOk, Bool.true_and, Bool.false_and]
      split <;> (try split) <;> (try split) <;> simp_all <;> bv_decide (config := { timeout := 300 })
