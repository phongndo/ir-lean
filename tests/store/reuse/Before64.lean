import Src64
import Tgt64
import Std.Tactic.BVDecide

/-! The reuse example, proved without the store: `docs/lemma-store.md` compares it with `After64.lean`. Each case
of the two runs is a bit-vector problem at width 64, which `bv_decide` hands to a SAT solver, so the proof holds at
this width only and rests on the axioms `bv_decide` adds. -/

open IRLean

theorem round_trip_64 : Refines Src64.f Tgt64.f := by
  intro x s
  simp only [Src64.f, Tgt64.f]
  rw [run_ret Src64.f.step (b := .bb1 x s) (r := Val.lshr (Val.shl x s true false) s) rfl,
    run_ret Tgt64.f.step (b := .bb1 x) (r := x) rfl]
  refine (Refine.outcome_ok_ok _ _).2 ((Refine.val_iff _ _).2 ?_)
  cases x with
  | none => exact .inl rfl
  | some x =>
    cases s with
    | none => exact .inl rfl
    | some s =>
      simp only [Val.shl, Val.lshr, Val.shiftOk, Bool.true_and, Bool.false_and]
      split <;> (try split) <;> (try split) <;> simp_all <;> bv_decide
