import Src64
import Tgt64
import LemmaStore

/-! The reuse example, proved from the store: the run of each side, then `IRLean.Generic.lshr_shl_nuw_refines`, a
stored lemma for every width, and `IRLean.Refine.outcome_ok_ok`. The proof is the same at every width, and rests on
the standard axioms only. `docs/lemma-store.md` compares it with `Before64.lean`. -/

open IRLean

theorem round_trip_64 : Refines Src64.f Tgt64.f := by
  intro x s
  simp only [Src64.f, Tgt64.f]
  rw [run_ret Src64.f.step (b := .bb1 x s) (r := Val.lshr (Val.shl x s true false) s) rfl,
    run_ret Tgt64.f.step (b := .bb1 x) (r := x) rfl]
  exact (Refine.outcome_ok_ok _ _).2 (Generic.lshr_shl_nuw_refines x s false false)
