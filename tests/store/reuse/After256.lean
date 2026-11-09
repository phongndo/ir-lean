import Src256
import Tgt256
import LemmaStore

/-! The reuse example, proved from the store: the run of each side, then `IRLean.Generic.lshr_shl_nuw_refines`, a
stored lemma for every width, and `IRLean.Refine.outcome_ok_ok`. The proof is the same at every width, and rests on
the standard axioms only. `docs/lemma-store.md` compares it with `Before256.lean`. -/

open IRLean

theorem round_trip_256 : Refines Src256.f Tgt256.f := by
  intro x s
  simp only [Src256.f, Tgt256.f]
  rw [run_ret Src256.f.step (b := .bb1 x s) (r := Val.lshr (Val.shl x s true false) s) rfl,
    run_ret Tgt256.f.step (b := .bb1 x) (r := x) rfl]
  exact (Refine.outcome_ok_ok _ _).2 (Generic.lshr_shl_nuw_refines x s false false)
