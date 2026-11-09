import IRLean.Generic.Arith

/-! A lemma with a hypothesis nothing needs: at width zero, `udiv` by `1` is undefined, and anything refines that.
A counterexample can't exist, and none is given, so `store.py add` has to refuse it with `hypothesis_unwitnessed`.
Its witness is given, so that's the only thing missing. -/

namespace LemmaStore.Test

open IRLean

theorem udiv_one_refines {w : Nat} (a : Val w) (exact : Bool) (hw : 0 < w) :
    Refines (Val.udiv a (some 1#w) exact) (Outcome.ok a) := by
  rw [IRLean.Generic.udiv_one a exact hw]
  exact (Refine.outcome_ok_ok _ _).2 (Refines.refl a)

theorem _root_.LemmaStore.Counter.LemmaStore.Test.udiv_one_refines.sat :
    ∃ (w : Nat) (_ : Val w) (_ : Bool), 0 < w :=
  ⟨1, none, false, Nat.one_pos⟩

end LemmaStore.Test
