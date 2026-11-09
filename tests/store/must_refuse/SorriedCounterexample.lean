import IRLean.Generic.Bitwise

/-! `Admissible.lean`'s lemma, with a counterexample proved by `sorry`, which shows nothing: `store.py add` has to
refuse it with `hypothesis_unwitnessed`, since rule 3 needs each counterexample to be a theorem in its own right. -/

namespace LemmaStore.Test

open IRLean

theorem and_eq_allOnes' {w : Nat} (a : Val w) {c : BitVec w} (hc : c = BitVec.allOnes w) : Val.and a (some c) = a := by
  subst hc; exact IRLean.Generic.and_allOnes a

theorem _root_.LemmaStore.Counter.LemmaStore.Test.and_eq_allOnes'.drop_hc :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w}, Val.and a (some c) = a :=
  sorry

theorem _root_.LemmaStore.Counter.LemmaStore.Test.and_eq_allOnes'.sat :
    ∃ (w : Nat) (_ : Val w) (c : BitVec w), c = BitVec.allOnes w :=
  ⟨1, none, BitVec.allOnes 1, rfl⟩

end LemmaStore.Test
