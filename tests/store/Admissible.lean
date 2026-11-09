import IRLean.Generic.Bitwise

/-! A new lemma that meets the bar, which `store.py add --dry-run` has to accept as a candidate, so the must-refuse
tests can't pass by the checker refusing everything. It's `IRLean.Generic.and_allOnes` with its constant lifted into a
side condition, the way a general lemma states one, with a counterexample for that condition and a witness. -/

namespace LemmaStore.Test

open IRLean

theorem and_eq_allOnes {w : Nat} (a : Val w) {c : BitVec w} (hc : c = BitVec.allOnes w) : Val.and a (some c) = a := by
  subst hc; exact IRLean.Generic.and_allOnes a

/-- `and 1, 0` is `0` in `i1`, not `1`. -/
theorem _root_.LemmaStore.Counter.LemmaStore.Test.and_eq_allOnes.drop_hc :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w}, Val.and a (some c) = a :=
  fun h => absurd (@h 1 (some 1#1) 0#1) (by decide)

theorem _root_.LemmaStore.Counter.LemmaStore.Test.and_eq_allOnes.sat :
    ∃ (w : Nat) (_ : Val w) (c : BitVec w), c = BitVec.allOnes w :=
  ⟨1, none, BitVec.allOnes 1, rfl⟩

end LemmaStore.Test
