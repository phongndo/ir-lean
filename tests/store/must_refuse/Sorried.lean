import IRLean.Int

/-! A lemma with no proof: `store.py add` has to refuse it with `sorry`, which rule 1 rules out. -/

namespace LemmaStore.Test

open IRLean

theorem and_comm_sorried {w : Nat} (a b : Val w) : Val.and a b = Val.and b a := sorry

end LemmaStore.Test
