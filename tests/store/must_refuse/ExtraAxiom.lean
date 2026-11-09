import IRLean.Int

/-! A lemma proved by an axiom of its own: `store.py add` has to refuse it with `nonstandard_axiom`, which rule 1
rules out. Lean accepts the proof. -/

namespace LemmaStore.Test

open IRLean

axiom trust_me {p : Prop} : p

theorem and_comm_trusted {w : Nat} (a b : Val w) : Val.and a b = Val.and b a := trust_me

end LemmaStore.Test
