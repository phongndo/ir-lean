import IRLean.Int
import Std.Tactic.BVDecide

/-! A lemma only `bv_decide` proves, which rests on an axiom `bv_decide` adds: `store.py add` has to refuse it with
`nonstandard_axiom`, as rule 1 says, though `tests/check_axioms.lean` allows that axiom in a proof. -/

namespace LemmaStore.Test

theorem mul_eight_i16 (x : BitVec 16) : x * 8#16 = x <<< 3 := by bv_decide

end LemmaStore.Test
