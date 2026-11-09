import IRLean.Int
import Std.Tactic.BVDecide

/-! A lemma only `bv_decide` proves, which rests on an axiom `bv_decide` adds: `store.py add` has to refuse it with
`nonstandard_axiom`, as rule 1 says, though `tests/check_axioms.lean` allows that axiom in a proof. Its statement has to
reach the SAT solver: one `bv_decide` normalizes away, such as `x * 8 = x <<< 3`, rests on the standard axioms. -/

namespace LemmaStore.Test

/-- Adding is `xor` plus the carries, shifted. -/
theorem add_eq_xor_carry_i16 (x y : BitVec 16) : (x ^^^ y) + ((x &&& y) <<< 1) = x + y := by bv_decide

end LemmaStore.Test
