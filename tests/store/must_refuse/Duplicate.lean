import IRLean.Generic.Bitwise

/-! `IRLean.Generic.xor_zero`, with its variables renamed and its equation the other way round: `store.py add` has
to refuse it with `duplicate`, since normalization gives it the stored lemma's key. -/

namespace LemmaStore.Test

open IRLean

theorem xor_zero_again {n : Nat} (v : Val n) : v = Val.xor v (some 0#n) := (IRLean.Generic.xor_zero v).symm

end LemmaStore.Test
