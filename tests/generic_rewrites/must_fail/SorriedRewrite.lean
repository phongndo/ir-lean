import IRLean.Generic.Arith

open IRLean IRLean.Generic

/-- A rewrite with no proof. It compiles, and the axiom check `tests/generic_rewrites.sh` runs has to refuse it. -/
theorem sub_self_eq {w : Nat} (a : Val w) : Val.sub a a = some 0#w := sorry
