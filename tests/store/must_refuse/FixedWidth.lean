import IRLean.Generic.Arith

/-! `add x, 0` to `x` at `i8` alone, where a statement for every width makes sense: `store.py add` has to refuse it
with `fixed_width`, which rule 2 rules out. -/

namespace LemmaStore.Test

open IRLean

theorem add_zero_i8 (a : Val 8) : Val.add a (some 0#8) true true = a := IRLean.Generic.add_zero a true true

end LemmaStore.Test
