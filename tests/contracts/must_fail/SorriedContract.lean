import ContractPoison

/-! Compiles, but must fail the axiom check: `sorry` is an axiom outside the standard three. `tests/contracts.sh`
compiles this without warnings as errors, so only the axiom check can stop it. -/

open IRLean IRLean.Contract IRLean.Contract.Test

theorem lax_sdiv_meets_contract : PoisonUB (w := 8) sdivLax := sorry
