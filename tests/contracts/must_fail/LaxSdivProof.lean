import ContractPoison

/-! Must fail to check, with an error that isn't a resource limit: the lax `sdiv` has less undefined behavior than
LangRef, so no proof that it meets `PoisonUB` can go through. `tests/contracts.sh` runs this. -/

open IRLean IRLean.Contract IRLean.Contract.Test

theorem lax_sdiv_meets_contract : PoisonUB (w := 8) sdivLax := by
  refine ⟨fun b => ?_, fun a => ?_, fun b => ?_, fun a => ?_⟩ <;>
    cases ‹Val 8› <;> simp_all [sdivLax, Val.sdiv, Val.divOverflows, IsUB, Outcome.ub, Outcome.ok]
