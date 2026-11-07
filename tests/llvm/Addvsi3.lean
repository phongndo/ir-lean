import CrtAddvsi3
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

set_option linter.unusedSimpArgs false

namespace Llvm

/-- `__addvsi3`: the sum, or an abort if it overflows. -/
theorem addvsi3_correct (a b : BitVec 32) :
    CrtAddvsi3._addvsi3 (some a) (some b) =
      if a.saddOverflow b = true then IRLean.Outcome.stop .noReturnCall else IRLean.Outcome.ok (some (a + b)) := by
  by_cases h : a.saddOverflow b = true
  · simp only [h, ite_true, IRLean.Outcome.stop]
    llvm_exec CrtAddvsi3._addvsi3
    all_goals llvm_close
  · simp only [h, ite_false, IRLean.Outcome.ok]
    llvm_exec CrtAddvsi3._addvsi3
    all_goals llvm_close

end Llvm
