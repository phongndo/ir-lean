import CrtAddvti3
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

set_option linter.unusedSimpArgs false

namespace Llvm

/-- `__addvti3`: the sum, or an abort if it overflows. -/
theorem addvti3_correct (a b : BitVec 128) :
    CrtAddvti3._addvti3 (some a) (some b) =
      if a.saddOverflow b = true then IRLean.Outcome.stop .noReturnCall else IRLean.Outcome.ok (some (a + b)) := by
  by_cases h : a.saddOverflow b = true
  · simp only [h, ite_true, IRLean.Outcome.stop]
    llvm_exec CrtAddvti3._addvti3
    all_goals llvm_close
  · simp only [h, ite_false, IRLean.Outcome.ok]
    llvm_exec CrtAddvti3._addvti3
    all_goals llvm_close

end Llvm
