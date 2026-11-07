import CrtSubvdi3
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

set_option linter.unusedSimpArgs false

namespace Llvm

/-- `__subvdi3`: the difference, or an abort if it overflows. -/
theorem subvdi3_correct (a b : BitVec 64) :
    CrtSubvdi3._subvdi3 (some a) (some b) =
      if a.ssubOverflow b = true then IRLean.Outcome.stop .noReturnCall else IRLean.Outcome.ok (some (a - b)) := by
  by_cases h : a.ssubOverflow b = true
  · simp only [h, ite_true, IRLean.Outcome.stop]
    llvm_exec CrtSubvdi3._subvdi3
    all_goals llvm_close
  · simp only [h, ite_false, IRLean.Outcome.ok]
    llvm_exec CrtSubvdi3._subvdi3
    all_goals llvm_close

end Llvm
