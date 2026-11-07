import CrtNegdi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__negdi2`: the two's complement negation, which wraps. -/
theorem negdi2_correct (a : BitVec 64) :
    CrtNegdi2._negdi2 (some a) =
      IRLean.Outcome.ok (some (-a)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtNegdi2._negdi2
  all_goals llvm_close

end Llvm
