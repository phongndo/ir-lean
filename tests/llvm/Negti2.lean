import CrtNegti2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__negti2`: the two's complement negation, which wraps. -/
theorem negti2_correct (a : BitVec 128) :
    CrtNegti2._negti2 (some a) =
      IRLean.Outcome.ok (some (-a)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtNegti2._negti2
  all_goals llvm_close

end Llvm
