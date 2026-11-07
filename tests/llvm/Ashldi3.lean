import CrtAshldi3
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__ashldi3`: its source gives `0 <= b < 64` as a precondition. -/
theorem ashldi3_correct (a : BitVec 64) (b : BitVec 32) (h : b < 64#32) :
    CrtAshldi3._ashldi3 (some a) (some b) =
      IRLean.Outcome.ok (some (a <<< b)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtAshldi3._ashldi3
  all_goals llvm_close

end Llvm
