import CrtAshrdi3
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__ashrdi3`: its source gives `0 <= b < 64` as a precondition. -/
theorem ashrdi3_correct (a : BitVec 64) (b : BitVec 32) (h : b < 64#32) :
    CrtAshrdi3._ashrdi3 (some a) (some b) =
      IRLean.Outcome.ok (some (a.sshiftRight' b)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtAshrdi3._ashrdi3
  all_goals llvm_close

end Llvm
