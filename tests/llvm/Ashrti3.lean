import CrtAshrti3
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__ashrti3`: its source gives `0 <= b < 128` as a precondition. -/
theorem ashrti3_correct (a : BitVec 128) (b : BitVec 32) (h : b < 128#32) :
    CrtAshrti3._ashrti3 (some a) (some b) =
      IRLean.Outcome.ok (some (a.sshiftRight' b)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtAshrti3._ashrti3
  all_goals llvm_close

end Llvm
