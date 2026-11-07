import CrtLshrti3
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__lshrti3`: its source gives `0 <= b < 128` as a precondition. -/
theorem lshrti3_correct (a : BitVec 128) (b : BitVec 32) (h : b < 128#32) :
    CrtLshrti3._lshrti3 (some a) (some b) =
      IRLean.Outcome.ok (some (a >>> b)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtLshrti3._lshrti3
  all_goals llvm_close

end Llvm
