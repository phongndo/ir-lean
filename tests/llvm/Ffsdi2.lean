import CrtFfsdi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__ffsdi2`: one more than the index of the lowest set bit, or 0 if there isn't one. -/
theorem ffsdi2_correct (a : BitVec 64) :
    CrtFfsdi2._ffsdi2 (some a) =
      IRLean.Outcome.ok (some (if a = 0#64 then 0#32 else (a.ctz + 1#64).setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtFfsdi2._ffsdi2
  all_goals llvm_close

end Llvm
