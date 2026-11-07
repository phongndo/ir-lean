import CrtFfssi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__ffssi2`: one more than the index of the lowest set bit, or 0 if there isn't one. -/
theorem ffssi2_correct (a : BitVec 32) :
    CrtFfssi2._ffssi2 (some a) =
      IRLean.Outcome.ok (some (if a = 0#32 then 0#32 else (a.ctz + 1#32).setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtFfssi2._ffssi2
  all_goals llvm_close

end Llvm
