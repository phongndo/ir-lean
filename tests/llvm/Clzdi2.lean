import CrtClzdi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__clzdi2`: its source gives `a != 0` as a precondition. -/
theorem clzdi2_correct (a : BitVec 64) (h : a ≠ 0#64) :
    CrtClzdi2._clzdi2 (some a) =
      IRLean.Outcome.ok (some (a.clz.setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtClzdi2._clzdi2
  all_goals llvm_close

end Llvm
