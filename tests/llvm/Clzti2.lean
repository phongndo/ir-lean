import CrtClzti2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__clzti2`: its source gives `a != 0` as a precondition. -/
theorem clzti2_correct (a : BitVec 128) (h : a ≠ 0#128) :
    CrtClzti2._clzti2 (some a) =
      IRLean.Outcome.ok (some (a.clz.setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtClzti2._clzti2
  all_goals llvm_close

end Llvm
