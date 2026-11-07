import CrtCtzdi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__ctzdi2`: its source gives `a != 0` as a precondition. -/
theorem ctzdi2_correct (a : BitVec 64) (h : a ≠ 0#64) :
    CrtCtzdi2._ctzdi2 (some a) =
      IRLean.Outcome.ok (some (a.ctz.setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtCtzdi2._ctzdi2
  all_goals llvm_close

end Llvm
