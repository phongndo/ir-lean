import CrtCtzti2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__ctzti2`: its source gives `a != 0` as a precondition. -/
theorem ctzti2_correct (a : BitVec 128) (h : a ≠ 0#128) :
    CrtCtzti2._ctzti2 (some a) =
      IRLean.Outcome.ok (some (a.ctz.setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtCtzti2._ctzti2
  all_goals llvm_close

end Llvm
