import CrtCmpdi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__cmpdi2`: 0, 1 or 2 if `a` is less than, equal to or greater than `b`. -/
theorem cmpdi2_correct (a b : BitVec 64) :
    CrtCmpdi2._cmpdi2 (some a) (some b) =
      IRLean.Outcome.ok (some (if BitVec.slt a b then 0#32 else if a = b then 1#32 else 2#32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtCmpdi2._cmpdi2
  all_goals llvm_close

end Llvm
