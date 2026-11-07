import CrtCtzsi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__ctzsi2`. Its source says `a != 0`, but it gives 32 for 0 too. -/
theorem ctzsi2_correct (a : BitVec 32) :
    CrtCtzsi2._ctzsi2 (some a) =
      IRLean.Outcome.ok (some (a.ctz)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtCtzsi2._ctzsi2
  all_goals llvm_close

end Llvm
