import CrtClzsi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__clzsi2`. Its source says `a != 0`, but it gives 32 for 0 too. -/
theorem clzsi2_correct (a : BitVec 32) :
    CrtClzsi2._clzsi2 (some a) =
      IRLean.Outcome.ok (some (a.clz)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtClzsi2._clzsi2
  all_goals llvm_close

end Llvm
