import CrtParitysi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__paritysi2`: 1 if an odd number of bits are set. -/
theorem paritysi2_correct (a : BitVec 32) :
    CrtParitysi2._paritysi2 (some a) =
      IRLean.Outcome.ok (some ((a.cpop &&& 1#32).setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtParitysi2._paritysi2
  all_goals llvm_close

end Llvm
