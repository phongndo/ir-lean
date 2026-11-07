import CrtPopcountsi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__popcountsi2`: the number of set bits. -/
theorem popcountsi2_correct (a : BitVec 32) :
    CrtPopcountsi2._popcountsi2 (some a) =
      IRLean.Outcome.ok (some (a.cpop.setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtPopcountsi2._popcountsi2
  all_goals llvm_close

end Llvm
