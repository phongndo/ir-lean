import CrtFfsti2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__ffsti2`: one more than the index of the lowest set bit, or 0 if there isn't one. -/
theorem ffsti2_correct (a : BitVec 128) :
    CrtFfsti2._ffsti2 (some a) =
      IRLean.Outcome.ok (some (if a = 0#128 then 0#32 else (a.ctz + 1#128).setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtFfsti2._ffsti2
  all_goals llvm_close

end Llvm
