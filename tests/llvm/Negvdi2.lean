import CrtNegvdi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__negvdi2`: the negation, or an abort if there isn't one. -/
theorem negvdi2_correct (a : BitVec 64) :
    CrtNegvdi2._negvdi2 (some a) =
      if a = BitVec.intMin 64 then IRLean.Outcome.stop .noReturnCall else IRLean.Outcome.ok (some (-a)) := by
  by_cases h : a = BitVec.intMin 64
  · simp only [h, ite_true, IRLean.Outcome.stop]
    llvm_exec CrtNegvdi2._negvdi2
    all_goals llvm_close
  · simp only [h, ite_false, IRLean.Outcome.ok]
    llvm_exec CrtNegvdi2._negvdi2
    all_goals llvm_close

end Llvm
