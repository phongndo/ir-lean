import CrtNegvti2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__negvti2`: the negation, or an abort if there isn't one. -/
theorem negvti2_correct (a : BitVec 128) :
    CrtNegvti2._negvti2 (some a) =
      if a = BitVec.intMin 128 then IRLean.Outcome.stop .noReturnCall else IRLean.Outcome.ok (some (-a)) := by
  by_cases h : a = BitVec.intMin 128
  · simp only [h, ite_true, IRLean.Outcome.stop]
    llvm_exec CrtNegvti2._negvti2
    all_goals llvm_close
  · simp only [h, ite_false, IRLean.Outcome.ok]
    llvm_exec CrtNegvti2._negvti2
    all_goals llvm_close

end Llvm
