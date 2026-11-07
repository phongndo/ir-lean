import CrtAbsvsi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

/-- `__absvsi2`: the absolute value, or an abort if there isn't one. -/
theorem absvsi2_correct (a : BitVec 32) :
    CrtAbsvsi2._absvsi2 (some a) =
      if a = BitVec.intMin 32 then IRLean.Outcome.stop .noReturnCall else IRLean.Outcome.ok (some (if a.msb then -a else a)) := by
  by_cases h : a = BitVec.intMin 32
  · simp only [h, ite_true, IRLean.Outcome.stop]
    llvm_exec CrtAbsvsi2._absvsi2
    all_goals llvm_close
  · simp only [h, ite_false, IRLean.Outcome.ok]
    llvm_exec CrtAbsvsi2._absvsi2
    all_goals llvm_close

end Llvm
