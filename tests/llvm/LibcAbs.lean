import LibcGenAbs
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified llvm-libc, and checks this fails on an injected bug. -/

namespace Llvm

/-- `abs`: the absolute value, for anything but the minimum, which C leaves undefined. -/
theorem abs_correct (c : BitVec 32) (h : c ≠ BitVec.intMin 32) :
    LibcGenAbs._ZN11__llvm_libc3absEi (some c) = IRLean.Outcome.ok (some (if c.msb then -c else c)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec LibcGenAbs._ZN11__llvm_libc3absEi
  all_goals llvm_close

end Llvm
