import LibcGenLabs
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified llvm-libc, and checks this fails on an injected bug. -/

namespace Llvm

/-- `labs`: the absolute value, for anything but the minimum, which C leaves undefined. -/
theorem labs_correct (c : BitVec 64) (h : c ≠ BitVec.intMin 64) :
    LibcGenLabs._ZN11__llvm_libc4labsEl (some c) = IRLean.Outcome.ok (some (if c.msb then -c else c)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec LibcGenLabs._ZN11__llvm_libc4labsEl
  all_goals llvm_close

end Llvm
