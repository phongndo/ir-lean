import LibcGenIsascii
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified llvm-libc, and checks this fails on an injected bug. -/

namespace Llvm

/-- `isascii`: for any `int`, whether it's in the ASCII range. -/
theorem isascii_correct (c : BitVec 32) :
    LibcGenIsascii._ZN11__llvm_libc7isasciiEi (some c) = IRLean.Outcome.ok (some (if c ≤ 127#32 then 1#32 else 0#32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec LibcGenIsascii._ZN11__llvm_libc7isasciiEi
  all_goals llvm_close

end Llvm
