import LibcGenToascii
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified llvm-libc, and checks this fails on an injected bug. -/

namespace Llvm

/-- `toascii`: the low seven bits. -/
theorem toascii_correct (c : BitVec 32) :
    LibcGenToascii._ZN11__llvm_libc7toasciiEi (some c) = IRLean.Outcome.ok (some (c &&& 127#32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec LibcGenToascii._ZN11__llvm_libc7toasciiEi
  all_goals llvm_close

end Llvm
