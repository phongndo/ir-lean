import LibcGenIsdigit
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified llvm-libc, and checks this fails on an injected bug. -/

namespace Llvm

/-- `isdigit`: for any `int`, whether it's an ASCII digit. -/
theorem isdigit_correct (c : BitVec 32) :
    LibcGenIsdigit._ZN11__llvm_libc7isdigitEi (some c) = IRLean.Outcome.ok (some (if 48#32 ≤ c ∧ c ≤ 57#32 then 1#32 else 0#32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec LibcGenIsdigit._ZN11__llvm_libc7isdigitEi
  all_goals llvm_close

end Llvm
