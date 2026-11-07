import LibcGenIsblank
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified llvm-libc, and checks this fails on an injected bug. -/

namespace Llvm

/-- `isblank`: for any `int`, whether it's a space or a tab. -/
theorem isblank_correct (c : BitVec 32) :
    LibcGenIsblank._ZN11__llvm_libc7isblankEi (some c) = IRLean.Outcome.ok (some (if c = 32#32 ∨ c = 9#32 then 1#32 else 0#32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec LibcGenIsblank._ZN11__llvm_libc7isblankEi
  all_goals llvm_close

end Llvm
