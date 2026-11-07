import LibcGenIslower
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified llvm-libc, and checks this fails on an injected bug. -/

namespace Llvm

/-- `islower`: for any `int`, whether it's a lowercase ASCII letter. -/
theorem islower_correct (c : BitVec 32) :
    LibcGenIslower._ZN11__llvm_libc7islowerEi (some c) = IRLean.Outcome.ok (some (if 97#32 ≤ c ∧ c ≤ 122#32 then 1#32 else 0#32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec LibcGenIslower._ZN11__llvm_libc7islowerEi
  all_goals llvm_close

end Llvm
