import LibcGenIsupper
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified llvm-libc, and checks this fails on an injected bug. -/

namespace Llvm

/-- `isupper`: for any `int`, whether it's an uppercase ASCII letter. -/
theorem isupper_correct (c : BitVec 32) :
    LibcGenIsupper._ZN11__llvm_libc7isupperEi (some c) = IRLean.Outcome.ok (some (if 65#32 ≤ c ∧ c ≤ 90#32 then 1#32 else 0#32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec LibcGenIsupper._ZN11__llvm_libc7isupperEi
  all_goals llvm_close

end Llvm
