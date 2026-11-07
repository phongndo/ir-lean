import LibcGenIscntrl
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified llvm-libc, and checks this fails on an injected bug. -/

namespace Llvm

/-- `iscntrl`: for any `int`, whether it's an ASCII control character. -/
theorem iscntrl_correct (c : BitVec 32) :
    LibcGenIscntrl._ZN11__llvm_libc7iscntrlEi (some c) = IRLean.Outcome.ok (some (if c < 32#32 ∨ c = 127#32 then 1#32 else 0#32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec LibcGenIscntrl._ZN11__llvm_libc7iscntrlEi
  all_goals llvm_close

end Llvm
