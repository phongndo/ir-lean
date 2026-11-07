import LibcGenIsgraph
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified llvm-libc, and checks this fails on an injected bug. -/

namespace Llvm

/-- `isgraph`: for any `int`, whether it's a printable ASCII character other than a space. -/
theorem isgraph_correct (c : BitVec 32) :
    LibcGenIsgraph._ZN11__llvm_libc7isgraphEi (some c) = IRLean.Outcome.ok (some (if 33#32 ≤ c ∧ c ≤ 126#32 then 1#32 else 0#32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec LibcGenIsgraph._ZN11__llvm_libc7isgraphEi
  all_goals llvm_close

end Llvm
