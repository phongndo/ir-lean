import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Unfolds ir-lean's semantics, for proofs about emitted code: `simp [llvm, foo.step]`. -/
register_simp_attr llvm

/-- Computes ir-lean's operations on values known not to be poison: `simp only [llvm_val, ...]`. -/
register_simp_attr llvm_val
