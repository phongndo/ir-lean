import LibcGenIsalnum
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified llvm-libc, and checks this fails on an injected bug.

`internal::isalnum` is an inline function, so its definition is `linkonce_odr`, and this is about the copy `isalnum.cpp`
compiles. The public `isalnum`, which calls it, is left out: the copy that call runs is whichever the linker keeps. -/

namespace Llvm

open LibcGenIsalnum

/-- A `switch` whose cases all go to one place is one `if`. -/
private theorem ite_same_or {α : Type} (p q : Bool) (a b : α) :
    (if p = true then a else if q = true then a else b) = if (p || q) = true then a else b := by
  cases p <;> cases q <;> rfl

/-- `internal::isalnum`: for any `char`, whether it's an ASCII letter or digit. -/
theorem internal_isalnum_correct (c : BitVec 8) :
    _ZN11__llvm_libc8internal7isalnumEc (some c) =
      IRLean.Outcome.ok
        (some (if 97#8 ≤ c ∧ c ≤ 122#8 ∨ 65#8 ≤ c ∧ c ≤ 90#8 ∨ 48#8 ≤ c ∧ c ≤ 57#8 then 1#1 else 0#1)) := by
  -- The entry block is a `switch` with 62 cases, all going to the same block.
  have entry : _ZN11__llvm_libc8internal7isalnumEc.step (.entry (some c)) = IRLean.jump
      (if 97#8 ≤ c ∧ c ≤ 122#8 ∨ 65#8 ≤ c ∧ c ≤ 90#8 ∨ 48#8 ≤ c ∧ c ≤ 57#8 then .return_1 (some 1#1)
        else .sw_default) := by
    simp only [_ZN11__llvm_libc8internal7isalnumEc.step, IRLean.sw, ite_same_or]
    rw [apply_ite IRLean.jump]
    split <;> split <;> first | rfl | (exfalso; bv_decide)
  simp only [IRLean.Outcome.ok, _ZN11__llvm_libc8internal7isalnumEc, IRLean.noundef_some]
  rw [IRLean.run, entry]
  by_cases h : 97#8 ≤ c ∧ c ≤ 122#8 ∨ 65#8 ≤ c ∧ c ≤ 90#8 ∨ 48#8 ≤ c ∧ c ≤ 57#8
  · simp only [h, ite_true, IRLean.jump, IRLean.Outcome.ok]
    llvm_step _ZN11__llvm_libc8internal7isalnumEc.step
  · simp only [h, ite_false, IRLean.jump, IRLean.Outcome.ok]
    llvm_step _ZN11__llvm_libc8internal7isalnumEc.step
    llvm_step _ZN11__llvm_libc8internal7isalnumEc.step

end Llvm
