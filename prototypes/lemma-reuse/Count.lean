import Bits

/-! Seed lemmas for `prototypes/lemma-reuse`: a value's set bits, counted field by field.

These hold at every width, and are proved once, by induction, on top of `tests/llvm/Bits.lean`. The lemmas `lemmas.py`
mines are about fixed widths, are proved by `bv_decide`, and lean on these to connect a population count to what a
field-by-field computation leaves behind. -/

namespace LemmaReuse

open Llvm.Bits

variable {w : Nat}

/-- The number of set bits in the `k`-bit field at `k * i`. -/
def field (x : BitVec w) (k i : Nat) : BitVec k := (x.extractLsb' (k * i) k).cpop

/-- The counts of the first `n` fields, added in `k` bits. -/
def fieldSum (x : BitVec w) (k : Nat) : Nat → BitVec k
  | 0 => 0
  | n + 1 => fieldSum x k n + field x k n

theorem count_le (x : BitVec w) (lo n : Nat) : count x lo n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [count]
    cases x.getLsbD (lo + n) <;> simp <;> omega

theorem toNat_field (x : BitVec w) (k i : Nat) : (field x k i).toNat = count x (k * i) k := by
  rw [field, toNat_cpop_eq, count_extract x _ k k (Nat.le_refl k)]

/-- A field holds at most `k` set bits. -/
theorem field_le (x : BitVec w) (k i : Nat) : field x k i ≤ BitVec.ofNat k k := by
  have h1 := toNat_field x k i
  have h2 := count_le x (k * i) k
  have h3 : k < 2 ^ k := Nat.lt_two_pow_self
  simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3]
  omega

theorem toNat_fieldSum (x : BitVec w) (k n : Nat) (h : k * n < 2 ^ k) :
    (fieldSum x k n).toNat = count x 0 (k * n) := by
  induction n with
  | zero => simp [fieldSum, count]
  | succ n ih =>
    have h' : k * n < 2 ^ k := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left k (Nat.le_succ n)) h
    have hsplit := count_split x 0 (k * n) k
    rw [Nat.zero_add] at hsplit
    have hle := count_le x 0 (k * (n + 1))
    rw [fieldSum, BitVec.toNat_add, ih h', toNat_field, ← hsplit, ← Nat.mul_succ]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle h)

/-- A population count is the sum of its fields' counts, when the total fits in a field. -/
theorem cpop_fieldSum (x : BitVec w) (k n r : Nat) (hw : w = k * n) (h : w < 2 ^ k) :
    x.cpop.setWidth r = (fieldSum x k n).setWidth r := by
  apply BitVec.eq_of_toNat_eq
  have h' : k * n < 2 ^ k := by rw [← hw]; exact h
  simp only [BitVec.toNat_setWidth]
  rw [toNat_cpop_eq, toNat_fieldSum x k n h', ← hw]

end LemmaReuse
