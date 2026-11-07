import Crc.Globals

/-! CRC-32's bit step, and that the two tables in zlib's `crc32.c` hold what it gives. This is its own
module because the kernel takes most of the time on these checks, and they only depend on the tables.
`tests/proofs.sh` regenerates `Crc` from zlib's own source. -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

open IRLean IRLean.Table Crc

namespace CrcProof

/-- RFC 1952's inner loop: one bit of the reflected polynomial. The state is wider than the CRC, so
that a whole word can be taken in at once, as the braided code does. -/
def bit (c : BitVec 64) : BitVec 64 :=
  if c &&& 1#64 = 1#64 then 0xEDB88320#64 ^^^ (c >>> 1#64) else c >>> 1#64

def steps : Nat → BitVec 64 → BitVec 64
  | 0, c => c
  | n + 1, c => steps n (bit c)

theorem bit_xor (a b : BitVec 64) : bit (a ^^^ b) = bit a ^^^ bit b := by
  simp only [bit]; bv_decide

theorem steps_xor (n : Nat) (a b : BitVec 64) : steps n (a ^^^ b) = steps n a ^^^ steps n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [steps, bit_xor, ih]

theorem steps_add (j k : Nat) (c : BitVec 64) : steps (j + k) c = steps k (steps j c) := by
  induction j generalizing c with
  | zero => simp [steps]
  | succ j ih =>
    rw [Nat.add_right_comm]
    simp only [steps, ih]

theorem bit_lt {c : BitVec 64} (h : c.toNat < 4294967296) : (bit c).toNat < 4294967296 := by
  have h' : c < 4294967296#64 := by simpa [BitVec.lt_def] using h
  have : bit c < 4294967296#64 := by simp only [bit]; bv_decide
  simpa [BitVec.lt_def] using this

theorem steps_lt (n : Nat) {c : BitVec 64} (h : c.toNat < 4294967296) :
    (steps n c).toNat < 4294967296 := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih => exact ih (bit_lt h)

/-- Eight steps take in the low byte and shift the rest down, whatever the rest holds. -/
theorem round_word (x : BitVec 64) : (x >>> 8#64) ^^^ steps 8 (x &&& 255#64) = steps 8 x := by
  simp only [steps, bit]; bv_decide

theorem shift8 {w : BitVec 64} (h : w.toNat < 72057594037927936) : steps 8 (w <<< 8#64) = w := by
  have h' : w < 72057594037927936#64 := by simpa [BitVec.lt_def] using h
  simp only [steps, bit]; bv_decide

/-! ### The tables -/

/-- `bit` on natural numbers, which the kernel can run quickly. It's written with these functions because
the kernel computes them directly, and it would otherwise work through their instances on every step. -/
def bitN (c : Nat) : Nat := Nat.xor (Nat.mul 3988292384 (Nat.mod c 2)) (Nat.div c 2)

theorem bitN_eq (c : Nat) : bitN c = (3988292384 * (c % 2)) ^^^ (c / 2) := rfl

/-- `steps` on natural numbers, written with `Nat.rec` for the same reason. -/
def stepsN (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c) (fun _ ih c => ih (bitN c)) n

theorem stepsN_zero (c : Nat) : stepsN 0 c = c := rfl

theorem stepsN_succ (n c : Nat) : stepsN (n + 1) c = stepsN n (bitN c) := rfl

theorem toNat_bit (c : BitVec 64) : (bit c).toNat = bitN c.toNat := by
  have hand : (c &&& 1#64 = 1#64) ↔ c.toNat % 2 = 1 := by
    rw [BitVec.toNat_eq, BitVec.toNat_and]
    have := Nat.and_two_pow_sub_one_eq_mod c.toNat 1
    simp at this ⊢
    try omega
  by_cases h : c.toNat % 2 = 1
  · simp [bit, bitN_eq, hand, h, BitVec.toNat_xor, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · have h0 : c.toNat % 2 = 0 := by omega
    simp [bit, bitN_eq, hand, h0, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_steps (n : Nat) (c : BitVec 64) : (steps n c).toNat = stepsN n c.toNat := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [steps, stepsN_succ, ih, toNat_bit]

/-- Every byte of the two tables is what the bit steps give. -/
theorem crc_table_bytes :
    g_crc_table_init.toList = (List.range 256).flatMap fun e => bytes4 (stepsN 8 e) := by
  decide +kernel

/-- One of the braid tables, which take 8 steps less for each byte further along a word. -/
noncomputable def braidSlice (k : Nat) : List Nat :=
  ((g_crc_braid_table_init.toList.drop (1024 * k)).take 1024)

def braidExpected (k : Nat) : List Nat :=
  (List.range 256).flatMap fun e => bytes4 (stepsN (320 - 8 * k) e)

theorem braid_slice0 : braidSlice 0 = braidExpected 0 := by decide +kernel
theorem braid_slice1 : braidSlice 1 = braidExpected 1 := by decide +kernel
theorem braid_slice2 : braidSlice 2 = braidExpected 2 := by decide +kernel
theorem braid_slice3 : braidSlice 3 = braidExpected 3 := by decide +kernel
theorem braid_slice4 : braidSlice 4 = braidExpected 4 := by decide +kernel
theorem braid_slice5 : braidSlice 5 = braidExpected 5 := by decide +kernel
theorem braid_slice6 : braidSlice 6 = braidExpected 6 := by decide +kernel
theorem braid_slice7 : braidSlice 7 = braidExpected 7 := by decide +kernel
end CrcProof
