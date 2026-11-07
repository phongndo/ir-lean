import Std.Tactic.BVDecide

/-! How a population count divides up, which `bv_decide` can't see for itself at 64 bits and more. -/

namespace Llvm.Bits

variable {w : Nat}

/-- The number of set bits from `lo` up to `lo + n`. -/
def count (x : BitVec w) (lo : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => count x lo n + (x.getLsbD (lo + n)).toNat

theorem cpopNatRec_eq_count (x : BitVec w) (n : Nat) : x.cpopNatRec n 0 = count x 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [BitVec.cpopNatRec_succ, Nat.zero_add, BitVec.cpopNatRec_eq, ih, count, Nat.zero_add, Nat.add_comm]

theorem count_extract (x : BitVec w) (lo k n : Nat) (h : n ≤ k) :
    count (x.extractLsb' lo k) 0 n = count x lo n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [count, Nat.zero_add]
    rw [ih (by omega), BitVec.getLsbD_extractLsb']
    simp [show n < k by omega]

theorem count_split (x : BitVec w) (lo a b : Nat) : count x lo (a + b) = count x lo a + count x (lo + a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← Nat.add_assoc, count, ih, count, Nat.add_assoc, Nat.add_assoc]

theorem count_add (x : BitVec w) (a b : Nat) : count x 0 (a + b) = count x 0 a + count x a b := by
  rw [count_split, Nat.zero_add]

theorem toNat_cpop_eq (x : BitVec w) : x.cpop.toNat = count x 0 w := by
  rw [BitVec.toNat_cpop, cpopNatRec_eq_count]

/-- The number of set bits in the byte at `8 * i`. -/
def byte (x : BitVec w) (i : Nat) : BitVec 8 := (x.extractLsb' (8 * i) 8).cpop

theorem toNat_byte (x : BitVec w) (i : Nat) : (byte x i).toNat = count x (8 * i) 8 := by
  rw [byte, toNat_cpop_eq, count_extract x _ 8 8 (Nat.le_refl 8)]

theorem toNat_byte_le (x : BitVec w) (i : Nat) : (byte x i).toNat ≤ 8 := by
  have := BitVec.toNat_cpop_le (x.extractLsb' (8 * i) 8)
  simpa [byte] using this

theorem byte_le (x : BitVec w) (i : Nat) : byte x i ≤ 8#8 := by
  have := BitVec.toNat_cpop_le (x.extractLsb' (8 * i) 8)
  simp only [BitVec.le_def, BitVec.toNat_ofNat]
  simpa [byte] using this

/-- A population count is the sum of the counts of a value's two parts. -/
theorem toNat_cpop_split (x : BitVec w) (a b : Nat) (h : w = a + b) :
    x.cpop.toNat = (x.extractLsb' 0 a).cpop.toNat + (x.extractLsb' a b).cpop.toNat := by
  subst h
  rw [toNat_cpop_eq, toNat_cpop_eq, toNat_cpop_eq, count_extract x 0 a a (Nat.le_refl a),
    count_extract x a b b (Nat.le_refl b), count_add]

theorem count_xor (x y : BitVec w) (lo n : Nat) :
    count (x ^^^ y) lo n % 2 = (count x lo n + count y lo n) % 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [count, BitVec.getLsbD_xor]
    cases x.getLsbD (lo + n) <;> cases y.getLsbD (lo + n) <;> simp <;> omega

/-- The parity of an xor is the parity of the two counts' sum. -/
theorem parity_xor (x y : BitVec w) : (x ^^^ y).cpop.toNat % 2 = (x.cpop.toNat + y.cpop.toNat) % 2 := by
  rw [toNat_cpop_eq, toNat_cpop_eq, toNat_cpop_eq, count_xor]

/-- Folding a value's two halves together with xor keeps its parity. -/
theorem parity_fold (x : BitVec w) (a : Nat) (h : w = a + a) :
    (x.extractLsb' 0 a ^^^ x.extractLsb' a a).cpop.toNat % 2 = x.cpop.toNat % 2 := by
  rw [parity_xor, toNat_cpop_split x a a h]

theorem toNat_cpop_bytes64 (x : BitVec 64) : x.cpop.toNat =
    (byte x 0).toNat + (byte x 1).toNat + (byte x 2).toNat + (byte x 3).toNat +
      (byte x 4).toNat + (byte x 5).toNat + (byte x 6).toNat + (byte x 7).toNat := by
  simp only [toNat_byte, toNat_cpop_eq]
  show count x 0 (8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) = _
  simp only [count_split]

theorem toNat_cpop_bytes128 (x : BitVec 128) : x.cpop.toNat =
    (byte x 0).toNat + (byte x 1).toNat + (byte x 2).toNat + (byte x 3).toNat +
      (byte x 4).toNat + (byte x 5).toNat + (byte x 6).toNat + (byte x 7).toNat +
      (byte x 8).toNat + (byte x 9).toNat + (byte x 10).toNat + (byte x 11).toNat +
      (byte x 12).toNat + (byte x 13).toNat + (byte x 14).toNat + (byte x 15).toNat := by
  simp only [toNat_byte, toNat_cpop_eq]
  show count x 0 (8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) = _
  simp only [count_split]

theorem cpop_eq_bytes128 (x : BitVec 128) : x.cpop.setWidth 32 =
    (byte x 0 + byte x 1 + byte x 2 + byte x 3 + byte x 4 + byte x 5 + byte x 6 + byte x 7 + byte x 8 + byte x 9 +
      byte x 10 + byte x 11 + byte x 12 + byte x 13 + byte x 14 + byte x 15).setWidth 32 := by
  have total := toNat_cpop_bytes128 x
  have h0 := toNat_byte_le x 0; have h1 := toNat_byte_le x 1; have h2 := toNat_byte_le x 2
  have h3 := toNat_byte_le x 3; have h4 := toNat_byte_le x 4; have h5 := toNat_byte_le x 5
  have h6 := toNat_byte_le x 6; have h7 := toNat_byte_le x 7; have h8 := toNat_byte_le x 8
  have h9 := toNat_byte_le x 9; have h10 := toNat_byte_le x 10; have h11 := toNat_byte_le x 11
  have h12 := toNat_byte_le x 12; have h13 := toNat_byte_le x 13; have h14 := toNat_byte_le x 14
  have h15 := toNat_byte_le x 15
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, Nat.reducePow]
  omega

theorem cpop_eq_bytes64 (x : BitVec 64) : x.cpop.setWidth 32 =
    (byte x 0 + byte x 1 + byte x 2 + byte x 3 + byte x 4 + byte x 5 + byte x 6 + byte x 7).setWidth 32 := by
  have total := toNat_cpop_bytes64 x
  have h0 := toNat_byte_le x 0; have h1 := toNat_byte_le x 1; have h2 := toNat_byte_le x 2
  have h3 := toNat_byte_le x 3; have h4 := toNat_byte_le x 4; have h5 := toNat_byte_le x 5
  have h6 := toNat_byte_le x 6; have h7 := toNat_byte_le x 7
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, Nat.reducePow]
  omega

/-- `cpop &&& 1` only depends on the count's parity. -/
theorem parity_setWidth {w : Nat} (hw : 32 ≤ w) (x : BitVec w) (y : BitVec 32) (h : y.cpop.toNat % 2 = x.cpop.toNat % 2) :
    (x.cpop &&& BitVec.ofNat w 1).setWidth 32 = y.cpop &&& 1#32 := by
  have hp : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ w by omega)
    simpa using this
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : Nat) % 2 ^ w = 1 := Nat.mod_eq_of_lt (by omega)
  have hx : x.cpop.toNat % 2 < 2 ^ 32 := by omega
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, h1, Nat.reducePow, Nat.reduceMod,
    Nat.and_one_is_mod, h]
  exact Nat.mod_eq_of_lt hx

/-! Adding a value's halves together, byte by byte, as a population count does once each byte holds its count. Each
byte is small enough not to carry into the next. -/

theorem fold16 {c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : BitVec 8}
    (h0 : c0 ≤ 8#8) (h1 : c1 ≤ 8#8) (h2 : c2 ≤ 8#8) (h3 : c3 ≤ 8#8) (h4 : c4 ≤ 8#8) (h5 : c5 ≤ 8#8) (h6 : c6 ≤ 8#8)
    (h7 : c7 ≤ 8#8) (h8 : c8 ≤ 8#8) (h9 : c9 ≤ 8#8) (h10 : c10 ≤ 8#8) (h11 : c11 ≤ 8#8) (h12 : c12 ≤ 8#8)
    (h13 : c13 ≤ 8#8) (h14 : c14 ≤ 8#8) (h15 : c15 ≤ 8#8) :
    (((c15 ++ c14 ++ c13 ++ c12 ++ c11 ++ c10 ++ c9 ++ c8 ++ c7 ++ c6 ++ c5 ++ c4 ++ c3 ++ c2 ++ c1 ++ c0) >>> 64#128) +
        (c15 ++ c14 ++ c13 ++ c12 ++ c11 ++ c10 ++ c9 ++ c8 ++ c7 ++ c6 ++ c5 ++ c4 ++ c3 ++ c2 ++ c1 ++ c0)).setWidth 64 =
      (c15 + c7) ++ (c14 + c6) ++ (c13 + c5) ++ (c12 + c4) ++ (c11 + c3) ++ (c10 + c2) ++ (c9 + c1) ++ (c8 + c0) := by
  bv_decide (config := { timeout := 120 })

theorem fold8 {d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8}
    (h0 : d0 ≤ 16#8) (h1 : d1 ≤ 16#8) (h2 : d2 ≤ 16#8) (h3 : d3 ≤ 16#8) (h4 : d4 ≤ 16#8) (h5 : d5 ≤ 16#8)
    (h6 : d6 ≤ 16#8) (h7 : d7 ≤ 16#8) :
    (((d7 ++ d6 ++ d5 ++ d4 ++ d3 ++ d2 ++ d1 ++ d0) >>> 32#64) + (d7 ++ d6 ++ d5 ++ d4 ++ d3 ++ d2 ++ d1 ++ d0)).setWidth 32 =
      (d7 + d3) ++ (d6 + d2) ++ (d5 + d1) ++ (d4 + d0) := by
  bv_decide (config := { timeout := 120 })

theorem fold4 {e0 e1 e2 e3 : BitVec 8} (h0 : e0 ≤ 32#8) (h1 : e1 ≤ 32#8) (h2 : e2 ≤ 32#8) (h3 : e3 ≤ 32#8) :
    let y := ((e3 ++ e2 ++ e1 ++ e0) >>> 16#32) + (e3 ++ e2 ++ e1 ++ e0)
    (y >>> 8#32) + y &&& 255#32 = (e3 + e2 + e1 + e0).setWidth 32 := by
  bv_decide (config := { timeout := 120 })

theorem fold4Small {e0 e1 e2 e3 : BitVec 8} (h0 : e0 ≤ 16#8) (h1 : e1 ≤ 16#8) (h2 : e2 ≤ 16#8) (h3 : e3 ≤ 16#8) :
    let y := ((e3 ++ e2 ++ e1 ++ e0) >>> 16#32) + (e3 ++ e2 ++ e1 ++ e0)
    (y >>> 8#32) + y &&& 127#32 = (e3 + e2 + e1 + e0).setWidth 32 := by
  bv_decide (config := { timeout := 120 })

end Llvm.Bits
