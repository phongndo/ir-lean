import Crc

/-! zlib's `crc32_z`, as clang compiles it at `-O2`, proved safe and correct against RFC 1952.
`tests/proofs.sh` regenerates `Crc` from zlib's own source.

The code is the braided version: at each step five lanes each take in a word, with table reads doing
320 bit steps at once, and the last block combines the lanes. This works because CRC steps are linear
over xor. -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

open LLVMLean Crc

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

/-- `bit` on natural numbers, which the kernel can run quickly. -/
def bitN (c : Nat) : Nat := (3988292384 * (c % 2)) ^^^ (c / 2)

def stepsN : Nat → Nat → Nat
  | 0, c => c
  | n + 1, c => stepsN n (bitN c)

theorem toNat_bit (c : BitVec 64) : (bit c).toNat = bitN c.toNat := by
  have hand : (c &&& 1#64 = 1#64) ↔ c.toNat % 2 = 1 := by
    rw [BitVec.toNat_eq, BitVec.toNat_and]
    have := Nat.and_two_pow_sub_one_eq_mod c.toNat 1
    simp at this ⊢
    try omega
  by_cases h : c.toNat % 2 = 1
  · simp [bit, bitN, hand, h, BitVec.toNat_xor, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · have h0 : c.toNat % 2 = 0 := by omega
    simp [bit, bitN, hand, h0, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_steps (n : Nat) (c : BitVec 64) : (steps n c).toNat = stepsN n c.toNat := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [steps, stepsN, ih, toNat_bit]

def bytes4 (v : Nat) : List Nat := [v % 256, v / 256 % 256, v / 65536 % 256, v / 16777216 % 256]

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

/-! ### Reading the tables through memory -/

theorem length_flatMap_range (g : Nat → List Nat) (hg : ∀ e, (g e).length = 4) (n : Nat) :
    ((List.range n).flatMap g).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [hg]
    omega

theorem getElem?_flatMap_range (g : Nat → List Nat) (hg : ∀ e, (g e).length = 4) {n x j : Nat}
    (hx : x < n) (hj : j < 4) : ((List.range n).flatMap g)[4 * x + j]? = (g x)[j]? := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases h : x < n
    · rw [List.getElem?_append_left (by rw [length_flatMap_range g hg]; omega), ih h]
    · have e : x = n := by omega
      subst e
      rw [List.getElem?_append_right (by rw [length_flatMap_range g hg]; omega),
        length_flatMap_range g hg]
      simp

theorem length_bytes4 (v : Nat) : (bytes4 v).length = 4 := rfl

/-- A table's entry, in the bytes of its global. -/
theorem lookup {init : Array Nat} {off n : Nat} {f : Nat → Nat}
    (h : (init.toList.drop off).take (4 * n) = (List.range n).flatMap fun e => bytes4 (f e))
    {x j : Nat} (hx : x < n) (hj : j < 4) : init[off + (4 * x + j)]? = (bytes4 (f x))[j]? := by
  have h1 := getElem?_flatMap_range (fun e => bytes4 (f e)) (fun e => length_bytes4 _) hx hj
  rw [← h, List.getElem?_take, if_pos (by omega), List.getElem?_drop] at h1
  simpa using h1

theorem load_entry {m : Mem} {block s off n x v : Nat} {init : Array Nat} {f : Nat → Nat}
    (hA : m.allocs block = some { size := s, readonly := true, bytes := Mem.globalBytes init })
    (h : (init.toList.drop off).take (4 * n) = (List.range n).flatMap fun e => bytes4 (f e))
    (hx : x < n) (hv : f x = v) (hlt : v < 4294967296) (hs : off + 4 * n ≤ s) (hmax : s < 2 ^ 64)
    (halign : (m.addr ⟨block, BitVec.ofNat 64 (off + 4 * x)⟩).toNat % 4 = 0) :
    Mem.loadInt 32 m (some ⟨block, BitVec.ofNat 64 (off + 4 * x)⟩) 4 =
      Outcome.ok (some (BitVec.ofNat 32 v)) := by
  have l0 := lookup h hx (j := 0) (by omega)
  have l1 := lookup h hx (j := 1) (by omega)
  have l2 := lookup h hx (j := 2) (by omega)
  have l3 := lookup h hx (j := 3) (by omega)
  have hoff : (BitVec.ofNat 64 (off + 4 * x)).toNat = off + 4 * x := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have fits : ¬ off + 4 * x + 32 / 8 > s := by omega
  have b0 : init[off + 4 * x + 0]? = some (v % 256) := by subst hv; simpa [bytes4] using l0
  have b1 : init[off + 4 * x + 1]? = some (v / 256 % 256) := by subst hv; simpa [bytes4, Nat.add_assoc] using l1
  have b2 : init[off + 4 * x + 2]? = some (v / 65536 % 256) := by subst hv; simpa [bytes4, Nat.add_assoc] using l2
  have b3 : init[off + 4 * x + 3]? = some (v / 16777216 % 256) := by subst hv; simpa [bytes4, Nat.add_assoc] using l3
  have g0 : ¬ (v % 256 > 255) := by omega
  have g1 : ¬ (v / 256 % 256 > 255) := by omega
  have g2 : ¬ (v / 65536 % 256 > 255) := by omega
  have g3 : ¬ (v / 16777216 % 256 > 255) := by omega
  have total : v % 256 + 256 * (v / 256 % 256 + 256 * (v / 65536 % 256 + 256 * (v / 16777216 % 256 + 256 * 0))) = v := by
    omega
  have t0 : (BitVec.ofNat 8 (v % 256)).toNat = v % 256 := by simp [BitVec.toNat_ofNat]
  have t1 : (BitVec.ofNat 8 (v / 256 % 256)).toNat = v / 256 % 256 := by simp [BitVec.toNat_ofNat]
  have t2 : (BitVec.ofNat 8 (v / 65536 % 256)).toNat = v / 65536 % 256 := by simp [BitVec.toNat_ofNat]
  have t3 : (BitVec.ofNat 8 (v / 16777216 % 256)).toNat = v / 16777216 % 256 := by simp [BitVec.toNat_ofNat]
  simp only [Mem.loadInt, Mem.access, hA, hoff, fits, if_false, halign, Mem.read]
  have e0 : Mem.globalBytes init (off + 4 * x + 0) = .val (BitVec.ofNat 8 (v % 256)) := by
    simp only [Mem.globalBytes, b0, g0, ite_false]
  have e1 : Mem.globalBytes init (off + 4 * x + 1) = .val (BitVec.ofNat 8 (v / 256 % 256)) := by
    simp only [Mem.globalBytes, b1, g1, ite_false]
  have e2 : Mem.globalBytes init (off + 4 * x + 2) = .val (BitVec.ofNat 8 (v / 65536 % 256)) := by
    simp only [Mem.globalBytes, b2, g2, ite_false]
  have e3 : Mem.globalBytes init (off + 4 * x + 3) = .val (BitVec.ofNat 8 (v / 16777216 % 256)) := by
    simp only [Mem.globalBytes, b3, g3, ite_false]
  have c : ((4 : Nat) != 1 && (0 : Nat) != 0) = false := rfl
  simp only [List.range, List.range.loop, List.map, c, Bool.false_eq_true, ite_false, hoff, e0, e1, e2,
    e3, Mem.collect, t0, t1, t2, t3, total]

/-! ### What the code reads and computes -/

/-- An entry as the table holds it. -/
def entryV (n : Nat) (x : BitVec 64) : BitVec 32 := BitVec.ofNat 32 (steps n x).toNat

theorem zext_entry (n : Nat) {x : BitVec 64} (hx : x.toNat < 4294967296) :
    (entryV n x).setWidth 64 = steps n x := by
  have := steps_lt n hx
  apply BitVec.eq_of_toNat_eq
  simp only [entryV, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The two global tables are in memory, untouched, where the code expects them. Every real layout
meets the size limits: LangRef says no object crosses the top of the address space, even one past its
end. -/
structure Tables (m : Mem) : Prop where
  crc : m.allocs g_crc_table.block = Crc.initial.allocs g_crc_table.block
  braid : m.allocs g_crc_braid_table.block = Crc.initial.allocs g_crc_braid_table.block
  crcAlign : (m.base g_crc_table.block).toNat % 4 = 0
  braidAlign : (m.base g_crc_braid_table.block).toNat % 4 = 0
  crcFits : (m.base g_crc_table.block).toNat + 1024 < 2 ^ 64
  braidFits : (m.base g_crc_braid_table.block).toNat + 8192 < 2 ^ 64

theorem addr_align {m : Mem} {block k : Nat} (hb : block ≠ 0) (ha : (m.base block).toNat % 4 = 0)
    : (m.addr ⟨block, BitVec.ofNat 64 (4 * k)⟩).toNat % 4 = 0 := by
  have h : (block == 0) = false := by simpa using hb
  simp only [Mem.addr, h, Bool.false_eq_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mul4 {x : BitVec 64} (hx : x.toNat < 256) :
    Val.mul (some x) (some 4#64) (nuw := true) (nsw := true) = some (BitVec.ofNat 64 (4 * x.toNat)) := by
  have h' : x < 256#64 := by simpa [BitVec.lt_def] using hx
  have h1 : x.umulOverflow 4#64 = false := by bv_decide
  have h2 : x.smulOverflow 4#64 = false := by bv_decide
  have e : x * 4#64 = BitVec.ofNat 64 (4 * x.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  simp [Val.mul, h1, h2, e]

variable {m : Mem}

/-- Reads an entry of a table of 256 at offset `off` of a read-only global. -/
theorem table_load {P : Ptr} {init : Array Nat} {s off n : Nat} {f : Nat → Nat} {x : BitVec 64}
    (hA : m.allocs P.block = some { size := s, readonly := true, bytes := Mem.globalBytes init })
    (hP : P.offset = BitVec.ofNat 64 off) (hb : P.block ≠ 0)
    (h : (init.toList.drop off).take 1024 = (List.range 256).flatMap fun e => bytes4 (f e))
    (hf : ∀ e, f e = stepsN n e) (hs : off + 1024 ≤ s) (hmax : s < 2 ^ 64) (h4 : off % 4 = 0)
    (ha : (m.base P.block).toNat % 4 = 0) (hfit : (m.base P.block).toNat + s < 2 ^ 64)
    (hx : x.toNat < 256) :
    Mem.loadInt 32 m
        (Mem.gep m (some P) (Val.mul (some x) (some 4#64) (nuw := true) (nsw := true))
          (inbounds := true) (nuw := true)) 4 =
      Outcome.ok (some (entryV n x)) := by
  have hv : f x.toNat = (steps n x).toNat := by rw [hf, toNat_steps]
  have hlt := steps_lt n (c := x) (by omega)
  have hal : (m.addr ⟨P.block, BitVec.ofNat 64 (off + 4 * x.toNat)⟩).toNat % 4 = 0 := by
    have e : off + 4 * x.toNat = 4 * (off / 4 + x.toNat) := by omega
    rw [e]
    exact addr_align hb ha
  have hload := load_entry (n := 256) hA h hx hv hlt (by omega) hmax hal
  have toff : (BitVec.ofNat 64 off).toNat = off := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have td : (BitVec.ofNat 64 (4 * x.toNat)).toNat = 4 * x.toNat := by
    simp only [BitVec.toNat_ofNat]; omega
  have hsum : BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * x.toNat) = BitVec.ofNat 64 (off + 4 * x.toNat) := by
    simp [BitVec.ofNat_add]
  have hb' : (P.block == 0) = false := by simpa using hb
  have haddr : (m.addr P).toNat + 4 * x.toNat < 2 ^ 64 := by
    simp only [Mem.addr, hb', Bool.false_eq_true, ite_false, BitVec.toNat_add, hP, toff]
    omega
  have hgep : Mem.gep m (some P) (some (BitVec.ofNat 64 (4 * x.toNat))) (inbounds := true) (nuw := true) =
      some ⟨P.block, BitVec.ofNat 64 (off + 4 * x.toNat)⟩ := by
    rw [Mem.gep_forward hA (by simp only [hP, toff]; omega) hmax haddr (by omega), hP, hsum]
  rw [mul4 hx, hgep, hload]
  rfl

theorem and255 (x : BitVec 64) : (x &&& 255#64).toNat < 256 := by
  have h : (x.toNat &&& 255) ≤ 255 := Nat.and_le_right
  rw [BitVec.toNat_and]
  exact Nat.lt_succ_of_le h

theorem zext8 (b : BitVec 8) : (b.setWidth 64).toNat < 256 := by
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem shr56 (x : BitVec 64) : (x >>> 56#64).toNat < 256 := by
  have h : x >>> 56#64 < 256#64 := by bv_decide
  exact BitVec.lt_def.mp h

theorem crc_load (T : Tables m) {x : BitVec 64} (hx : x.toNat < 256) :
    Mem.loadInt 32 m
        (Mem.gep m (some g_crc_table) (Val.mul (some x) (some 4#64) (nuw := true) (nsw := true))
          (inbounds := true) (nuw := true)) 4 =
      Outcome.ok (some (entryV 8 x)) := by
  have hl : (g_crc_table_init.toList.drop 0).take 1024 =
      (List.range 256).flatMap fun e => bytes4 (stepsN 8 e) := by
    rw [List.drop_zero, crc_table_bytes]
    exact List.take_of_length_le (by rw [length_flatMap_range _ (fun e => length_bytes4 _)]; omega)
  exact table_load (s := 1024) (off := 0) T.crc rfl (by simp [g_crc_table]) hl (fun _ => rfl)
    (by omega) (by omega) (by omega) T.crcAlign T.crcFits hx

/-- Reads table `k` of `crc_braid_table`, whose pointer the code writes as `P`. -/
theorem braid_load (T : Tables m) {P : Ptr} {k : Nat} (hP : P = ⟨2, BitVec.ofNat 64 (1024 * k)⟩)
    (hk : k < 8) (hS : braidSlice k = braidExpected k) {x : BitVec 64} (hx : x.toNat < 256) :
    Mem.loadInt 32 m
        (Mem.gep m (some P) (Val.mul (some x) (some 4#64) (nuw := true) (nsw := true))
          (inbounds := true) (nuw := true)) 4 =
      Outcome.ok (some (entryV (320 - 8 * k) x)) := by
  subst hP
  exact table_load (s := 8192) (off := 1024 * k) T.braid rfl (by simp) hS (fun _ => rfl)
    (by omega) (by omega) (by omega) T.braidAlign T.braidFits hx

/-- A table read, as the code writes it. -/
abbrev tableRead (m : Mem) (P : Ptr) (x : BitVec 64) : Outcome (Val 32) :=
  Mem.loadInt 32 m
    (Mem.gep m (some P) (Val.mul (some x) (some 4#64) (nuw := true) (nsw := true))
      (inbounds := true) (nuw := true)) 4

theorem crc_and (T : Tables m) (x : BitVec 64) :
    tableRead m g_crc_table (x &&& 255#64) = Outcome.ok (some (entryV 8 (x &&& 255#64))) :=
  crc_load T (and255 x)
theorem crc_byte (T : Tables m) (b : BitVec 8) :
    tableRead m g_crc_table (b.setWidth 64) = Outcome.ok (some (entryV 8 (b.setWidth 64))) :=
  crc_load T (zext8 b)
theorem braid0 (T : Tables m) (x : BitVec 64) :
    tableRead m g_crc_braid_table (x &&& 255#64) = Outcome.ok (some (entryV 320 (x &&& 255#64))) :=
  braid_load T (k := 0) rfl (by omega) braid_slice0 (and255 x)
theorem braid1 (T : Tables m) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 1024#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 312 (x &&& 255#64))) :=
  braid_load T (k := 1) rfl (by omega) braid_slice1 (and255 x)
theorem braid2 (T : Tables m) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 2048#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 304 (x &&& 255#64))) :=
  braid_load T (k := 2) rfl (by omega) braid_slice2 (and255 x)
theorem braid3 (T : Tables m) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 3072#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 296 (x &&& 255#64))) :=
  braid_load T (k := 3) rfl (by omega) braid_slice3 (and255 x)
theorem braid4 (T : Tables m) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 4096#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 288 (x &&& 255#64))) :=
  braid_load T (k := 4) rfl (by omega) braid_slice4 (and255 x)
theorem braid5 (T : Tables m) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 5120#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 280 (x &&& 255#64))) :=
  braid_load T (k := 5) rfl (by omega) braid_slice5 (and255 x)
theorem braid6 (T : Tables m) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 6144#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 272 (x &&& 255#64))) :=
  braid_load T (k := 6) rfl (by omega) braid_slice6 (and255 x)
theorem braid7 (T : Tables m) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 7168#64 } (x >>> 56#64) =
      Outcome.ok (some (entryV 264 (x >>> 56#64))) :=
  braid_load T (k := 7) rfl (by omega) braid_slice7 (shr56 x)

/-! ### The spec and the words -/

/-- RFC 1952's update for one byte. -/
def byteStep (c : BitVec 64) (b : BitVec 8) : BitVec 64 := steps 8 (c ^^^ b.setWidth 64)

/-- The state after `i` bytes of `d`, from state `s0`. -/
def spec (s0 : BitVec 64) (d : Nat → BitVec 8) : Nat → BitVec 64
  | 0 => s0
  | i + 1 => byteStep (spec s0 d i) (d i)

def start (crc : BitVec 64) : BitVec 64 := (crc &&& 4294967295#64) ^^^ 4294967295#64
def finish (c : BitVec 64) : BitVec 64 := c ^^^ 4294967295#64

/-- `j` bytes of `d` from `i`, little-endian. -/
def le (d : Nat → BitVec 8) (i : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (d i).toNat + 256 * le d (i + 1) j

theorem le_lt (d : Nat → BitVec 8) (i j : Nat) : le d i j < 256 ^ j := by
  induction j generalizing i with
  | zero => simp [le]
  | succ j ih =>
    have := ih (i + 1)
    have hd := (d i).isLt
    simp only [le, Nat.pow_succ]
    simp at hd
    omega

/-- The 64-bit word the code loads. -/
def word (d : Nat → BitVec 8) (i : Nat) : BitVec 64 := BitVec.ofNat 64 (le d i 8)

theorem ofNat_le_succ (d : Nat → BitVec 8) (i j : Nat) (hj : j ≤ 7) :
    BitVec.ofNat 64 (le d i (j + 1)) =
      (d i).setWidth 64 ^^^ (BitVec.ofNat 64 (le d (i + 1) j) <<< 8#64) := by
  have hlt : le d (i + 1) j < 256 ^ 7 := by
    have h1 := le_lt d (i + 1) j
    have h2 : 256 ^ j ≤ 256 ^ 7 := Nat.pow_le_pow_right (by omega) hj
    omega
  have hd := (d i).isLt
  have htn : (BitVec.ofNat 64 (le d (i + 1) j)).toNat = le d (i + 1) j := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  generalize BitVec.ofNat 64 (le d (i + 1) j) = B at htn
  have hB : B < 72057594037927936#64 := by
    rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; omega
  have hz : ((d i).setWidth 64).toNat = (d i).toNat := by
    simp only [BitVec.toNat_setWidth]; omega
  generalize hA' : (d i).setWidth 64 = A at hz
  have hA : A < 256#64 := by
    rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; simp at hd; omega
  have key : A + 256#64 * B = A ^^^ (B <<< 8#64) := by bv_decide
  rw [← key]
  apply BitVec.eq_of_toNat_eq
  simp only [le, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul, hz, htn]
  omega

/-- Taking in `j` bytes one at a time, or all at once as a word, comes to the same thing. -/
theorem steps_le (s0 : BitVec 64) (d : Nat → BitVec 8) (i j : Nat) (hj : j ≤ 8) :
    steps (8 * j) (spec s0 d i ^^^ BitVec.ofNat 64 (le d i j)) = spec s0 d (i + j) := by
  induction j generalizing i with
  | zero => simp [le, steps]
  | succ j ih =>
    have hlt : (BitVec.ofNat 64 (le d (i + 1) j)).toNat < 72057594037927936 := by
      have h1 := le_lt d (i + 1) j
      have h2 : 256 ^ j ≤ 256 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
      simp only [BitVec.toNat_ofNat]
      have : le d (i + 1) j < 72057594037927936 := by omega
      omega
    have e : 8 * (j + 1) = 8 + 8 * j := by omega
    rw [e, steps_add, ofNat_le_succ d i j (by omega), ← BitVec.xor_assoc, steps_xor, shift8 hlt]
    have e2 : i + (j + 1) = i + 1 + j := by omega
    rw [e2]
    exact ih (i + 1) (by omega)

theorem word_spec (s0 : BitVec 64) (d : Nat → BitVec 8) (i : Nat) :
    steps 64 (spec s0 d i ^^^ word d i) = spec s0 d (i + 8) :=
  steps_le s0 d i 8 (by omega)

/-! ### The braid -/

theorem steps_steps (j k : Nat) (c : BitVec 64) : steps k (steps j c) = steps (j + k) c :=
  (steps_add j k c).symm

/-- Five words at once: what the serial update does to 40 bytes, spread over the words. -/
theorem five_words (s0 : BitVec 64) (d : Nat → BitVec 8) (i : Nat) :
    spec s0 d (i + 40) =
      steps 320 (spec s0 d i ^^^ word d i) ^^^ steps 256 (word d (i + 8)) ^^^
        steps 192 (word d (i + 16)) ^^^ steps 128 (word d (i + 24)) ^^^ steps 64 (word d (i + 32)) := by
  have w0 := word_spec s0 d i
  have w1 := word_spec s0 d (i + 8)
  have w2 := word_spec s0 d (i + 16)
  have w3 := word_spec s0 d (i + 24)
  have w4 := word_spec s0 d (i + 32)
  rw [show i + 32 + 8 = i + 40 from rfl] at w4
  rw [show i + 24 + 8 = i + 32 from rfl] at w3
  rw [show i + 16 + 8 = i + 24 from rfl] at w2
  rw [show i + 8 + 8 = i + 16 from rfl] at w1
  rw [← w4, ← w3, ← w2, ← w1, ← w0]
  simp only [steps_xor, steps_steps]

/-- What the lanes hold: combining them with the next five words gives the serial state after those
words. -/
def Lanes (s0 : BitVec 64) (d : Nat → BitVec 8) (i : Nat) (c0 c1 c2 c3 c4 : BitVec 64) : Prop :=
  steps 320 (word d i ^^^ c0) ^^^ steps 256 (word d (i + 8) ^^^ c1) ^^^
    steps 192 (word d (i + 16) ^^^ c2) ^^^ steps 128 (word d (i + 24) ^^^ c3) ^^^
    steps 64 (word d (i + 32) ^^^ c4) = spec s0 d (i + 40)

theorem xor_zero' (x : BitVec 64) : x ^^^ 0#64 = x := by simp

/-- The lanes before the first iteration. -/
theorem lanes_start (s0 : BitVec 64) (d : Nat → BitVec 8) (i : Nat) :
    Lanes s0 d i (spec s0 d i) 0#64 0#64 0#64 0#64 := by
  unfold Lanes
  rw [five_words, xor_zero', xor_zero', xor_zero', xor_zero', BitVec.xor_comm (word d i)]

seal steps in
/-- Each lane advances by the 40 bytes the other four lanes are taking in. -/
theorem lanes_step {s0 : BitVec 64} {d : Nat → BitVec 8} {i : Nat} {c0 c1 c2 c3 c4 : BitVec 64}
    (h : Lanes s0 d i c0 c1 c2 c3 c4) :
    Lanes s0 d (i + 40) (steps 320 (word d i ^^^ c0)) (steps 320 (word d (i + 8) ^^^ c1))
      (steps 320 (word d (i + 16) ^^^ c2)) (steps 320 (word d (i + 24) ^^^ c3))
      (steps 320 (word d (i + 32) ^^^ c4)) := by
  unfold Lanes at h ⊢
  rw [five_words s0 d (i + 40), ← h]
  generalize word d (i + 8) = w1
  generalize word d (i + 16) = w2
  generalize word d (i + 24) = w3
  generalize word d (i + 32) = w4
  generalize word d (i + 40) = w0'
  generalize word d (i + 40 + 8) = w1'
  generalize word d (i + 40 + 16) = w2'
  generalize word d (i + 40 + 24) = w3'
  generalize word d (i + 40 + 32) = w4'
  generalize word d i = w0
  simp only [steps_xor, steps_steps, Nat.reduceAdd]
  ac_rfl

seal steps in
/-- The last block: the code combines the lanes through one word at a time. -/
theorem lanes_finish {s0 : BitVec 64} {d : Nat → BitVec 8} {i : Nat} {c0 c1 c2 c3 c4 : BitVec 64}
    (h : Lanes s0 d i c0 c1 c2 c3 c4) :
    steps 64 (word d (i + 32) ^^^ c4 ^^^
      steps 64 (word d (i + 24) ^^^ c3 ^^^
        steps 64 (word d (i + 16) ^^^ c2 ^^^
          steps 64 (word d (i + 8) ^^^ c1 ^^^ steps 64 (word d i ^^^ c0))))) = spec s0 d (i + 40) := by
  rw [← h]
  generalize word d (i + 8) = w1
  generalize word d (i + 16) = w2
  generalize word d (i + 24) = w3
  generalize word d (i + 32) = w4
  generalize word d i = w0
  simp only [steps_xor, steps_steps, Nat.reduceAdd]
  ac_rfl

/-! One lane's eight table reads add up to 320 steps. -/

theorem steps_down {x y : BitVec 64} {n : Nat} (hy : y.toNat < 72057594037927936)
    (h : steps n y = x) : steps (8 + n) (y <<< 8#64) = x := by
  rw [steps_add, shift8 hy, h]

/-- A byte shifted up `k` bytes takes `8 * k` steps to come back down. -/
theorem steps_byte {x : BitVec 64} (hx : x.toNat < 256) (k : Nat) (hk : k ≤ 7) :
    steps (8 * k) (x <<< (8 * k)) = x := by
  induction k with
  | zero => simp [steps]
  | succ k ih =>
    have hlt : (x <<< (8 * k)).toNat < 72057594037927936 := by
      simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      have hp : 2 ^ (8 * k) ≤ 2 ^ 48 := Nat.pow_le_pow_right (by omega) (by omega)
      have hm : x.toNat * 2 ^ (8 * k) < 256 * 2 ^ 48 :=
        Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hx (Nat.pow_pos (by omega))) (Nat.mul_le_mul_left _ hp)
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
    have e : x <<< (8 * (k + 1)) = (x <<< (8 * k)) <<< 8#64 := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.shiftLeft_add]
      rfl
    rw [e, show 8 * (k + 1) = 8 + 8 * k by omega]
    exact steps_down hlt (ih (by omega))


theorem zext_xor32 (a b : BitVec 32) : (a ^^^ b).setWidth 64 = a.setWidth 64 ^^^ b.setWidth 64 := by
  bv_decide

/-- A word, split into its bytes. -/
theorem split_word (W : BitVec 64) :
    W = (W >>> 56#64) <<< 56#64 ^^^ (((W >>> 48#64) &&& 255#64) <<< 48#64 ^^^
      (((W >>> 40#64) &&& 255#64) <<< 40#64 ^^^ (((W >>> 32#64) &&& 255#64) <<< 32#64 ^^^
      (((W >>> 24#64) &&& 255#64) <<< 24#64 ^^^ (((W >>> 16#64) &&& 255#64) <<< 16#64 ^^^
      (((W >>> 8#64) &&& 255#64) <<< 8#64 ^^^ (W &&& 255#64))))))) := by
  bv_decide

theorem up {x : BitVec 64} (hx : x.toNat < 256) (k n : Nat) (hk : k ≤ 7) :
    steps (8 * k + n) (x <<< (8 * k)) = steps n x := by
  rw [steps_add, steps_byte hx k hk]

/-- Why the braid tables work: their entries add up to 320 steps of the whole word. -/
theorem table_sum (W : BitVec 64) :
    steps 264 (W >>> 56#64) ^^^ (steps 272 ((W >>> 48#64) &&& 255#64) ^^^
      (steps 280 ((W >>> 40#64) &&& 255#64) ^^^ (steps 288 ((W >>> 32#64) &&& 255#64) ^^^
      (steps 296 ((W >>> 24#64) &&& 255#64) ^^^ (steps 304 ((W >>> 16#64) &&& 255#64) ^^^
      (steps 312 ((W >>> 8#64) &&& 255#64) ^^^ steps 320 (W &&& 255#64))))))) = steps 320 W := by
  conv => rhs; rw [split_word W]
  simp only [steps_xor]
  have h7 := up (shr56 W) 7 264 (by omega)
  have h6 := up (and255 (W >>> 48#64)) 6 272 (by omega)
  have h5 := up (and255 (W >>> 40#64)) 5 280 (by omega)
  have h4 := up (and255 (W >>> 32#64)) 4 288 (by omega)
  have h3 := up (and255 (W >>> 24#64)) 3 296 (by omega)
  have h2 := up (and255 (W >>> 16#64)) 2 304 (by omega)
  have h1 := up (and255 (W >>> 8#64)) 1 312 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd] at h7 h6 h5 h4 h3 h2 h1
  simp only [BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, h7, h6, h5, h4, h3, h2, h1]

theorem steps320_lt (W : BitVec 64) : (steps 320 W).toNat < 4294967296 := by
  rw [← table_sum W]
  have b (n : Nat) (x : BitVec 64) (hx : x.toNat < 256) : steps n x < 4294967296#64 := by
    have := steps_lt n (c := x) (by omega)
    rw [BitVec.lt_def]; simpa using this
  have h7 := b 264 _ (shr56 W)
  have h6 := b 272 _ (and255 (W >>> 48#64))
  have h5 := b 280 _ (and255 (W >>> 40#64))
  have h4 := b 288 _ (and255 (W >>> 32#64))
  have h3 := b 296 _ (and255 (W >>> 24#64))
  have h2 := b 304 _ (and255 (W >>> 16#64))
  have h1 := b 312 _ (and255 (W >>> 8#64))
  have h0 := b 320 _ (and255 W)
  generalize steps 264 _ = a7 at *
  generalize steps 272 _ = a6 at *
  generalize steps 280 _ = a5 at *
  generalize steps 288 _ = a4 at *
  generalize steps 296 _ = a3 at *
  generalize steps 304 _ = a2 at *
  generalize steps 312 _ = a1 at *
  generalize steps 320 _ = a0 at *
  have : a7 ^^^ (a6 ^^^ (a5 ^^^ (a4 ^^^ (a3 ^^^ (a2 ^^^ (a1 ^^^ a0)))))) < 4294967296#64 := by bv_decide
  simpa [BitVec.lt_def] using this

theorem trunc_zext (L : BitVec 32) : (L.setWidth 64).setWidth 32 = L := by bv_decide

/-- One lane of an iteration: eight table reads, as the optimizer left them. It knows the lane's
state only has 32 bits, so reads the upper bytes straight from the word. -/
theorem braid_lane (V : BitVec 64) (C : BitVec 32) :
    entryV 264 (V >>> 56#64) ^^^ (entryV 272 ((V >>> 48#64) &&& 255#64) ^^^
      (entryV 280 ((V >>> 40#64) &&& 255#64) ^^^ (entryV 288 ((V >>> 32#64) &&& 255#64) ^^^
      (entryV 296 (((V ^^^ C.setWidth 64) >>> 24#64) &&& 255#64) ^^^
      (entryV 304 (((V ^^^ C.setWidth 64) >>> 16#64) &&& 255#64) ^^^
      (entryV 312 (((V ^^^ C.setWidth 64) >>> 8#64) &&& 255#64) ^^^
      entryV 320 ((V ^^^ C.setWidth 64) &&& 255#64))))))) =
      (steps 320 (V ^^^ C.setWidth 64)).setWidth 32 := by
  have e7 : V >>> 56#64 = (V ^^^ C.setWidth 64) >>> 56#64 := by bv_decide
  have e6 : V >>> 48#64 = (V ^^^ C.setWidth 64) >>> 48#64 := by bv_decide
  have e5 : V >>> 40#64 = (V ^^^ C.setWidth 64) >>> 40#64 := by bv_decide
  have e4 : V >>> 32#64 = (V ^^^ C.setWidth 64) >>> 32#64 := by bv_decide
  rw [e7, e6, e5, e4]
  generalize V ^^^ C.setWidth 64 = W
  rw [← table_sum W]
  have z (n : Nat) (x : BitVec 64) (hx : x.toNat < 256) : (entryV n x).setWidth 64 = steps n x :=
    zext_entry n (by omega)
  rw [← z 264 _ (shr56 W), ← z 272 _ (and255 _), ← z 280 _ (and255 _), ← z 288 _ (and255 _),
    ← z 296 _ (and255 _), ← z 304 _ (and255 _), ← z 312 _ (and255 _), ← z 320 _ (and255 _)]
  simp only [← zext_xor32]
  exact (trunc_zext _).symm

theorem zext_steps320 (W : BitVec 64) : ((steps 320 W).setWidth 32).setWidth 64 = steps 320 W := by
  have := steps320_lt W
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

/-! ### Reading words of the buffer -/

theorem addr_bufPtr (m : Mem) (block o i k : Nat) :
    m.addr (bufPtr block o (i + k)) = m.addr (bufPtr block o i) + BitVec.ofNat 64 k := by
  have hoff : BitVec.ofNat 64 (o + (i + k)) = BitVec.ofNat 64 (o + i) + BitVec.ofNat 64 k := by
    rw [← Nat.add_assoc]; simp [BitVec.ofNat_add]
  simp only [Mem.addr, bufPtr, hoff]
  split
  · rfl
  · rw [BitVec.add_assoc]

theorem addr_mod8 (A : BitVec 64) {k : Nat} (hk : k < 2 ^ 64) :
    (A + BitVec.ofNat 64 k).toNat % 8 = (A.toNat + k) % 8 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem load64 {block o n : Nat} {d : Nat → BitVec 8} (B : Readable m block o n d) {i : Nat}
    (h : i + 8 ≤ n) (ha : (m.addr (bufPtr block o i)).toNat % 8 = 0) :
    Mem.loadInt 64 m (some (bufPtr block o i)) 8 = Outcome.ok (some (word d i)) := by
  obtain ⟨a, hA, hsz, hmax, hd⟩ := B.alloc
  have hoff : (BitVec.ofNat 64 (o + i)).toNat = o + i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have fits : ¬ o + i + 64 / 8 > a.size := by omega
  have b0 := hd i (by omega)
  have b1 := hd (i + 1) (by omega)
  have b2 := hd (i + 2) (by omega)
  have b3 := hd (i + 3) (by omega)
  have b4 := hd (i + 4) (by omega)
  have b5 := hd (i + 5) (by omega)
  have b6 := hd (i + 6) (by omega)
  have b7 := hd (i + 7) (by omega)
  have c : ((8 : Nat) != 1 && (0 : Nat) != 0) = false := rfl
  have fits' : ¬ o + (i + 64 / 8) > a.size := by omega
  simp only [Mem.loadInt, Mem.access, hA, bufPtr, hoff, ite_false, ha, Mem.read,
    List.range, List.range.loop, List.map, c, Bool.false_eq_true, Nat.add_assoc, Nat.add_zero, fits',
    word, le, Nat.reduceAdd]
  simp only [hoff, Nat.add_assoc, Nat.reduceAdd, b0, b1, b2, b3, b4, b5, b6, b7, Mem.collect]

/-! ### Running the blocks, from the end backward -/

/-- A word's round of `crc_word`, folded back into steps. -/
theorem round_word' (x : BitVec 64) :
    (x >>> 8#64) ^^^ (entryV 8 (x &&& 255#64)).setWidth 64 = steps 8 x := by
  rw [zext_entry 8 (by have := and255 x; omega), round_word]

/-- The same, when the optimizer has moved the round's last step in among the next word's bytes. -/
theorem round_mid (y x : BitVec 64) :
    y ^^^ (entryV 8 (x &&& 255#64)).setWidth 64 ^^^ x >>> 8#64 = y ^^^ steps 8 x := by
  rw [BitVec.xor_assoc, BitVec.xor_comm ((entryV 8 _).setWidth 64), round_word']

theorem toNat_and7 (x : BitVec 64) : (x &&& 7#64).toNat = x.toNat % 8 := by
  have := Nat.and_two_pow_sub_one_eq_mod x.toNat 3
  simp [BitVec.toNat_and]
  simpa using this

/-- A byte's round. -/
theorem round_byte (x : BitVec 64) (b : BitVec 8) :
    (x >>> 8#64) ^^^ (entryV 8 ((b ^^^ x.setWidth 8).setWidth 64)).setWidth 64 =
      steps 8 (x ^^^ b.setWidth 64) := by
  rw [zext_entry 8 (by have := zext8 (b ^^^ x.setWidth 8); omega), ← round_word (x ^^^ b.setWidth 64)]
  have e1 : (x ^^^ b.setWidth 64) >>> 8#64 = x >>> 8#64 := by bv_decide
  have e2 : (x ^^^ b.setWidth 64) &&& 255#64 = (b ^^^ x.setWidth 8).setWidth 64 := by bv_decide
  rw [e1, e2]

theorem spec_byte (s0 : BitVec 64) (d : Nat → BitVec 8) (i : Nat) :
    steps 8 (spec s0 d i ^^^ (d i).setWidth 64) = spec s0 d (i + 1) := rfl

theorem spec_lt {s0 : BitVec 64} (hs : s0.toNat < 4294967296) (d : Nat → BitVec 8) (i : Nat) :
    (spec s0 d i).toNat < 4294967296 := by
  induction i with
  | zero => exact hs
  | succ i ih =>
    apply steps_lt
    have h : spec s0 d i < 4294967296#64 := by rw [BitVec.lt_def]; simpa using ih
    have h2 : spec s0 d i ^^^ (d i).setWidth 64 < 4294967296#64 := by bv_decide
    simpa [BitVec.lt_def] using h2

theorem range32 {x : BitVec 64} (h : x.toNat < 4294967296) :
    Val.range 0#64 4294967296#64 (some x) = some x := by
  have h' : BitVec.ult (x - 0#64) (4294967296#64 - 0#64) = true := by
    simp [BitVec.ult]; omega
  simp only [Val.range, h', ite_true]

theorem udiv40 (L : BitVec 64) : Val.udiv (some L) (some 40#64) = Outcome.ok (some (L / 40#64)) := by
  simp [Val.udiv]

/-- `div - 1`, whose `nsw` holds because a byte count over 40 is well below the sign bit. -/
theorem dec1_nsw {D : BitVec 64} (h : D.toNat < 4611686018427387904) :
    Val.add (some D) (some 18446744073709551615#64) (nsw := true) =
      some (D + 18446744073709551615#64) := by
  have h' : D < 4611686018427387904#64 := by simpa [BitVec.lt_def] using h
  have : D.saddOverflow 18446744073709551615#64 = false := by bv_decide
  simp [Val.add, this]

theorem trunc32 {x : BitVec 64} (h : x.toNat < 4294967296) :
    Val.trunc 32 (some x) (nuw := true) = some (x.setWidth 32) := by
  have e : (x.setWidth 32).setWidth 64 = x := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    omega
  simp [Val.trunc, e]

local notation "St" => Crc.crc32_z.step

/-- Runs one block: evaluates it on known values, folding the CRC rounds as they appear, and leaves
each branch condition as a fact about natural numbers. -/
syntax "exec " term ", " term : tactic
macro_rules
  | `(tactic| exec $b, $t) =>
    `(tactic| (rw [run]; simp (disch := omega) only [Crc.crc32_z.step, llvm_val, Val.trunc_some, lshr_lit,
        crc_and $t:term, crc_byte $t:term, braid0 $t:term, braid1 $t:term, braid2 $t:term,
        braid3 $t:term, braid4 $t:term, braid5 $t:term, braid6 $t:term, braid7 $t:term,
        Readable.load $b:term, Readable.gep $b:term, Readable.gep_plain, load64 $b:term,
        round_word', round_mid, round_byte, spec_byte, steps_steps, braid_lane, zext_xor32, select_and,
        toNat_and7, Mem.toVal, udiv40, Val.mul_some, dec1_nsw, trunc32,
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        jump, ret, andThen, Outcome.ok, beq_toNat, bne_toNat, ult_toNat, decide_eq_true_eq,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.add_assoc]))

variable {block o n : Nat} {d : Nat → BitVec 8} {s0 : BitVec 64}

theorem while_end299_run (hs : s0.toNat < 4294967296) :
    run St (.while_end299 m (some (spec s0 d n))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have h := spec_lt hs d n
  have h1 : spec s0 d n < 4294967296#64 := by rw [BitVec.lt_def]; simpa using h
  have h2 : (spec s0 d n ^^^ 4294967295#64) < 4294967296#64 := by bv_decide
  have h3 : (spec s0 d n ^^^ 4294967295#64).toNat < 4294967296 := by simpa [BitVec.lt_def] using h2
  rw [run]
  simp only [Crc.crc32_z.step, llvm_val, jump, andThen, Outcome.ok]
  rw [run]
  simp only [Crc.crc32_z.step, range32 h3, ret, andThen, Outcome.ok]
  rfl

/-- The last bytes, one at a time, in the seven blocks clang unrolled them to. -/
theorem while_body289_6_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i : Nat} (hi : i + 7 = n) :
    run St (.while_body289_6 m (some (bufPtr block o i)) (some (spec s0 d (i + 6)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  subst hi
  exact while_end299_run hs

theorem while_body289_5_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 5 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289_5 m (some L) (some (bufPtr block o i)) (some (spec s0 d (i + 5)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 6 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_6_run B T hs (by omega)

theorem while_body289_4_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 4 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289_4 m (some L) (some (bufPtr block o i)) (some (spec s0 d (i + 4)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 5 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_5_run B T hs h0 (by omega) hi

theorem while_body289_3_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 3 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289_3 m (some L) (some (bufPtr block o i)) (some (spec s0 d (i + 3)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 4 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_4_run B T hs h0 (by omega) hi

theorem while_body289_2_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 2 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289_2 m (some L) (some (bufPtr block o i)) (some (spec s0 d (i + 2)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 3 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_3_run B T hs h0 (by omega) hi

theorem while_body289_1_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 1 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289_1 m (some L) (some (bufPtr block o i)) (some (spec s0 d (i + 1)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 2 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_2_run B T hs h0 (by omega) hi

theorem while_body289_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 0 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289 m (some L) (some (bufPtr block o i)) (some (spec s0 d i))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 1 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_1_run B T hs h0 (by omega) hi

theorem while_cond287_preheader_run (B : Readable m block o n d) (T : Tables m)
    (hs : s0.toNat < 4294967296) {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hi : i + L.toNat = n) :
    run St (.while_cond287_preheader m (some L) (some (bufPtr block o i)) (some (spec s0 d i))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_run B T hs h0 (by omega) hi

/-- Eight bytes at a time, while there are that many. -/
theorem while_body220_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    (r : Nat) :
    ∀ (i : Nat) (L : BitVec 64), 8 ≤ L.toNat → L.toNat < 8 * (r + 1) → i + L.toNat = n →
      run St (.while_body220 m (some (spec s0 d i)) (some (bufPtr block o i)) (some L)) =
        Outcome.ok (some (finish (spec s0 d n)), m) := by
  induction r with
  | zero => intro i L h8 hr; omega
  | succ r ih =>
    intro i L h8 hr hi
    have hdec : (L + 18446744073709551608#64).toNat = L.toNat - 8 :=
      toNat_dec 8 rfl (by omega) (by omega)
    exec B, T
    split
    · exact ih (i + 8) _ (by omega) (by omega) (by omega)
    · exact while_cond287_preheader_run B T hs (by omega) (by omega)

theorem if_end216_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (hi : i + L.toNat = n) :
    run St (.if_end216 m (some L) (some (bufPtr block o i)) (some (spec s0 d i))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · exact while_body220_run B T hs (L.toNat / 8) i L (by omega) (by omega) hi
  · exact while_cond287_preheader_run B T hs (by omega) hi

theorem aligned_add {i k : Nat} (h : (m.addr (bufPtr block o i)).toNat % 8 = 0) (hk : k % 8 = 0)
    (hk' : k < 2 ^ 64) : (m.addr (bufPtr block o (i + k))).toNat % 8 = 0 := by
  rw [addr_bufPtr, addr_mod8 _ hk']
  omega

/-- The last block of the braid: combine the lanes. -/
theorem while_end80_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i : Nat} {L c0 c1 c2 c3 c4 : BitVec 64} (hi : i + 40 + L.toNat = n)
    (ha : (m.addr (bufPtr block o i)).toNat % 8 = 0) (h : Lanes s0 d i c0 c1 c2 c3 c4) :
    run St (.while_end80 m (some c2) (some c1) (some c3) (some c0) (some c4)
        (some (bufPtr block o i)) (some L)) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have a1 := aligned_add (k := 8) ha (by omega) (by omega)
  have a2 := aligned_add (k := 16) ha (by omega) (by omega)
  have a3 := aligned_add (k := 24) ha (by omega) (by omega)
  have a4 := aligned_add (k := 32) ha (by omega) (by omega)
  exec B, T
  rw [lanes_finish h]
  exact if_end216_run B T hs (by omega)

theorem mul40 {D : BitVec 64} (h : 40 * D.toNat < 2 ^ 64) :
    Val.mul (some D) (some 40#64) (nuw := true) = some (BitVec.ofNat 64 (40 * D.toNat)) := by
  have e : D * 40#64 = BitVec.ofNat 64 (40 * D.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  have hno : D.umulOverflow 40#64 = false := by
    simp only [BitVec.umulOverflow, BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le, ge_iff_le]
    omega
  simp [Val.mul, hno, e]

theorem bufPtr_back {j c : Nat} (hc : c + 40 = 18446744073709551616) (h : 40 ≤ j) :
    bufPtr block o (j + c) = bufPtr block o (j - 40) := by
  have e : o + (j + c) = o + (j - 40) + 2 ^ 64 := by omega
  have hb : BitVec.ofNat 64 (o + (j + c)) = BitVec.ofNat 64 (o + (j - 40)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [e, Nat.add_mod_right]
  simp only [bufPtr, hb]

/-- Leaving the loop: the code works out the pointer to the last block by going to the end of the
blocks and back one. -/
theorem while_end80_loopexit_run (B : Readable m block o n d) (T : Tables m)
    (hs : s0.toNat < 4294967296) {i i0 : Nat} {D L : BitVec 64} {C0 C1 C2 C3 C4 : BitVec 32}
    (hi0 : i0 + 40 * D.toNat = i + 40) (hD : 40 * D.toNat < 2 ^ 64) (hn : i + 40 + L.toNat = n)
    (ha : (m.addr (bufPtr block o i)).toNat % 8 = 0)
    (h : Lanes s0 d i (C0.setWidth 64) (C1.setWidth 64) (C2.setWidth 64) (C3.setWidth 64) (C4.setWidth 64)) :
    run St (.while_end80_loopexit m (some (bufPtr block o i0)) (some D) (some L) (some C0) (some C1)
        (some C2) (some C3) (some C4)) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have g := bufPtr_back (block := block) (o := o) (j := i0 + 40 * D.toNat) (c := 18446744073709551576)
    rfl (by omega)
  rw [show i0 + 40 * D.toNat - 40 = i by omega] at g
  rw [run]
  simp only [Crc.crc32_z.step, mul40 hD, llvm_val, Readable.gep_plain, jump, andThen, Outcome.ok, g]
  exact while_end80_run B T hs hn ha h

theorem lanes_step32 {i : Nat} {C0 C1 C2 C3 C4 : BitVec 32}
    (h : Lanes s0 d i (C0.setWidth 64) (C1.setWidth 64) (C2.setWidth 64) (C3.setWidth 64) (C4.setWidth 64)) :
    Lanes s0 d (i + 40)
      (((steps 320 (word d i ^^^ C0.setWidth 64)).setWidth 32).setWidth 64)
      (((steps 320 (word d (i + 8) ^^^ C1.setWidth 64)).setWidth 32).setWidth 64)
      (((steps 320 (word d (i + 16) ^^^ C2.setWidth 64)).setWidth 32).setWidth 64)
      (((steps 320 (word d (i + 24) ^^^ C3.setWidth 64)).setWidth 32).setWidth 64)
      (((steps 320 (word d (i + 32) ^^^ C4.setWidth 64)).setWidth 32).setWidth 64) := by
  simp only [zext_steps320]
  exact lanes_step h

/-- The main loop, five words at a time: `r + 1` iterations left, then the last block. -/
theorem while_body15_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {D L : BitVec 64} (hD : 40 * D.toNat < 2 ^ 64) (hn : i0 + 40 * D.toNat + L.toNat = n)
    (r : Nat) :
    ∀ (i : Nat) (dec : BitVec 64) (C0 C1 C2 C3 C4 : BitVec 32), dec.toNat = r + 1 →
      i + 40 * (r + 1) + 40 = i0 + 40 * D.toNat → (m.addr (bufPtr block o i)).toNat % 8 = 0 →
      Lanes s0 d i (C0.setWidth 64) (C1.setWidth 64) (C2.setWidth 64) (C3.setWidth 64) (C4.setWidth 64) →
      run St (.while_body15 m (some dec) (some (bufPtr block o i)) (some C4) (some C0) (some C3)
          (some C1) (some C2) (some (bufPtr block o i0)) (some D) (some L)) =
        Outcome.ok (some (finish (spec s0 d n)), m) := by
  induction r with
  | zero =>
    intro i dec C0 C1 C2 C3 C4 hdec hi ha h
    have a1 := aligned_add (k := 8) ha (by omega) (by omega)
    have a2 := aligned_add (k := 16) ha (by omega) (by omega)
    have a3 := aligned_add (k := 24) ha (by omega) (by omega)
    have a4 := aligned_add (k := 32) ha (by omega) (by omega)
    have a5 := aligned_add (k := 40) ha (by omega) (by omega)
    have hd : (dec + 18446744073709551615#64).toNat = dec.toNat - 1 :=
      toNat_dec 1 rfl (by omega) (by omega)
    have h' := lanes_step32 h
    exec B, T
    split
    · exact while_end80_loopexit_run B T hs (by omega) hD (by omega) a5 h'
    · omega
  | succ r ih =>
    intro i dec C0 C1 C2 C3 C4 hdec hi ha h
    have a1 := aligned_add (k := 8) ha (by omega) (by omega)
    have a2 := aligned_add (k := 16) ha (by omega) (by omega)
    have a3 := aligned_add (k := 24) ha (by omega) (by omega)
    have a4 := aligned_add (k := 32) ha (by omega) (by omega)
    have a5 := aligned_add (k := 40) ha (by omega) (by omega)
    have hd : (dec + 18446744073709551615#64).toNat = dec.toNat - 1 :=
      toNat_dec 1 rfl (by omega) (by omega)
    have h' := lanes_step32 h
    exec B, T
    split
    · omega
    · exact ih (i + 40) _ _ _ _ _ _ (by omega) (by omega) a5 h'

theorem toNat_div40 (L : BitVec 64) : (L / 40#64).toNat = L.toNat / 40 := by
  simp [BitVec.toNat_udiv]

/-- What's left over after whole blocks of 40. -/
theorem toNat_left {L : BitVec 64} :
    ((L / 40#64) * 18446744073709551576#64 + L).toNat = L.toNat % 40 := by
  have hK : 18446744073709551576#64 = -(40#64) := by decide
  have e : (L / 40#64) * 18446744073709551576#64 + L = L - (L / 40#64) * 40#64 := by
    rw [hK, BitVec.mul_neg, BitVec.sub_eq_add_neg, BitVec.add_comm]
  have hD := toNat_div40 L
  have hmul : ((L / 40#64) * 40#64).toNat = 40 * (L.toNat / 40) := by
    simp only [BitVec.toNat_mul, hD, BitVec.toNat_ofNat]
    omega
  have hle : (L / 40#64) * 40#64 ≤ L := by
    rw [BitVec.le_def, hmul]; omega
  rw [e, BitVec.toNat_sub_of_le hle, hmul]
  omega

/-- Past the alignment loop, the braid proper. -/
theorem while_end_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (hL : 40 ≤ L.toNat) (hi : i + L.toNat = n)
    (ha : (m.addr (bufPtr block o i)).toNat % 8 = 0) :
    run St (.while_end m (some L) (some (bufPtr block o i)) (some (spec s0 d i))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hD := toNat_div40 L
  have hleft := toNat_left (L := L)
  have hX := spec_lt hs d i
  have hLt := L.isLt
  have hb : (L / 40#64).toNat < 4611686018427387904 := by omega
  have hdec : (L / 40#64 + 18446744073709551615#64).toNat = (L / 40#64).toNat - 1 :=
    toNat_dec 1 rfl (by omega) (by omega)
  exec B, T
  split
  · exact while_end80_run B T hs (by omega) ha (lanes_start s0 d i)
  · have hl : Lanes s0 d i (((spec s0 d i).setWidth 32).setWidth 64) ((0#32).setWidth 64)
        ((0#32).setWidth 64) ((0#32).setWidth 64) ((0#32).setWidth 64) := by
      have e : ((spec s0 d i).setWidth 32).setWidth 64 = spec s0 d i := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth]
        omega
      rw [e]
      exact lanes_start s0 d i
    exec B, T
    exact while_body15_run B T hs (D := L / 40#64) (by omega) (by omega) ((L / 40#64).toNat - 2) i _ _ _ _ _ _
      (by omega) (by omega) ha hl

/-- The byte loop that gets the pointer to a multiple of eight, unrolled into eight blocks. The eighth
can't be reached: one of the eight addresses before it is a multiple of eight. -/
theorem while_body_7_run {i0 : Nat} {R : Outcome (Val 64 × Mem)} {L : Val 64} {p : PtrVal} {x : Val 64}
    (hA : (m.addr (bufPtr block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr block o i0)).toNat % 8 + 7 < 8) :
    run St (.while_body_7 m (some (bufPtr block o i0)) L p x) = R := by
  omega

theorem while_body_6_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr block o i0)).toNat % 8 + 6 < 8) :
    run St (.while_body_6 m (some (bufPtr block o i0)) (some L) (some (bufPtr block o (i0 + 6))) (some (spec s0 d (i0 + 6)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551609#64).toNat = L.toNat - 7 := toNat_dec 7 rfl (by omega) (by omega)
  have haddr := addr_bufPtr m block o i0 7
  have hm := addr_mod8 (m.addr (bufPtr block o i0)) (k := 7) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_7_run hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_5_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr block o i0)).toNat % 8 + 5 < 8) :
    run St (.while_body_5 m (some (bufPtr block o i0)) (some L) (some (bufPtr block o (i0 + 5))) (some (spec s0 d (i0 + 5)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551610#64).toNat = L.toNat - 6 := toNat_dec 6 rfl (by omega) (by omega)
  have haddr := addr_bufPtr m block o i0 6
  have hm := addr_mod8 (m.addr (bufPtr block o i0)) (k := 6) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_6_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_4_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr block o i0)).toNat % 8 + 4 < 8) :
    run St (.while_body_4 m (some (bufPtr block o i0)) (some L) (some (bufPtr block o (i0 + 4))) (some (spec s0 d (i0 + 4)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551611#64).toNat = L.toNat - 5 := toNat_dec 5 rfl (by omega) (by omega)
  have haddr := addr_bufPtr m block o i0 5
  have hm := addr_mod8 (m.addr (bufPtr block o i0)) (k := 5) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_5_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_3_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr block o i0)).toNat % 8 + 3 < 8) :
    run St (.while_body_3 m (some (bufPtr block o i0)) (some L) (some (bufPtr block o (i0 + 3))) (some (spec s0 d (i0 + 3)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551612#64).toNat = L.toNat - 4 := toNat_dec 4 rfl (by omega) (by omega)
  have haddr := addr_bufPtr m block o i0 4
  have hm := addr_mod8 (m.addr (bufPtr block o i0)) (k := 4) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_4_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_2_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr block o i0)).toNat % 8 + 2 < 8) :
    run St (.while_body_2 m (some (bufPtr block o i0)) (some L) (some (bufPtr block o (i0 + 2))) (some (spec s0 d (i0 + 2)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551613#64).toNat = L.toNat - 3 := toNat_dec 3 rfl (by omega) (by omega)
  have haddr := addr_bufPtr m block o i0 3
  have hm := addr_mod8 (m.addr (bufPtr block o i0)) (k := 3) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_3_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_1_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr block o i0)).toNat % 8 + 1 < 8) :
    run St (.while_body_1 m (some (bufPtr block o i0)) (some L) (some (bufPtr block o (i0 + 1))) (some (spec s0 d (i0 + 1)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551614#64).toNat = L.toNat - 2 := toNat_dec 2 rfl (by omega) (by omega)
  have haddr := addr_bufPtr m block o i0 2
  have hm := addr_mod8 (m.addr (bufPtr block o i0)) (k := 2) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_2_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_run (B : Readable m block o n d) (T : Tables m) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr block o i0)).toNat % 8 + 0 < 8) :
    run St (.while_body m (some (bufPtr block o i0)) (some L) (some (spec s0 d i0))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551615#64).toNat = L.toNat - 1 := toNat_dec 1 rfl (by omega) (by omega)
  have haddr := addr_bufPtr m block o i0 1
  have hm := addr_mod8 (m.addr (bufPtr block o i0)) (k := 1) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_1_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_cond_preheader_run (B : Readable m block o n d) (T : Tables m)
    (hs : s0.toNat < 4294967296) {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : L.toNat = n) :
    run St (.while_cond_preheader m (some (bufPtr block o 0)) (some L) (some (spec s0 d 0))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hi' : 0 + L.toNat = n := by omega
  exec B, T
  split
  · exact while_end_run B T hs (by omega) hi' (by omega)
  · exact while_body_run B T hs hL hi' (by omega) (by omega)

/-- Reading `len` bytes of a buffer, `crc32_z` returns the CRC of RFC 1952 and leaves memory as it
found it, and being `ok` also says it never hits undefined behavior or poison on the way. -/
theorem crc32_z_correct {crc len : BitVec 64} (B : Readable m block o len.toNat d) (T : Tables m)
    (hnn : m.addr (bufPtr block o 0) ≠ 0#64) :
    crc32_z (some crc) (some (bufPtr block o 0)) (some len) m =
      Outcome.ok (some (finish (spec (start crc) d len.toNat)), m) := by
  have hnn' : (m.addr (bufPtr block o 0)).toNat ≠ 0 := fun e => hnn (BitVec.eq_of_toNat_eq e)
  have hnull : m.addr Ptr.null = 0#64 := rfl
  have hs : (start crc).toNat < 4294967296 := by
    have h : start crc < 4294967296#64 := by simp only [start]; bv_decide
    simpa [BitVec.lt_def] using h
  have h0 : (crc &&& 4294967295#64) ^^^ 4294967295#64 = spec (start crc) d 0 := rfl
  simp only [crc32_z, noundef_some]
  rw [run]
  simp only [Crc.crc32_z.step, Mem.toVal, hnull, llvm_val, beq_toNat, decide_eq_true_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, jump, andThen, Outcome.ok]
  split
  · omega
  · rw [run]
    simp only [Crc.crc32_z.step, llvm_val, ult_toNat, decide_eq_true_eq, h0,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, jump, andThen, Outcome.ok]
    split
    · exact while_cond_preheader_run B T hs (by omega) rfl
    · exact if_end216_run B T hs (Nat.zero_add _)

/-- zlib's documented way to get the initial value: a null buffer gives 0. -/
theorem crc32_z_null (crc len : BitVec 64) :
    crc32_z (some crc) (some Ptr.null) (some len) m = Outcome.ok (some 0#64, m) := by
  simp only [crc32_z, noundef_some]
  rw [run]
  simp only [Crc.crc32_z.step, Mem.toVal, llvm_val, jump, andThen, Outcome.ok]
  rw [show (m.addr Ptr.null == m.addr Ptr.null) = true by simp]
  simp only [ite_true]
  rw [run]
  simp [Crc.crc32_z.step, ret, Outcome.ok, Val.range, BitVec.ult]

/-- The spec gives the published check value of CRC-32, for "123456789". -/
example : finish (spec (start 0#64) (fun i => BitVec.ofNat 8
    ([49, 50, 51, 52, 53, 54, 55, 56, 57].getD i 0)) 9) = 0xCBF43926#64 := by decide +kernel

/-- The theorem on a real buffer, which shows its hypotheses can all hold at once. -/
theorem crc32_z_check_value :
    let init : Array Nat := #[49, 50, 51, 52, 53, 54, 55, 56, 57]
    let m := Crc.initial.addGlobal 100 init.size false init
    crc32_z (some 0#64) (some (bufPtr 100 0 0)) (some 9#64) m = Outcome.ok (some 0xCBF43926#64, m) := by
  intro init m
  have B := Readable.ofGlobal Crc.initial 100 init (by decide) (by decide) (by decide)
  have T : Tables m := ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩
  have hnn : m.addr (bufPtr 100 0 0) ≠ 0#64 := by decide
  rw [crc32_z_correct (len := 9#64) B T hnn]
  congr 3
  decide +kernel

#print axioms crc32_z_correct
#print axioms crc32_z_check_value

end CrcProof
