import Crc.Globals
import CrcTables

/-! What `Crc32` needs before it runs any blocks: the tables through memory, what the code computes, the
spec, and the braid. It's its own module so a change to a proof about a block doesn't check this again. -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false
open IRLean Crc

namespace CrcProof


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
    (halign : (m.addr ⟨block, BitVec.ofNat 64 (off + 4 * x), []⟩).toNat % 4 = 0) :
    Mem.loadInt 32 m (some ⟨block, BitVec.ofNat 64 (off + 4 * x), []⟩) 4 =
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
  have hc : m.check ⟨block, BitVec.ofNat 64 (off + 4 * x), []⟩
      { size := s, readonly := true, bytes := Mem.globalBytes init } false = none :=
    Mem.check_constant rfl rfl
  simp only [Mem.loadInt, Mem.access, hA, hoff, fits, if_false, halign, hc, Mem.read, Mem.visible]
  have hw : ∀ o', m.unwritten ⟨block, BitVec.ofNat 64 (off + 4 * x), []⟩
      { size := s, readonly := true, bytes := Mem.globalBytes init } o' = false :=
    fun _ => Mem.unwritten_constant rfl
  have e0 : Mem.globalBytes init (off + 4 * x + 0) = .val (BitVec.ofNat 8 (v % 256)) := by
    simp only [Mem.globalBytes, b0, g0, ite_false]
  have e1 : Mem.globalBytes init (off + 4 * x + 1) = .val (BitVec.ofNat 8 (v / 256 % 256)) := by
    simp only [Mem.globalBytes, b1, g1, ite_false]
  have e2 : Mem.globalBytes init (off + 4 * x + 2) = .val (BitVec.ofNat 8 (v / 65536 % 256)) := by
    simp only [Mem.globalBytes, b2, g2, ite_false]
  have e3 : Mem.globalBytes init (off + 4 * x + 3) = .val (BitVec.ofNat 8 (v / 16777216 % 256)) := by
    simp only [Mem.globalBytes, b3, g3, ite_false]
  have c : ((4 : Nat) != 1 && (0 : Nat) != 0) = false := rfl
  simp only [List.range, List.range.loop, List.map, c, Bool.false_eq_true, ite_false, hoff, hc, hw, e0, e1, e2,
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
structure Tables (m : Mem) (ts : List Tag) : Prop where
  crc : m.allocs g_crc_table.block = Crc.initial.allocs g_crc_table.block
  braid : m.allocs g_crc_braid_table.block = Crc.initial.allocs g_crc_braid_table.block
  crcAlign : (m.base g_crc_table.block).toNat % 4 = 0
  braidAlign : (m.base g_crc_braid_table.block).toNat % 4 = 0
  crcFits : (m.base g_crc_table.block).toNat + 1024 < 2 ^ 64
  braidFits : (m.base g_crc_braid_table.block).toNat + 8192 < 2 ^ 64
  /-- The code looks at the buffer pointer's address, to find its alignment, which its tags have to allow. -/
  addressFree : ∀ x, x ∈ ts → x.noAddress = false

theorem addr_align {m : Mem} {block k : Nat} (hb : block ≠ 0) (ha : (m.base block).toNat % 4 = 0)
    : (m.addr ⟨block, BitVec.ofNat 64 (4 * k), []⟩).toNat % 4 = 0 := by
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

variable {m : Mem} {ts : List Tag}

/-- Reads an entry of a table of 256 at offset `off` of a read-only global. -/
theorem table_load {P : Ptr} {init : Array Nat} {s off n : Nat} {f : Nat → Nat} {x : BitVec 64}
    (hA : m.allocs P.block = some { size := s, readonly := true, bytes := Mem.globalBytes init })
    (hP : P.offset = BitVec.ofNat 64 off) (hPt : P.tags = []) (hb : P.block ≠ 0)
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
  have hal : (m.addr ⟨P.block, BitVec.ofNat 64 (off + 4 * x.toNat), []⟩).toNat % 4 = 0 := by
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
      some ⟨P.block, BitVec.ofNat 64 (off + 4 * x.toNat), []⟩ := by
    rw [Mem.gep_forward hA (by simp only [hP, toff]; omega) hmax haddr (by omega), hP, hsum]
    cases P; simp_all
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

theorem crc_load (T : Tables m ts) {x : BitVec 64} (hx : x.toNat < 256) :
    Mem.loadInt 32 m
        (Mem.gep m (some g_crc_table) (Val.mul (some x) (some 4#64) (nuw := true) (nsw := true))
          (inbounds := true) (nuw := true)) 4 =
      Outcome.ok (some (entryV 8 x)) := by
  have hl : (g_crc_table_init.toList.drop 0).take 1024 =
      (List.range 256).flatMap fun e => bytes4 (stepsN 8 e) := by
    rw [List.drop_zero, crc_table_bytes]
    exact List.take_of_length_le (by rw [length_flatMap_range _ (fun e => length_bytes4 _)]; omega)
  exact table_load (s := 1024) (off := 0) T.crc rfl rfl (by simp [g_crc_table]) hl (fun _ => rfl)
    (by omega) (by omega) (by omega) T.crcAlign T.crcFits hx

/-- Reads table `k` of `crc_braid_table`, whose pointer the code writes as `P`. -/
theorem braid_load (T : Tables m ts) {P : Ptr} {k : Nat} (hP : P = ⟨2, BitVec.ofNat 64 (1024 * k), []⟩)
    (hk : k < 8) (hS : braidSlice k = braidExpected k) {x : BitVec 64} (hx : x.toNat < 256) :
    Mem.loadInt 32 m
        (Mem.gep m (some P) (Val.mul (some x) (some 4#64) (nuw := true) (nsw := true))
          (inbounds := true) (nuw := true)) 4 =
      Outcome.ok (some (entryV (320 - 8 * k) x)) := by
  subst hP
  exact table_load (s := 8192) (off := 1024 * k) T.braid rfl rfl (by simp) hS (fun _ => rfl)
    (by omega) (by omega) (by omega) T.braidAlign T.braidFits hx

/-- A table read, as the code writes it. -/
abbrev tableRead (m : Mem) (P : Ptr) (x : BitVec 64) : Outcome (Val 32) :=
  Mem.loadInt 32 m
    (Mem.gep m (some P) (Val.mul (some x) (some 4#64) (nuw := true) (nsw := true))
      (inbounds := true) (nuw := true)) 4

theorem crc_and (T : Tables m ts) (x : BitVec 64) :
    tableRead m g_crc_table (x &&& 255#64) = Outcome.ok (some (entryV 8 (x &&& 255#64))) :=
  crc_load T (and255 x)
theorem crc_byte (T : Tables m ts) (b : BitVec 8) :
    tableRead m g_crc_table (b.setWidth 64) = Outcome.ok (some (entryV 8 (b.setWidth 64))) :=
  crc_load T (zext8 b)
theorem braid0 (T : Tables m ts) (x : BitVec 64) :
    tableRead m g_crc_braid_table (x &&& 255#64) = Outcome.ok (some (entryV 320 (x &&& 255#64))) :=
  braid_load T (k := 0) rfl (by omega) braid_slice0 (and255 x)
theorem braid1 (T : Tables m ts) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 1024#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 312 (x &&& 255#64))) :=
  braid_load T (k := 1) rfl (by omega) braid_slice1 (and255 x)
theorem braid2 (T : Tables m ts) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 2048#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 304 (x &&& 255#64))) :=
  braid_load T (k := 2) rfl (by omega) braid_slice2 (and255 x)
theorem braid3 (T : Tables m ts) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 3072#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 296 (x &&& 255#64))) :=
  braid_load T (k := 3) rfl (by omega) braid_slice3 (and255 x)
theorem braid4 (T : Tables m ts) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 4096#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 288 (x &&& 255#64))) :=
  braid_load T (k := 4) rfl (by omega) braid_slice4 (and255 x)
theorem braid5 (T : Tables m ts) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 5120#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 280 (x &&& 255#64))) :=
  braid_load T (k := 5) rfl (by omega) braid_slice5 (and255 x)
theorem braid6 (T : Tables m ts) (x : BitVec 64) :
    tableRead m { g_crc_braid_table with offset := 6144#64 } (x &&& 255#64) =
      Outcome.ok (some (entryV 272 (x &&& 255#64))) :=
  braid_load T (k := 6) rfl (by omega) braid_slice6 (and255 x)
theorem braid7 (T : Tables m ts) (x : BitVec 64) :
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
    m.addr (bufPtr ts block o (i + k)) = m.addr (bufPtr ts block o i) + BitVec.ofNat 64 k := by
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

theorem load64 {block o n : Nat} {d : Nat → BitVec 8} (B : Readable m ts block o n d) {i : Nat}
    (h : i + 8 ≤ n) (ha : (m.addr (bufPtr ts block o i)).toNat % 8 = 0) :
    Mem.loadInt 64 m (some (bufPtr ts block o i)) 8 = Outcome.ok (some (word d i)) := by
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
  have hc := B.allowed a hA (BitVec.ofNat 64 (o + i))
  have w0 := B.clean a hA i (by omega) (BitVec.ofNat 64 (o + i))
  have w1 := B.clean a hA (i + 1) (by omega) (BitVec.ofNat 64 (o + i))
  have w2 := B.clean a hA (i + 2) (by omega) (BitVec.ofNat 64 (o + i))
  have w3 := B.clean a hA (i + 3) (by omega) (BitVec.ofNat 64 (o + i))
  have w4 := B.clean a hA (i + 4) (by omega) (BitVec.ofNat 64 (o + i))
  have w5 := B.clean a hA (i + 5) (by omega) (BitVec.ofNat 64 (o + i))
  have w6 := B.clean a hA (i + 6) (by omega) (BitVec.ofNat 64 (o + i))
  have w7 := B.clean a hA (i + 7) (by omega) (BitVec.ofNat 64 (o + i))
  simp only [Mem.loadInt, Mem.access, hA, bufPtr, hoff, ite_false, ha, hc, Mem.read, Mem.visible,
    List.range, List.range.loop, List.map, c, Bool.false_eq_true, Nat.add_assoc, Nat.add_zero, fits',
    word, le, Nat.reduceAdd]
  simp only [hoff, Nat.add_assoc, Nat.reduceAdd, w0, w1, w2, w3, w4, w5, w6, w7, Bool.false_eq_true, if_false,
    b0, b1, b2, b3, b4, b5, b6, b7, Mem.collect]

end CrcProof
