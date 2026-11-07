import LlvmXxhash
import Kit

/-! `llvm::xxh3_64bits` from `llvm/lib/Support/xxhash.cpp`, for inputs of at most 16 bytes, against XXH3's definition for those
lengths with no seed. What it does above 16 bytes is three more algorithms, which aren't covered here. -/

set_option linter.unusedSimpArgs false

namespace Llvm.Xxhash

open IRLean LlvmXxhash

/-- `n` bytes from `i`, as a little-endian number. -/
def read (d : Nat → BitVec 8) (i : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (d i).toNat + 256 * read d (i + 1) n

def word32 (d : Nat → BitVec 8) (i : Nat) : BitVec 32 := BitVec.ofNat 32 (read d i 4)

def word64 (d : Nat → BitVec 8) (i : Nat) : BitVec 64 := BitVec.ofNat 64 (read d i 8)

variable {m : Mem} {t : List Tag} {block o n : Nat} {d : Nat → BitVec 8}

theorem load32 (B : Reachable m t block o n d) {i : Nat} (h : i + 4 ≤ n) :
    Mem.loadInt 32 m (some (bufPtr t block o i)) 1 = Outcome.ok (some (word32 d i)) := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := B.alloc
  have off : (BitVec.ofNat 64 (o + i)).toNat = o + i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have fits : ¬ o + i + 32 / 8 > a.size := by omega
  have hc := B.allowed a ha (BitVec.ofNat 64 (o + i))
  have hv : ∀ j, j < 4 → m.visible (bufPtr t block o i) a (o + i + j) = .val (d (i + j)) := by
    intro j hj
    have hw := B.clean a ha (i + j) (by omega) (BitVec.ofNat 64 (o + i))
    have hb := hd (i + j) (by omega)
    rw [← Nat.add_assoc] at hw hb
    simp only [Mem.visible, bufPtr, hw, Bool.false_eq_true, ite_false, hb]
  have e0 := hv 0 (by omega)
  have e1 := hv 1 (by omega)
  have e2 := hv 2 (by omega)
  have e3 := hv 3 (by omega)
  simp only [bufPtr] at e0 e1 e2 e3
  have hne : ((1 : Nat) != 1 && (m.addr { block := block, offset := BitVec.ofNat 64 (o + i), tags := t }).toNat % 1 != 0) = false := rfl
  simp only [Mem.loadInt, Mem.access, ha, bufPtr, off, fits, hne, Bool.false_eq_true, ite_false, hc, Mem.read, List.range,
    List.range.loop, List.map, e0, e1, e2, e3, Mem.collect, Outcome.ok, word32, read]
  simp [Nat.add_assoc]

theorem load64 (B : Reachable m t block o n d) {i : Nat} (h : i + 8 ≤ n) :
    Mem.loadInt 64 m (some (bufPtr t block o i)) 1 = Outcome.ok (some (word64 d i)) := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := B.alloc
  have off : (BitVec.ofNat 64 (o + i)).toNat = o + i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have fits : ¬ o + i + 64 / 8 > a.size := by omega
  have hc := B.allowed a ha (BitVec.ofNat 64 (o + i))
  have hv : ∀ j, j < 8 → m.visible (bufPtr t block o i) a (o + i + j) = .val (d (i + j)) := by
    intro j hj
    have hw := B.clean a ha (i + j) (by omega) (BitVec.ofNat 64 (o + i))
    have hb := hd (i + j) (by omega)
    rw [← Nat.add_assoc] at hw hb
    simp only [Mem.visible, bufPtr, hw, Bool.false_eq_true, ite_false, hb]
  have e0 := hv 0 (by omega)
  have e1 := hv 1 (by omega)
  have e2 := hv 2 (by omega)
  have e3 := hv 3 (by omega)
  have e4 := hv 4 (by omega)
  have e5 := hv 5 (by omega)
  have e6 := hv 6 (by omega)
  have e7 := hv 7 (by omega)
  simp only [bufPtr] at e0 e1 e2 e3 e4 e5 e6 e7
  have hne : ((1 : Nat) != 1 && (m.addr { block := block, offset := BitVec.ofNat 64 (o + i), tags := t }).toNat % 1 != 0) = false := rfl
  simp only [Mem.loadInt, Mem.access, ha, bufPtr, off, fits, hne, Bool.false_eq_true, ite_false, hc, Mem.read, List.range,
    List.range.loop, List.map, e0, e1, e2, e3, e4, e5, e6, e7, Mem.collect, Outcome.ok, word64, read]
  simp [Nat.add_assoc]

/-- Stepping back from the end of the buffer, by an offset `D` that's how `-k` comes out. -/
theorem gep_back (B : Reachable m t block o n d) {i k : Nat} (D : BitVec 64) (hD : D.toNat = 2 ^ 64 - k) (hk : k ≤ i) (hi : i ≤ n)
    (hk0 : 0 < k) (hk8 : k ≤ 8) :
    Mem.gep m (some (bufPtr t block o i)) (some D) (inbounds := true) = some (bufPtr t block o (i - k)) := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := B.alloc
  have haddr := B.toNat_addr hi
  have hoff : (BitVec.ofNat 64 (o + i)).toNat = o + i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hmsb : D.msb = true := by
    rw [BitVec.msb_eq_decide, hD]
    simp only [decide_eq_true_eq]
    omega
  have hneg : (-D).toNat = k := by
    rw [BitVec.toNat_neg, hD]
    omega
  have hwrap : Mem.addressWraps (m.addr (bufPtr t block o i)) D = false := by
    simp only [Mem.addressWraps, hmsb, ite_true, BitVec.ult, decide_eq_false_iff_not, hneg]
    omega
  have hsum : BitVec.ofNat 64 (o + i) + D = BitVec.ofNat 64 (o + (i - k)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hoff, hD, BitVec.toNat_ofNat]
    omega
  have hne : (D != 0#64) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro e
    rw [e] at hD
    simp at hD
    omega
  have htn : (BitVec.ofNat 64 (o + (i - k))).toNat = o + (i - k) := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [Mem.gep, bufPtr, Bool.false_and, Bool.false_eq_true, ite_false, Bool.true_or, Bool.true_and, hwrap, hne, ite_true, ha, hoff, hsum, htn]
  rw [ite_eq_left ⟨by omega, by omega⟩]

theorem mul128_ok (a b : BitVec 64) :
    Val.mul (some (a.setWidth 128)) (some (b.setWidth 128)) (nuw := true) = some (a.setWidth 128 * b.setWidth 128) := by
  apply Val.mul_ok
  have ha := a.isLt
  have hb := b.isLt
  have hm : a.toNat * b.toNat < 2 ^ 128 := by
    calc a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
      _ < 2 ^ 128 := by decide
  simp only [Bool.true_and, Bool.false_and, Bool.or_false, BitVec.umulOverflow, decide_eq_false_iff_not, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-! ### XXH3, up to 16 bytes -/

/-- XXH3's default secret, as far as these lengths read it. -/
def secretBytes : List Nat :=
  [0xb8, 0xfe, 0x6c, 0x39, 0x23, 0xa4, 0x4b, 0xbe, 0x7c, 0x01, 0x81, 0x2c, 0xf7, 0x21, 0xad, 0x1c,
   0xde, 0xd4, 0x6d, 0xe9, 0x83, 0x90, 0x97, 0xdb, 0x72, 0x40, 0xa4, 0xa4, 0xb7, 0xb3, 0x67, 0x1f,
   0xcb, 0x79, 0xe6, 0x4e, 0xcc, 0xc0, 0xe5, 0x78, 0x82, 0x5a, 0xd0, 0x7d, 0xcc, 0xff, 0x72, 0x21,
   0xb8, 0x08, 0x46, 0x74, 0xf7, 0x43, 0x24, 0x8e, 0xe0, 0x35, 0x90, 0xe6, 0x81, 0x3a, 0x26, 0x4c,
   0x3c, 0x28, 0x52, 0xbb, 0x91, 0xc3, 0x00, 0xcb]

def secret32 (k : Nat) : BitVec 32 := word32 (fun i => BitVec.ofNat 8 (secretBytes.getD i 0)) k

def secret64 (k : Nat) : BitVec 64 := word64 (fun i => BitVec.ofNat 8 (secretBytes.getD i 0)) k

def prime64_2 : BitVec 64 := 14029467366897019727#64
def prime64_3 : BitVec 64 := 1609587929392839161#64
def primeMx1 : BitVec 64 := 0x165667919E3779F9#64
def primeMx2 : BitVec 64 := 0x9FB21C651E98DF25#64

/-- XXH64's avalanche, as XXH3 uses it. -/
def avalanche64 (h : BitVec 64) : BitVec 64 :=
  let a := (h ^^^ (h >>> 33#64)) * prime64_2
  let b := (a ^^^ (a >>> 29#64)) * prime64_3
  b ^^^ (b >>> 32#64)

def avalanche3 (h : BitVec 64) : BitVec 64 :=
  let a := (h ^^^ (h >>> 37#64)) * primeMx1
  a ^^^ (a >>> 32#64)

def swap64 (x : BitVec 64) : BitVec 64 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8 ++
    x.extractLsb' 32 8 ++ x.extractLsb' 40 8 ++ x.extractLsb' 48 8 ++ x.extractLsb' 56 8

/-- A 128-bit product, folded together with xor. -/
def mulFold (a b : BitVec 64) : BitVec 64 :=
  let p := a.setWidth 128 * b.setWidth 128
  p.setWidth 64 ^^^ (p >>> 64#128).setWidth 64

def rotl (x : BitVec 64) (k : Nat) : BitVec 64 := (x <<< k) ||| (x >>> (64 - k))

/-- XXH3 with no seed, for an input of at most 16 bytes. -/
def xxh3Short (d : Nat → BitVec 8) (L : Nat) : BitVec 64 :=
  if 8 < L then
    let lo := (secret64 24 ^^^ secret64 32) ^^^ word64 d 0
    let hi := (secret64 40 ^^^ secret64 48) ^^^ word64 d (L - 8)
    avalanche3 (BitVec.ofNat 64 L + swap64 lo + hi + mulFold lo hi)
  else if 4 ≤ L then
    let input := (word32 d (L - 4)).setWidth 64 ||| ((word32 d 0).setWidth 64 <<< 32#64)
    let a := (secret64 8 ^^^ secret64 16) ^^^ input
    let b := (a ^^^ rotl a 49 ^^^ rotl a 24) * primeMx2
    let c := (b ^^^ ((b >>> 35#64) + BitVec.ofNat 64 L)) * primeMx2
    c ^^^ (c >>> 28#64)
  else if L ≠ 0 then
    let combined : BitVec 32 := ((d 0).setWidth 32 <<< 16#32) ||| ((d (L / 2)).setWidth 32 <<< 24#32) |||
      (d (L - 1)).setWidth 32 ||| (BitVec.ofNat 32 L <<< 8#32)
    avalanche64 (combined.setWidth 64 ^^^ (secret32 0 ^^^ secret32 4).setWidth 64)
  else
    avalanche64 (secret64 56 ^^^ secret64 64)

/-! The spec gives the values in LLVM's own test, `llvm/unittests/Support/xxhashTest.cpp`, on its buffer. -/

def testState : Nat → BitVec 64
  | 0 => 1#64
  | i + 1 =>
    let x := testState i
    let a := x ^^^ (x <<< 13#64)
    let b := a ^^^ (a >>> 7#64)
    b ^^^ (b <<< 17#64)

def testBytes (i : Nat) : BitVec 8 := (testState (i + 1)).setWidth 8

theorem vectors :
    xxh3Short testBytes 0 = 0x2d06800538d394c2#64 ∧ xxh3Short testBytes 1 = 0xd0d496e05c553485#64 ∧
    xxh3Short testBytes 2 = 0x84d625edb7055eac#64 ∧ xxh3Short testBytes 3 = 0x6ea2d59aca5c3778#64 ∧
    xxh3Short testBytes 4 = 0xbf65290914e80242#64 ∧ xxh3Short testBytes 5 = 0xc01fd099ad4fc8e4#64 ∧
    xxh3Short testBytes 6 = 0x9e3ea8187399caa5#64 ∧ xxh3Short testBytes 7 = 0x9da8b60540644f5a#64 ∧
    xxh3Short testBytes 8 = 0xabc1413da6cd0209#64 ∧ xxh3Short testBytes 9 = 0x8bc89400bfed51f6#64 ∧
    xxh3Short testBytes 16 = 0x7e46916754d7c9b8#64 := by
  decide +kernel

/-! ### Running it -/

theorem bswap_raw (x : BitVec 64) : Val.bswapRaw x = swap64 x := by
  simp only [Val.bswapRaw, swap64, Nat.reduceDiv, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.foldl_cons, List.foldl_nil, Nat.reduceMul, Nat.reduceSub, Nat.sub_zero]
  bv_decide

theorem gep_len (B : Reachable m t block o n d) {len : BitVec 64} (hlen : len.toNat = n) :
    Mem.gep m (some (bufPtr t block o 0)) (some len) (inbounds := true) (nuw := true) = some (bufPtr t block o n) := by
  have := B.gep (i := 0) (k := n) (by omega)
  rw [Nat.zero_add, ← hlen, BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  rw [← hlen]
  exact this

theorem bswap_some {x : BitVec 64} : Val.bswap (some x) = some (swap64 x) := by
  rw [← bswap_raw]
  rfl

theorem av3 (h : BitVec 64) : avalanche3 h =
    ((h >>> 37#64 ^^^ h) * 1609587791953885689#64) >>> 32#64 ^^^ ((h >>> 37#64 ^^^ h) * 1609587791953885689#64) := by
  simp only [avalanche3, primeMx1]
  rw [BitVec.xor_comm h, BitVec.xor_comm (_ * _)]

theorem av64 {h : BitVec 64} (h0 : h >>> 33#64 = 0#64) : avalanche64 h =
    let a := h * 14029467366897019727#64
    let b := (a >>> 29#64 ^^^ a) * 1609587929392839161#64
    b >>> 32#64 ^^^ b := by
  simp only [avalanche64, prime64_2, prime64_3, h0, BitVec.xor_zero]
  rw [BitVec.xor_comm (_ * _) (_ >>> 29#64), BitVec.xor_comm (_ * _) (_ >>> 32#64)]

theorem len_ofNat {len : BitVec 64} {n : Nat} (h : len.toNat = n) : BitVec.ofNat 64 n = len := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem run_9to16 (B : Reachable m t block o n d) {len : BitVec 64} (hlen : len.toNat = n) (h1 : 8 < n) (h2 : n ≤ 16) :
    run _ZN4llvm11xxh3_64bitsEPKhm.step (.if_then_i m (some (bufPtr t block o 0)) (some len)) =
      Outcome.ok (some (xxh3Short d n), m) := by
  have hb := gep_back B (i := n) (k := 8) 18446744073709551608#64 rfl (by omega) (by omega) (by omega) (by omega)
  rw [run]
  llvm_simp [_ZN4llvm11xxh3_64bitsEPKhm.step, load64 B (show 0 + 8 ≤ n by omega), gep_len B hlen, hb,
    load64 B (show n - 8 + 8 ≤ n by omega), bswap_some, mul128_ok]
  rw [run]
  llvm_simp [_ZN4llvm11xxh3_64bitsEPKhm.step]
  have hs1 : secret64 24 ^^^ secret64 32 = 7458650908927343033#64 := by decide +kernel
  have hs2 : secret64 40 ^^^ secret64 48 = 12634492766384443962#64 := by decide +kernel
  have hspec : xxh3Short d n = avalanche3 (BitVec.ofNat 64 n + swap64 (word64 d 0 ^^^ 7458650908927343033#64) +
      (word64 d (n - 8) ^^^ 12634492766384443962#64) +
      mulFold (word64 d 0 ^^^ 7458650908927343033#64) (word64 d (n - 8) ^^^ 12634492766384443962#64)) := by
    simp only [xxh3Short, ite_eq_left h1, hs1, hs2, BitVec.xor_comm 7458650908927343033#64, BitVec.xor_comm 12634492766384443962#64]
  rw [hspec, av3, len_ofNat hlen]
  simp only [mulFold]
  rw [BitVec.mul_comm (BitVec.setWidth 128 (word64 d 0 ^^^ 7458650908927343033#64))]
  generalize BitVec.setWidth 128 (word64 d (n - 8) ^^^ 12634492766384443962#64) *
    BitVec.setWidth 128 (word64 d 0 ^^^ 7458650908927343033#64) = p
  have efold : BitVec.setWidth 64 (p >>> 64#128 ^^^ p) = BitVec.setWidth 64 p ^^^ BitVec.setWidth 64 (p >>> 64#128) := by bv_decide
  rw [efold]
  generalize swap64 (word64 d 0 ^^^ 7458650908927343033#64) = S
  generalize word64 d (n - 8) ^^^ 12634492766384443962#64 = hi
  generalize BitVec.setWidth 64 p ^^^ BitVec.setWidth 64 (p >>> 64#128) = F
  have eacc : len + S + hi + F = S + len + hi + F := by ac_rfl
  rw [eacc]

theorem fshl_lit (x : BitVec 64) {k : Nat} (hk : 0 < k) (hk' : k < 64) :
    Val.fshlRaw x x (BitVec.ofNat 64 k) = rotl x k := by
  have h1 : (BitVec.ofNat 64 k).toNat % 64 = k := by
    simp only [BitVec.toNat_ofNat]
    omega
  simp only [Val.fshlRaw, h1, rotl]
  rw [ite_eq_right (by omega)]

theorem run_4to8 (B : Reachable m t block o n d) {len : BitVec 64} (hlen : len.toNat = n) (h1 : 4 ≤ n) (h2 : n ≤ 8) :
    run _ZN4llvm11xxh3_64bitsEPKhm.step (.if_then5_i m (some (bufPtr t block o 0)) (some len)) =
      Outcome.ok (some (xxh3Short d n), m) := by
  have hb := gep_back B (i := n) (k := 4) 18446744073709551612#64 rfl (by omega) (by omega) (by omega) (by omega)
  have hlen8 : len ≤ 8#64 := by
    show len.toNat ≤ _
    simp only [BitVec.toNat_ofNat]
    omega
  rw [run]
  llvm_simp [_ZN4llvm11xxh3_64bitsEPKhm.step, load32 B (show 0 + 4 ≤ n by omega), gep_len B hlen, hb,
    load32 B (show n - 4 + 4 ≤ n by omega), fshl_lit _ (show 0 < 49 by omega) (show 49 < 64 by omega),
    fshl_lit _ (show 0 < 24 by omega) (show 24 < 64 by omega)]
  rw [run]
  llvm_simp [_ZN4llvm11xxh3_64bitsEPKhm.step]
  have hs : secret64 8 ^^^ secret64 16 = 14355981877291832738#64 := by decide +kernel
  have hA : (secret64 8 ^^^ secret64 16) ^^^ ((word32 d (n - 4)).setWidth 64 ||| (word32 d 0).setWidth 64 <<< 32#64) =
      (BitVec.setWidth 64 (word32 d 0) <<< 32#64 ||| BitVec.setWidth 64 (word32 d (n - 4))) ^^^ 14355981877291832738#64 := by
    rw [hs]
    bv_decide
  have hn8 : ¬ 8 < n := by omega
  simp only [xxh3Short, ite_eq_right hn8, ite_eq_left h1, hA, primeMx2, len_ofNat hlen]
  generalize (BitVec.setWidth 64 (word32 d 0) <<< 32#64 ||| BitVec.setWidth 64 (word32 d (n - 4))) ^^^ 14355981877291832738#64 = A
  have e1 : A ^^^ rotl A 49 ^^^ rotl A 24 = rotl A 49 ^^^ rotl A 24 ^^^ A := by ac_rfl
  rw [e1]
  generalize (rotl A 49 ^^^ rotl A 24 ^^^ A) * 11507291218515648293#64 = b
  rw [BitVec.xor_comm b]
  generalize ((b >>> 35#64 + len ^^^ b) * 11507291218515648293#64) = c
  rw [BitVec.xor_comm c]

theorem run_1to3 (B : Reachable m t block o n d) {len : BitVec 64} (hlen : len.toNat = n) (h1 : 1 ≤ n) (h2 : n ≤ 3) :
    run _ZN4llvm11xxh3_64bitsEPKhm.step (.if_then9_i m (some (bufPtr t block o 0)) (some len)) =
      Outcome.ok (some (xxh3Short d n), m) := by
  have hlen3 : len ≤ 3#64 := by
    show len.toNat ≤ _
    simp only [BitVec.toNat_ofNat]
    omega
  have hhalf : BitVec.ofNat 64 (n / 2) = len >>> 1#64 := by
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 64 (n / 2)).toNat = (len >>> 1).toNat
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hlen, BitVec.toNat_ofNat]
    omega
  have hmid : Mem.gep m (some (bufPtr t block o 0)) (some (len >>> 1#64)) (inbounds := true) (nuw := true) =
      some (bufPtr t block o (n / 2)) := by
    rw [← hhalf]
    have := B.gep (i := 0) (k := n / 2) (by omega)
    rwa [Nat.zero_add] at this
  have hplain : Mem.gep m (some (bufPtr t block o 0)) (some len) = some (bufPtr t block o n) := by
    have := Reachable.gep_plain m t block o 0 n
    rwa [Nat.zero_add, len_ofNat hlen] at this
  have hlast : Mem.gep m (some (bufPtr t block o n)) (some 18446744073709551615#64) = some (bufPtr t block o (n - 1)) := by
    have hoff : BitVec.ofNat 64 (o + n) + 18446744073709551615#64 = BitVec.ofNat 64 (o + (n - 1)) := by
      apply BitVec.eq_of_toNat_eq
      obtain ⟨a, ha, hsz, hmax, hd⟩ := B.alloc
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    simp [Mem.gep, bufPtr, hoff]
  rw [run]
  llvm_simp [_ZN4llvm11xxh3_64bitsEPKhm.step, B.load (show 0 < n by omega), hmid, hplain, hlast, B.load (show n / 2 < n by omega),
    B.load (show n - 1 < n by omega)]
  rw [run]
  llvm_simp [_ZN4llvm11xxh3_64bitsEPKhm.step]
  have hs : (secret32 0 ^^^ secret32 4).setWidth 64 = 2267503259#64 := by decide +kernel
  have hL : BitVec.ofNat 32 n = len.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hlen]
  have hn8 : ¬ 8 < n := by omega
  have hn4 : ¬ 4 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  simp only [xxh3Short, ite_eq_right hn8, ite_eq_right hn4, ite_eq_left hn0, hs, hL]
  generalize d 0 = b0
  generalize d (n / 2) = b1
  generalize d (n - 1) = b2
  have hH : (BitVec.setWidth 32 b0 <<< 16#32 ||| BitVec.setWidth 32 b1 <<< 24#32 ||| BitVec.setWidth 32 b2 |||
        BitVec.setWidth 32 len <<< 8#32).setWidth 64 ^^^ 2267503259#64 =
      (BitVec.setWidth 64 b1 <<< 24#64 ||| BitVec.setWidth 64 b0 <<< 16#64 ||| BitVec.setWidth 64 b2 ||| len <<< 8#64) ^^^
        2267503259#64 := by bv_decide
  have hsmall : ((BitVec.setWidth 64 b1 <<< 24#64 ||| BitVec.setWidth 64 b0 <<< 16#64 ||| BitVec.setWidth 64 b2 ||| len <<< 8#64) ^^^
      2267503259#64) >>> 33#64 = 0#64 := by bv_decide
  rw [hH, av64 hsmall]

theorem run_empty : run _ZN4llvm11xxh3_64bitsEPKhm.step (.return_1 m (some 3244421341483603138#64)) =
    Outcome.ok (some (xxh3Short d 0), m) := by
  have hs : avalanche64 (secret64 56 ^^^ secret64 64) = 3244421341483603138#64 := by decide +kernel
  have h : xxh3Short d 0 = 3244421341483603138#64 := by simpa [xxh3Short] using hs
  rw [run, h]
  simp only [_ZN4llvm11xxh3_64bitsEPKhm.step, ret, Outcome.ok, noundef_some]

abbrev effects : Effects := { other := .none, arg := .read, inaccessible := .none, errno := .none }

abbrev readTag (m : Mem) : Tag := { call := m.nextCall, readonly := true, nofree := true, expires := true, noAddress := true }

/-- `llvm::xxh3_64bits`, for at most 16 readable bytes: the XXH3 of those bytes, with no seed. Longer inputs aren't covered. -/
theorem xxh3_64bits_correct {len : BitVec 64} (B : Reachable m t block o len.toNat d) (h : len.toNat ≤ 16) :
    _ZN4llvm11xxh3_64bitsEPKhm (some (bufPtr t block o 0)) (some len) m =
      Outcome.ok (some (xxh3Short d len.toNat), m.afterCall) := by
  have B' := B.enter (e := effects) (T := readTag m) (Or.inl rfl) rfl rfl rfl rfl
  have hlen16 : len < 17#64 := by
    show len.toNat < _
    simp only [BitVec.toNat_ofNat]
    omega
  have hrun : run _ZN4llvm11xxh3_64bitsEPKhm.step (.entry (m.inCall effects) (some (bufPtr (readTag m :: t) block o 0)) (some len)) =
      Outcome.ok (some (xxh3Short d len.toNat), m.inCall effects) := by
    rw [run]
    have hu : len.ult 17#64 = true := decide_eq_true hlen16
    llvm_simp [_ZN4llvm11xxh3_64bitsEPKhm.step, hu]
    rw [run]
    llvm_simp [_ZN4llvm11xxh3_64bitsEPKhm.step]
    apply ite_cases <;> intro h8
    · exact run_9to16 B' rfl (by simpa [BitVec.ult] using h8) h
    · have h8' : ¬ 8 < len.toNat := by simpa [BitVec.ult] using h8
      rw [run]
      llvm_simp [_ZN4llvm11xxh3_64bitsEPKhm.step]
      apply ite_cases <;> intro h3
      · exact run_4to8 B' rfl (by simp [BitVec.ult] at h3; omega) (by omega)
      · have h3' : ¬ 3 < len.toNat := by simpa [BitVec.ult] using h3
        rw [run]
        llvm_simp [_ZN4llvm11xxh3_64bitsEPKhm.step]
        apply ite_cases <;> intro h0
        · have hz : len = 0#64 := by simpa using h0
          subst hz
          exact run_empty
        · have hz : ¬ len.toNat = 0 := fun e => h0 (by simp [show len = 0#64 from BitVec.eq_of_toNat_eq (by simpa using e)])
          exact run_1to3 B' rfl (by omega) (by omega)
  simp only [_ZN4llvm11xxh3_64bitsEPKhm, noundef_some, Mem.call, Mem.tag, Option.map]
  rw [show run _ZN4llvm11xxh3_64bitsEPKhm.step _ = _ from hrun]
  rfl

/-- The hypotheses can all hold, on real bytes: the first nine bytes of LLVM's test's buffer give its value. -/
theorem xxh3_64bits_check_value :
    let init : Array Nat := #[(testBytes 0).toNat, (testBytes 1).toNat, (testBytes 2).toNat, (testBytes 3).toNat, (testBytes 4).toNat,
      (testBytes 5).toNat, (testBytes 6).toNat, (testBytes 7).toNat, (testBytes 8).toNat]
    let m := LlvmXxhash.initial.addGlobal 100 init.size false init
    _ZN4llvm11xxh3_64bitsEPKhm (some (bufPtr [] 100 0 0)) (some 9#64) m = Outcome.ok (some 0x8bc89400bfed51f6#64, m.afterCall) := by
  intro init m
  have B := Readable.ofGlobal LlvmXxhash.initial 100 init rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [xxh3_64bits_correct (len := 9#64) B.toReachable (by decide)]
  congr 3
  decide +kernel

end Llvm.Xxhash
