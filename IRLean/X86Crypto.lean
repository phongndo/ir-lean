import IRLean.Vec

/-! x86's carry-less multiplication, AES rounds and arithmetic in GF(2^8), following the pseudo-code in Intel's
Software Developer's Manual, volume 2: PCLMULQDQ, AESENC, AESENCLAST, AESDEC, AESDECLAST, AESIMC and AESKEYGENASSIST,
and the VEX and EVEX forms of the first five on 256 and 512 bits, which do the same to each 128-bit block, and GFNI's
GF2P8AFFINEQB, GF2P8AFFINEINVQB and GF2P8MULB.

LangRef 23.1.3 doesn't define target intrinsics, nor what poison does to them. As in `IRLean.X86`, a lane of the
result is poison when a lane it's computed from is. Which those are isn't the same for each:

- PCLMULQDQ multiplies one quadword of each operand, in each 128-bit block, and doesn't read the other, so poison in
  a quadword the immediate doesn't pick doesn't reach the result. LLVM reads it the same way: at the pin,
  `instCombineIntrinsic` in `llvm/lib/Target/X86/X86InstCombineIntrinsic.cpp` demands of each operand only the
  quadwords the immediate picks.
- An AES round's `ShiftRows` moves bytes between the two quadwords of the state, so each quadword of the result is
  computed from both, and from the same quadword of the round key, which is only XORed in.
- AESIMC and AESKEYGENASSIST compute each quadword of the result from the same quadword of their operand:
  `InvMixColumns` works on each 32-bit column, and AESKEYGENASSIST's low half reads bits 63 to 32, and its high half
  bits 127 to 96.
- GFNI's affine maps compute each byte from that byte of the first operand and the whole quadword of the second, the
  matrix, that the byte is in. GF2P8MULB is lane by lane.

Neither Alive2 nor LLVM's constant folder computes any of these at the pin, so only the processor checks the values,
in `tests/x86native.py`, which can't see poison. `tests/x86check.py` checks PCLMULQDQ's poison rule against what
InstCombine does: it leaves a call whose picked quadwords have values, with the others replaced by poison, and
folds one whose picked quadwords are all poison to zero, which refines poison. Nothing but this file says what
poison does to the AES instructions. -/

namespace IRLean.X86

/-- The carry-less product of two 64-bit numbers, 128 bits: bit `i` is the XOR, over `j`, of `x[j] && y[i - j]`,
which is PCLMULQDQ's `TmpB[i]`. So it's the XOR of `y <<< j` for each bit `j` of `x`, and bit 127 is 0. -/
@[llvm] def clmul64 (x y : BitVec 64) : BitVec 128 :=
  (List.range 64).foldl (fun acc j => if x.getLsbD j then acc ^^^ (y.setWidth 128 <<< j) else acc) 0

/-- `llvm.x86.pclmulqdq`, and `.256` and `.512`, PCLMULQDQ and VPCLMULQDQ: each 128-bit block of the result is the
carry-less product of one quadword of that block of `a` and one of `b`, the high one of `a` if bit 0 of `imm` is set
and of `b` if bit 4 is, and the low one otherwise. The other bits of `imm` aren't read.

Both lanes of a block are poison if a quadword `imm` picks is. The one it doesn't pick isn't read. -/
@[llvm] def pclmulqdq (imm : Nat) (a b : Vec n 64) : Vec n 64 :=
  Vector.ofFn fun i =>
    let block := 2 * (i.val / 2)
    match a.lane (block + (if imm.testBit 0 then 1 else 0)), b.lane (block + (if imm.testBit 4 then 1 else 0)) with
    | some x, some y => some ((clmul64 x y).extractLsb' (64 * (i.val % 2)) 64)
    | _, _ => none

/-! AES. The SDM writes each instruction with the transformations of FIPS 197, on a state of 16 bytes: its
`s[r, c]`, row `r` of column `c`, is byte `r + 4 c`, and byte `i` is bits `8 i` to `8 i + 7`. -/

/-- FIPS 197's S-box, its table 4: the inverse in GF(2^8), then an affine map. -/
def sbox : Array (BitVec 8) := #[
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]

/-- FIPS 197's inverse S-box, its table 6. -/
def invSbox : Array (BitVec 8) := #[
    0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
    0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
    0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
    0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
    0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
    0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
    0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
    0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
    0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
    0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
    0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
    0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
    0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
    0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
    0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d]

@[llvm] def subByte (x : BitVec 8) : BitVec 8 := sbox.getD x.toNat 0

@[llvm] def invSubByte (x : BitVec 8) : BitVec 8 := invSbox.getD x.toNat 0

/-- Multiplication in GF(2^8), FIPS 197's `•`: polynomials over GF(2), modulo `x^8 + x^4 + x^3 + x + 1`. -/
@[llvm] def gfmul (a b : BitVec 8) : BitVec 8 :=
  ((List.range 8).foldl
      (fun (acc : BitVec 8 × BitVec 8) j =>
        let (sum, x) := acc
        (if b.getLsbD j then sum ^^^ x else sum, (x <<< 1) ^^^ (if x.msb then 0x1b#8 else 0)))
      (0, a)).1

/-- Byte `i` of a value, from the lowest. -/
@[llvm] def byteOf (s : BitVec w) (i : Nat) : BitVec 8 := s.extractLsb' (8 * i) 8

/-- The value of `k` bytes whose byte `i` is `f i`. -/
@[llvm] def ofBytes (k : Nat) (f : Nat → BitVec 8) : BitVec w :=
  (List.range k).foldr (fun i acc => (acc <<< 8) ||| (f i).setWidth w) 0

/-- `ShiftRows`: row `r` moves left by `r` columns. -/
@[llvm] def shiftRows (s : BitVec 128) : BitVec 128 :=
  ofBytes 16 fun i => byteOf s (i % 4 + 4 * ((i / 4 + i % 4) % 4))

/-- `InvShiftRows`: row `r` moves right by `r` columns. -/
@[llvm] def invShiftRows (s : BitVec 128) : BitVec 128 :=
  ofBytes 16 fun i => byteOf s (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4))

/-- `SubBytes`, and `SubWord` on 32 bits: the S-box on each byte. -/
@[llvm] def subBytes (s : BitVec w) : BitVec w := ofBytes (w / 8) fun i => subByte (byteOf s i)

/-- `InvSubBytes`: the inverse S-box on each byte. -/
@[llvm] def invSubBytes (s : BitVec w) : BitVec w := ofBytes (w / 8) fun i => invSubByte (byteOf s i)

/-- `MixColumns`, on a value of whole 32-bit columns: each column `a` becomes `b`, with
`b[r] = 2 • a[r] ⊕ 3 • a[r + 1] ⊕ a[r + 2] ⊕ a[r + 3]`, rows counted modulo 4. -/
@[llvm] def mixColumns (s : BitVec w) : BitVec w :=
  ofBytes (w / 8) fun i =>
    let a (k : Nat) := byteOf s (4 * (i / 4) + (i % 4 + k) % 4)
    gfmul 2 (a 0) ^^^ gfmul 3 (a 1) ^^^ a 2 ^^^ a 3

/-- `InvMixColumns`: `b[r] = 14 • a[r] ⊕ 11 • a[r + 1] ⊕ 13 • a[r + 2] ⊕ 9 • a[r + 3]`. -/
@[llvm] def invMixColumns (s : BitVec w) : BitVec w :=
  ofBytes (w / 8) fun i =>
    let a (k : Nat) := byteOf s (4 * (i / 4) + (i % 4 + k) % 4)
    gfmul 14 (a 0) ^^^ gfmul 11 (a 1) ^^^ gfmul 13 (a 2) ^^^ gfmul 9 (a 3)

/-- A round of AES on each 128-bit block: `f` of the block of `a`, XORed with the round key.

A quadword of the result is poison if either quadword of that block of `a` is, since each round moves bytes between
them, or that quadword of the key. -/
@[llvm] def aesRound (f : BitVec 128 → BitVec 128) (a key : Vec n 64) : Vec n 64 :=
  Vector.ofFn fun i =>
    match a.lane (2 * (i.val / 2)), a.lane (2 * (i.val / 2) + 1), key.lane i with
    | some lo, some hi, some k => some ((f (hi ++ lo)).extractLsb' (64 * (i.val % 2)) 64 ^^^ k)
    | _, _, _ => none

/-- `llvm.x86.aesni.aesenc`, and `.256` and `.512`, AESENC and VAESENC: `ShiftRows`, `SubBytes`, `MixColumns`, then
the round key. -/
@[llvm] def aesenc (a key : Vec n 64) : Vec n 64 := aesRound (fun s => mixColumns (subBytes (shiftRows s))) a key

/-- `llvm.x86.aesni.aesenclast`, AESENCLAST: a last round, without `MixColumns`. -/
@[llvm] def aesenclast (a key : Vec n 64) : Vec n 64 := aesRound (fun s => subBytes (shiftRows s)) a key

/-- `llvm.x86.aesni.aesdec`, AESDEC: `InvShiftRows`, `InvSubBytes`, `InvMixColumns`, then the round key. This is a
round of FIPS 197's equivalent inverse cipher, whose key goes in after `InvMixColumns`, not before it. -/
@[llvm] def aesdec (a key : Vec n 64) : Vec n 64 :=
  aesRound (fun s => invMixColumns (invSubBytes (invShiftRows s))) a key

/-- `llvm.x86.aesni.aesdeclast`, AESDECLAST: a last round, without `InvMixColumns`. -/
@[llvm] def aesdeclast (a key : Vec n 64) : Vec n 64 := aesRound (fun s => invSubBytes (invShiftRows s)) a key

/-- `llvm.x86.aesni.aesimc`, AESIMC: `InvMixColumns`. Each quadword is two columns, so this is lane by lane. -/
@[llvm] def aesimc (a : Vec n 64) : Vec n 64 := Vec.map (fun x => x.map invMixColumns) a

/-- `llvm.x86.aesni.aeskeygenassist`, AESKEYGENASSIST. With `X1` bits 63 to 32 of the operand and `X3` bits 127 to
96, the result's four 32-bit words are `SubWord X1`, `RotWord (SubWord X1) ⊕ RCON`, `SubWord X3` and
`RotWord (SubWord X3) ⊕ RCON`, lowest first. `RotWord` moves the low byte to the top, and `RCON` is `imm`'s low eight
bits. So each quadword is computed from the high half of the same quadword, lane by lane. -/
@[llvm] def aeskeygenassist (imm : Nat) (a : Vec n 64) : Vec n 64 :=
  Vec.map
    (fun x =>
      x.map fun x =>
        let word : BitVec 32 := subBytes (x.extractLsb' 32 32)
        (word.rotateRight 8 ^^^ BitVec.ofNat 32 (imm % 256)) ++ word)
    a

/-! GFNI: arithmetic on bytes as elements of GF(2^8), AES's field. -/

/-- The inverse in GF(2^8), with 0 for 0: the 254th power. -/
@[llvm] def gfinv (x : BitVec 8) : BitVec 8 :=
  ((List.range 7).foldl
      (fun (acc : BitVec 8 × BitVec 8) _ =>
        let square := gfmul acc.2 acc.2
        (gfmul acc.1 square, square))
      (1, x)).1

/-- GFNI's `affine_byte`: bit `i` of the result is the parity of `x` ANDed with byte `7 - i` of the matrix, XORed
with bit `i` of `imm`. -/
@[llvm] def affineByte (matrix : BitVec 64) (x : BitVec 8) (imm : Nat) : BitVec 8 :=
  (List.range 8).foldl
    (fun acc i =>
      let row := byteOf matrix (7 - i) &&& x
      let parity := (List.range 8).foldl (fun p j => p != row.getLsbD j) false
      if parity != imm.testBit i then acc ||| (1#8 <<< i) else acc)
    0

/-- GF2P8AFFINEQB and GF2P8AFFINEINVQB: byte `i` of the result is `affineByte` of `f` of byte `i` of `x`, with the
quadword of `matrix` that byte `i` is in, its bytes `8 (i / 8)` to `8 (i / 8) + 7`.

A byte is poison when that byte of `x` is, or any of those eight bytes of `matrix`. -/
@[llvm] def affine (f : BitVec 8 → BitVec 8) (imm : Nat) (x matrix : Vec n 8) : Vec n 8 :=
  Vector.ofFn fun i =>
    let rows := (List.range 8).foldr
      (fun j acc =>
        match matrix.lane (8 * (i.val / 8) + j), acc with
        | some b, some m => some ((m <<< 8) ||| b.setWidth 64)
        | _, _ => none)
      (some 0#64)
    match x[i], rows with
    | some b, some m => some (affineByte m (f b) imm)
    | _, _ => none

/-- `llvm.x86.vgf2p8affineqb.*`, GF2P8AFFINEQB: an affine map over GF(2) on each byte. -/
@[llvm] def gf2p8affineqb (imm : Nat) (x matrix : Vec n 8) : Vec n 8 := affine id imm x matrix

/-- `llvm.x86.vgf2p8affineinvqb.*`, GF2P8AFFINEINVQB: the same on each byte's inverse in GF(2^8). -/
@[llvm] def gf2p8affineinvqb (imm : Nat) (x matrix : Vec n 8) : Vec n 8 := affine gfinv imm x matrix

/-- `llvm.x86.vgf2p8mulb.*`, GF2P8MULB: the product in GF(2^8) of each two bytes. -/
@[llvm] def gf2p8mulb (a b : Vec n 8) : Vec n 8 :=
  Vec.map2
    (fun x y =>
      match x, y with
      | some x, some y => some (gfmul x y)
      | _, _ => none)
    a b

end IRLean.X86
