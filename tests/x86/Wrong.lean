import IRLean

/-! A wrong version of each definition in `IRLean.X86`, each a way of misreading Intel's pseudo-code. The checks
have to refuse them: `tests/x86native.py` fails unless the processor disagrees with each on some input to each
intrinsic that uses it, and `tests/x86check.py` unless Alive2, or LLVM's constant folder, does where it knows the
intrinsic. So a check that passes for the model is one that could have failed.

The tests put this module beside the emitted one as `X86Wrong`, and run the emitted code with each call into
`X86` a call into `X86Wrong`. -/

namespace IRLean.X86Wrong

/-- Wrong: reads `a`'s bytes as signed too. PMADDUBSW's first operand is unsigned. -/
def pmaddubsw (n : Nat) (a b : Vec m 8) : Vec n 16 :=
  Vector.ofFn fun i =>
    match a.lane (2 * i), a.lane (2 * i + 1), b.lane (2 * i), b.lane (2 * i + 1) with
    | some x0, some x1, some y0, some y1 => some (X86.ssat16 (x0.toInt * y0.toInt + x1.toInt * y1.toInt))
    | _, _, _, _ => none

/-- Wrong: saturates to 32 bits, where PMADDWD wraps. Only four copies of -32768 show it. -/
def pmaddwd (n : Nat) (a b : Vec m 16) : Vec n 32 :=
  Vector.ofFn fun i =>
    match a.lane (2 * i), a.lane (2 * i + 1), b.lane (2 * i), b.lane (2 * i + 1) with
    | some x0, some x1, some y0, some y1 =>
      some (BitVec.ofInt 32 (max (-2147483648) (min 2147483647 (x0.toInt * y0.toInt + x1.toInt * y1.toInt))))
    | _, _, _, _ => none

/-- Wrong: saturates the sum, which is VPDPBUSDS. VPDPBUSD wraps. -/
def vpdpbusd (acc : Vec n 32) (a b : Vec m 8) : Vec n 32 :=
  Vector.ofFn fun i =>
    match acc[i], X86.dot4 a b i with
    | some s, some d => some (BitVec.ofInt 32 (max (-2147483648) (min 2147483647 (s.toInt + d))))
    | _, _ => none

/-- Wrong: the second and third operands the other way round, so the table's index is `4 x + 2 z + y`. -/
def pternlog (imm : Nat) (a b c : Vec n w) : Vec n w := X86.pternlog imm a c b

/-- Wrong: bit 7 of an index doesn't zero the byte. -/
def pshufb (a b : Vec n 8) : Vec n 8 :=
  Vector.ofFn fun i =>
    match b.lane i with
    | none => none
    | some s => a.lane (i.val / 16 * 16 + s.toNat % 16)

/-- Wrong: a count of the lane's width or more is taken modulo the width, as the scalar shifts take theirs. -/
def apply : X86.Shift → BitVec w → Nat → BitVec w
  | .shl, x, c => x <<< (c % w)
  | .lshr, x, c => x >>> (c % w)
  | .ashr, x, c => x.sshiftRight (c % w)

def shiftLanes (s : X86.Shift) (a b : Vec n w) : Vec n w :=
  Vec.map2
    (fun x c =>
      match x, c with
      | some x, some c => some (apply s x c.toNat)
      | _, _ => none)
    a b

def shiftImm (s : X86.Shift) (a : Vec n w) (c : Val 32) : Vec n w :=
  match c with
  | none => HasPoison.poison
  | some c => Vec.map (fun x => x.map (apply s · c.toNat)) a

def shiftVec (s : X86.Shift) (a : Vec n w) (c : Vec m u) : Vec n w :=
  let k := 64 / u
  match (List.range k).foldr
      (fun j acc =>
        match c.lane j, acc with
        | some x, some y => some ((y <<< u) ||| x.toNat)
        | _, _ => none)
      (some 0) with
  | none => HasPoison.poison
  | some count => Vec.map (fun x => x.map (apply s · count)) a

/-- Wrong: bit 1 of the immediate picks `b`'s quadword. PCLMULQDQ reads bit 4. -/
def pclmulqdq (imm : Nat) (a b : Vec n 64) : Vec n 64 :=
  Vector.ofFn fun i =>
    let block := 2 * (i.val / 2)
    match a.lane (block + (if imm.testBit 0 then 1 else 0)), b.lane (block + (if imm.testBit 1 then 1 else 0)) with
    | some x, some y => some ((X86.clmul64 x y).extractLsb' (64 * (i.val % 2)) 64)
    | _, _ => none

/-- Wrong: `InvShiftRows`, decryption's, where AESENC has `ShiftRows`. -/
def aesenc (a key : Vec n 64) : Vec n 64 :=
  X86.aesRound (fun s => X86.mixColumns (X86.subBytes (X86.invShiftRows s))) a key

/-- Wrong: a full round, with `MixColumns`, which AESENCLAST leaves out. -/
def aesenclast (a key : Vec n 64) : Vec n 64 := X86.aesenc a key

/-- Wrong: the round key goes in before `InvMixColumns`, as in FIPS 197's inverse cipher. AESDEC is a round of
its equivalent inverse cipher, where it goes in after. -/
def aesdec (a key : Vec n 64) : Vec n 64 :=
  Vector.ofFn fun i =>
    match a.lane (2 * (i.val / 2)), a.lane (2 * (i.val / 2) + 1),
        key.lane (2 * (i.val / 2)), key.lane (2 * (i.val / 2) + 1) with
    | some lo, some hi, some klo, some khi =>
      let s := X86.invSubBytes (X86.invShiftRows (hi ++ lo)) ^^^ (khi ++ klo)
      some ((X86.invMixColumns s).extractLsb' (64 * (i.val % 2)) 64)
    | _, _, _, _ => none

/-- Wrong: `ShiftRows`, encryption's, where AESDECLAST has `InvShiftRows`. -/
def aesdeclast (a key : Vec n 64) : Vec n 64 :=
  X86.aesRound (fun s => X86.invSubBytes (X86.shiftRows s)) a key

/-- Wrong: `MixColumns`, where AESIMC has its inverse. -/
def aesimc (a : Vec n 64) : Vec n 64 := Vec.map (fun x => x.map X86.mixColumns) a

/-- Wrong: `RotWord` moves the top byte to the bottom, where AESKEYGENASSIST's moves the low byte to the top. -/
def aeskeygenassist (imm : Nat) (a : Vec n 64) : Vec n 64 :=
  Vec.map
    (fun x =>
      x.map fun x =>
        let word : BitVec 32 := X86.subBytes (x.extractLsb' 32 32)
        (word.rotateLeft 8 ^^^ BitVec.ofNat 32 (imm % 256)) ++ word)
    a

/-- Wrong: `(a + b) >>> 1`, without the 1 that makes PAVGB and PAVGW round up. -/
def pavg (a b : Vec n w) : Vec n w :=
  Vec.map2
    (fun x y =>
      match x, y with
      | some x, some y => some (((x.setWidth (w + 1) + y.setWidth (w + 1)) >>> 1).setWidth w)
      | _, _ => none)
    a b

/-- Wrong: keeps the low bits, where PACKSSWB and PACKSSDW saturate. -/
def packss (n w : Nat) (a b : Vec m u) : Vec n w := X86.pack (fun x => x.setWidth w) n a b

/-- Wrong: saturates an unsigned number, so a negative one becomes the greatest, where PACKUSWB and PACKUSDW read
theirs as signed and make it 0. -/
def packus (n w : Nat) (a b : Vec m u) : Vec n w :=
  X86.pack (fun x => if ((BitVec.allOnes w).setWidth u).ult x then BitVec.allOnes w else x.setWidth w) n a b

/-- Wrong: keeps `a`'s lane where `b`'s is 0, where PSIGN makes it 0. -/
def psign (a b : Vec n w) : Vec n w :=
  Vec.map2
    (fun x y =>
      match x, y with
      | some x, some y => some (if y.msb then -x else x)
      | _, _ => none)
    a b

/-- Wrong: the unsigned product's high half, which is PMULHUW. -/
def pmulhw (a b : Vec n 16) : Vec n 16 := X86.pmulhuw a b

/-- Wrong: the signed product's high half, which is PMULHW. -/
def pmulhuw (a b : Vec n 16) : Vec n 16 := X86.pmulhw a b

/-- Wrong: the product shifted right by 15, without rounding. -/
def pmulhrsw (a b : Vec n 16) : Vec n 16 :=
  Vec.map2
    (fun x y =>
      match x, y with
      | some x, some y => some ((x.signExtend 32 * y.signExtend 32).extractLsb' 15 16)
      | _, _ => none)
    a b

/-- Wrong: differences of signed bytes. PSADBW's are unsigned. -/
def psadbw (n : Nat) (a b : Vec m 8) : Vec n 64 :=
  Vector.ofFn fun i =>
    (List.range 8).foldl
      (fun acc k =>
        match acc, a.lane (8 * i + k), b.lane (8 * i + k) with
        | some s, some x, some y => some (s + (if x.slt y then y - x else x - y).setWidth 64)
        | _, _, _ => none)
      (some 0)

/-- Wrong: `b`'s pairs in the low half of each block and `a`'s in the high half. -/
def horizontal (f : Val w → Val w → Val w) (a b : Vec n w) : Vec n w := X86.horizontal f b a

/-- Wrong: `a`'s byte where the mask's bit 7 is set, and `b`'s otherwise. -/
def pblendvb (a b mask : Vec n 8) : Vec n 8 := X86.pblendvb b a mask

/-- Wrong: wraps, which is VPDPBUSD. -/
def vpdpbusds (acc : Vec n 32) (a b : Vec m 8) : Vec n 32 := X86.vpdpbusd acc a b

/-- Wrong: saturates, which is VPDPWSSDS. -/
def vpdpwssd (acc : Vec n 32) (a b : Vec m 16) : Vec n 32 := X86.vpdpwssds acc a b

/-- Wrong: wraps, which is VPDPWSSD. -/
def vpdpwssds (acc : Vec n 32) (a b : Vec m 16) : Vec n 32 := X86.vpdpwssd acc a b

/-- Wrong: 0 where the mask is clear, which is zeroing. The intrinsic merges, keeping `passthru`'s lane. -/
def pmov (a : Vec m u) (_passthru : Vec n w) (mask : Val k) : Vec n w :=
  X86.maskNarrow (BitVec.setWidth w) a (Vector.replicate n (some 0)) mask

/-- Wrong: saturates an unsigned number, which is VPMOVUS. -/
def pmovs (a : Vec m u) (passthru : Vec n w) (mask : Val k) : Vec n w := X86.pmovus a passthru mask

/-- Wrong: saturates a signed number to an unsigned result, as PACKUSWB does, so a lane with its top bit set
becomes 0. VPMOVUS reads its lanes as unsigned. -/
def pmovus (a : Vec m u) (passthru : Vec n w) (mask : Val k) : Vec n w :=
  X86.maskNarrow (X86.usatTo w) a passthru mask

/-- Wrong: takes all of `n` for the index, where BZHI reads its low eight bits. -/
def bzhi (x n : Val w) : Val w :=
  match x, n with
  | some x, some n => some (if n.toNat < w then x &&& ~~~(BitVec.allOnes w <<< n.toNat) else x)
  | _, _ => none

/-- Wrong: the length in the low eight bits and the start in the next, the other way round from BEXTR. -/
def bextr (x c : Val w) : Val w :=
  match x, c with
  | some x, some c => some ((x >>> (c.toNat / 256 % 256)) &&& ~~~(BitVec.allOnes w <<< (c.toNat % 256)))
  | _, _ => none

/-- Wrong: the polynomial `104C11DB7`, zlib's and Ethernet's CRC-32. The CRC32 instruction's is CRC-32C's. -/
def crc32 (crc : Val c) (data : Val k) : Val c :=
  match crc, data with
  | some crc, some data =>
    let start : BitVec (k + 32) :=
      ((X86.bitReflect data).setWidth (k + 32) <<< 32) ^^^
        ((X86.bitReflect (crc.setWidth 32)).setWidth (k + 32) <<< k)
    let rest := (List.range k).foldl
      (fun acc i => if acc.getLsbD (k + 31 - i) then acc ^^^ (0x104C11DB7#(k + 32) <<< (k - 1 - i)) else acc)
      start
    some ((X86.bitReflect (rest.setWidth 32)).setWidth c)
  | _, _ => none

/-- Wrong: CF, which is what `ptestc` returns. -/
def ptestz (a b : Vec n 64) : Val 32 := X86.ptestc a b

/-- Wrong: ZF, which is what `ptestz` returns. -/
def ptestc (a b : Vec n 64) : Val 32 := X86.ptestz a b

/-- Wrong: 1 if either flag is clear, where `ptestnzc` wants both. -/
def ptestnzc (a b : Vec n 64) : Val 32 := (X86.ptestFlags a b).map fun f => if !f.1 || !f.2 then 1 else 0

/-- Wrong: the index of the last least word, where PHMINPOSUW gives the first's. -/
def phminposuw (a : Vec n 16) : Vec n 16 :=
  let best := (List.range 7).foldl
    (fun acc i =>
      match acc, a.lane (i + 1) with
      | some (least, index), some x => if x.ule least then some (x, i + 1) else some (least, index)
      | _, _ => none)
    ((a.lane 0).map fun x => (x, 0))
  Vector.ofFn fun i =>
    if i.val = 0 then best.map (·.1) else if i.val = 1 then best.map fun b => BitVec.ofNat 16 b.2 else some 0

/-- Wrong: row `i` of the matrix for bit `i`, where GF2P8AFFINEQB takes byte `7 - i`. -/
def affineByte (matrix : BitVec 64) (x : BitVec 8) (imm : Nat) : BitVec 8 :=
  (List.range 8).foldl
    (fun acc i =>
      let row := X86.byteOf matrix i &&& x
      let parity := (List.range 8).foldl (fun p j => p != row.getLsbD j) false
      if parity != imm.testBit i then acc ||| (1#8 <<< i) else acc)
    0

def affine (f : BitVec 8 → BitVec 8) (imm : Nat) (x matrix : Vec n 8) : Vec n 8 :=
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

def gf2p8affineqb (imm : Nat) (x matrix : Vec n 8) : Vec n 8 := affine id imm x matrix

def gf2p8affineinvqb (imm : Nat) (x matrix : Vec n 8) : Vec n 8 := affine X86.gfinv imm x matrix

/-- Wrong: the product of two integers, modulo 256, where GF2P8MULB multiplies polynomials. -/
def gf2p8mulb (a b : Vec n 8) : Vec n 8 :=
  Vec.map2
    (fun x y =>
      match x, y with
      | some x, some y => some (x * y)
      | _, _ => none)
    a b

end IRLean.X86Wrong
