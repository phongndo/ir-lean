import IRLean.Lanes
import IRLean.X86

/-! x86's integer arithmetic that isn't a generic operation lane by lane: averages, packing with saturation, the
high half of a product, sums of absolute differences, sums of neighbours, and a few more, following the pseudo-code
in Intel's Software Developer's Manual, volume 2. Each is written on bit vectors, as the pseudo-code is.

LangRef 23.1.3 doesn't define target intrinsics, nor what poison does to them. As in `IRLean.X86`, a lane of the
result is poison when a lane it's computed from is, and each definition says which those are. For PSIGN and PBLENDVB
that follows Alive2 where it's more poisonous than the pseudo-code: a lane is poison when that lane of any operand
is, even one the result doesn't take its value from.

`tests/x86native.py` checks each against the processor, and `tests/x86check.py` against Alive2, both ways, and
LLVM's constant folder, poison included, where they know it. -/

namespace IRLean.X86

/-- `llvm.x86.*.pavg.{b,w}`, PAVGB and PAVGW: each lane is `(a + b + 1) >>> 1` of unsigned numbers, with the sum
in one more bit than a lane has, so it doesn't wrap. -/
@[llvm] def pavg (a b : Vec n w) : Vec n w :=
  Vec.map2
    (fun x y =>
      match x, y with
      | some x, some y => some (((x.setWidth (w + 1) + y.setWidth (w + 1) + 1) >>> 1).setWidth w)
      | _, _ => none)
    a b

/-- `SaturateSignedWordToSignedByte` and `SaturateSignedDwordToSignedWord`: a signed number, to `w` bits, signed. -/
@[llvm] def ssatTo (w : Nat) (x : BitVec u) : BitVec w :=
  if x.slt ((BitVec.intMin w).signExtend u) then BitVec.intMin w
  else if ((BitVec.intMax w).signExtend u).slt x then BitVec.intMax w
  else x.setWidth w

/-- `SaturateSignedWordToUnsignedByte` and `SaturateSignedDwordToUnsignedWord`: a signed number, to `w` bits,
unsigned, so a negative one becomes 0. -/
@[llvm] def usatTo (w : Nat) (x : BitVec u) : BitVec w :=
  if x.slt 0 then 0
  else if ((BitVec.allOnes w).setWidth u).slt x then BitVec.allOnes w
  else x.setWidth w

/-- PACKSSWB, PACKSSDW, PACKUSWB and PACKUSDW: each lane saturated to half its width by `sat`. In each 128-bit
block, the low half of the result is that block of `a`, and the high half that block of `b`. So lane `i` of the
result is poison when the one lane it's the saturation of is. -/
@[llvm] def pack (sat : BitVec u → BitVec w) (n : Nat) (a b : Vec m u) : Vec n w :=
  let g := 128 / u
  Vector.ofFn fun i =>
    ((if i.val % (2 * g) < g then a else b).lane (i.val / (2 * g) * g + i.val % g)).map sat

/-- `llvm.x86.*.packsswb` and `packssdw`: `pack` with signed saturation. -/
@[llvm] def packss (n w : Nat) (a b : Vec m u) : Vec n w := pack (ssatTo w) n a b

/-- `llvm.x86.*.packuswb` and `packusdw`: `pack` with unsigned saturation of a signed number. -/
@[llvm] def packus (n w : Nat) (a b : Vec m u) : Vec n w := pack (usatTo w) n a b

/-- `llvm.x86.*.psign.{b,w,d}`, PSIGNB, PSIGNW and PSIGND: each lane of `a` negated where that lane of `b` is
negative, 0 where it's 0, and kept where it's positive. Negating the least number gives it back.

A lane is poison when that lane of `a` or of `b` is, even where `b`'s is 0 and the result doesn't depend on `a`'s,
as Alive2 reads it. -/
@[llvm] def psign (a b : Vec n w) : Vec n w :=
  Vec.map2
    (fun x y =>
      match x, y with
      | some x, some y => some (if y.msb then -x else if y = 0 then 0 else x)
      | _, _ => none)
    a b

/-- `llvm.x86.*.pmulh.w`, PMULHW: the high 16 bits of each signed 32-bit product. -/
@[llvm] def pmulhw (a b : Vec n 16) : Vec n 16 :=
  Vec.map2
    (fun x y =>
      match x, y with
      | some x, some y => some ((x.signExtend 32 * y.signExtend 32).extractLsb' 16 16)
      | _, _ => none)
    a b

/-- `llvm.x86.*.pmulhu.w`, PMULHUW: the high 16 bits of each unsigned 32-bit product. -/
@[llvm] def pmulhuw (a b : Vec n 16) : Vec n 16 :=
  Vec.map2
    (fun x y =>
      match x, y with
      | some x, some y => some ((x.setWidth 32 * y.setWidth 32).extractLsb' 16 16)
      | _, _ => none)
    a b

/-- `llvm.x86.*.pmul.hr.sw`, PMULHRSW: each signed 32-bit product shifted right by 14, with the sign, then plus 1,
and bits 16 to 1 of that. So it's the product over `2^15`, rounded to nearest, and -32768 times itself gives
-32768. -/
@[llvm] def pmulhrsw (a b : Vec n 16) : Vec n 16 :=
  Vec.map2
    (fun x y =>
      match x, y with
      | some x, some y => some (((x.signExtend 32 * y.signExtend 32).sshiftRight 14 + 1).extractLsb' 1 16)
      | _, _ => none)
    a b

/-- `llvm.x86.*.psad.bw`, PSADBW: lane `i`, of 64 bits, is the sum of the absolute differences of the eight
unsigned bytes of `a` and `b` at `8 i` to `8 i + 7`. It's at most `8 * 255`, so the bits above 16 are 0.

A lane is poison when any of those sixteen bytes is. -/
@[llvm] def psadbw (n : Nat) (a b : Vec m 8) : Vec n 64 :=
  Vector.ofFn fun i =>
    (List.range 8).foldl
      (fun acc k =>
        match acc, a.lane (8 * i + k), b.lane (8 * i + k) with
        | some s, some x, some y => some (s + (if x.ult y then y - x else x - y).setWidth 64)
        | _, _, _ => none)
      (some 0)

/-- PHADDW, PHADDD, PHADDSW, PHSUBW, PHSUBD and PHSUBSW: `f` of each two neighbouring lanes, the lower first. In
each 128-bit block, the low half of the result is the pairs of that block of `a`, and the high half those of `b`.
So a lane is poison when one of the two lanes it combines is, as `f` says. -/
@[llvm] def horizontal (f : Val w → Val w → Val w) (a b : Vec n w) : Vec n w :=
  let g := 128 / w
  Vector.ofFn fun i =>
    let src := if i.val % g < g / 2 then a else b
    let first := i.val / g * g + 2 * (i.val % (g / 2))
    f (src.lane first) (src.lane (first + 1))

/-- `llvm.x86.sse41.pblendvb` and `llvm.x86.avx2.pblendvb`, PBLENDVB: each byte is `b`'s where bit 7 of that byte
of `mask` is set, and `a`'s otherwise.

A byte is poison when that byte of any operand is, even the one the mask doesn't pick, as Alive2 reads it. A
`select` on the mask's sign bits, which InstCombine makes of it, refines that. -/
@[llvm] def pblendvb (a b mask : Vec n 8) : Vec n 8 :=
  Vec.map3
    (fun x y m =>
      match x, y, m with
      | some x, some y, some m => some (if m.msb then y else x)
      | _, _, _ => none)
    a b mask

/-- Signed saturation of an integer to 32 bits. -/
@[llvm] def ssat32 (x : Int) : BitVec 32 := BitVec.ofInt 32 (max (-2147483648) (min 2147483647 x))

/-- `llvm.x86.avx512.vpdpbusds.*`, VPDPBUSDS: VPDPBUSD with the whole sum, the accumulator and the four products,
saturated to a signed 32-bit result. -/
@[llvm] def vpdpbusds (acc : Vec n 32) (a b : Vec m 8) : Vec n 32 :=
  Vector.ofFn fun i =>
    match acc[i], dot4 a b i with
    | some s, some d => some (ssat32 (s.toInt + d))
    | _, _ => none

/-- The sum of two products of signed words of `a` and `b`, at `2i` and `2i + 1`, or `none` if one of them is
poison. -/
@[llvm] def dot2 (a b : Vec m 16) (i : Nat) : Option Int :=
  match a.lane (2 * i), a.lane (2 * i + 1), b.lane (2 * i), b.lane (2 * i + 1) with
  | some x0, some x1, some y0, some y1 => some (x0.toInt * y0.toInt + x1.toInt * y1.toInt)
  | _, _, _, _ => none

/-- `llvm.x86.avx512.vpdpwssd.*`, VPDPWSSD: lane `i` is `acc[i]` plus `dot2 a b i`, wrapped to 32 bits. -/
@[llvm] def vpdpwssd (acc : Vec n 32) (a b : Vec m 16) : Vec n 32 :=
  Vector.ofFn fun i =>
    match acc[i], dot2 a b i with
    | some s, some d => some (s + BitVec.ofInt 32 d)
    | _, _ => none

/-- `llvm.x86.avx512.vpdpwssds.*`, VPDPWSSDS: VPDPWSSD with the whole sum saturated to a signed 32-bit result. -/
@[llvm] def vpdpwssds (acc : Vec n 32) (a b : Vec m 16) : Vec n 32 :=
  Vector.ofFn fun i =>
    match acc[i], dot2 a b i with
    | some s, some d => some (ssat32 (s.toInt + d))
    | _, _ => none

/-- `SaturateUnsignedDoubleWordToByte` and the like: an unsigned number, to `w` bits, unsigned. -/
@[llvm] def usatFrom (w : Nat) (x : BitVec u) : BitVec w :=
  if ((BitVec.allOnes w).setWidth u).ult x then BitVec.allOnes w else x.setWidth w

/-- VPMOVDB and the other down-converting moves, with a mask and what to keep where it's clear: lane `i` of the
result, for each lane of `a`, is `f a[i]` where bit `i` of `mask` is set, and `passthru[i]` where it's clear. The
lanes above those, where the result has more lanes than `a`, are 0.

A lane below is poison when the lane the mask picks for it is, of `a` or of `passthru`. The mask is one number, so
if it's poison every lane is, the zeroed ones too. -/
@[llvm] def maskNarrow (f : BitVec u → BitVec w) (a : Vec m u) (passthru : Vec n w) (mask : Val k) : Vec n w :=
  match mask with
  | none => HasPoison.poison
  | some mask =>
    Vector.ofFn fun i =>
      if i.val < m then (if mask.getLsbD i.val then (a.lane i.val).map f else passthru[i]) else some 0

/-- `llvm.x86.avx512.mask.pmov.*`, VPMOVDB, VPMOVDW, VPMOVQB, VPMOVQD, VPMOVQW and VPMOVWB: each lane's low bits. -/
@[llvm] def pmov (a : Vec m u) (passthru : Vec n w) (mask : Val k) : Vec n w :=
  maskNarrow (BitVec.setWidth w) a passthru mask

/-- `llvm.x86.avx512.mask.pmovs.*`, VPMOVSDB and the rest: each lane, signed, saturated to a signed result. -/
@[llvm] def pmovs (a : Vec m u) (passthru : Vec n w) (mask : Val k) : Vec n w :=
  maskNarrow (ssatTo w) a passthru mask

/-- `llvm.x86.avx512.mask.pmovus.*`, VPMOVUSDB and the rest: each lane, unsigned, saturated to an unsigned result. -/
@[llvm] def pmovus (a : Vec m u) (passthru : Vec n w) (mask : Val k) : Vec n w :=
  maskNarrow (usatFrom w) a passthru mask

/-- `llvm.x86.bmi.bzhi.{32,64}`, BZHI: `x` with its bits from `N` up cleared, where `N` is the low eight bits of
`n`. With `N` the width or more, it's `x`. -/
@[llvm] def bzhi (x n : Val w) : Val w :=
  match x, n with
  | some x, some n => some (x &&& ~~~(BitVec.allOnes w <<< (n.toNat % 256)))
  | _, _ => none

/-- `llvm.x86.bmi.bextr.{32,64}`, BEXTR: `LEN` bits of `x` from bit `START`, where `START` is the low eight bits of
`c` and `LEN` the next eight. Bits past the top of `x` are 0. -/
@[llvm] def bextr (x c : Val w) : Val w :=
  match x, c with
  | some x, some c => some ((x >>> (c.toNat % 256)) &&& ~~~(BitVec.allOnes w <<< (c.toNat / 256 % 256)))
  | _, _ => none

/-- `BIT_REFLECT`: the bits in the other order. -/
@[llvm] def bitReflect (x : BitVec n) : BitVec n :=
  (List.range n).foldl (fun acc i => if x.getLsbD i then acc ||| (1#n <<< (n - 1 - i)) else acc) 0

/-- CRC32's step on `k` bits of data: with both bit-reflected, the old CRC shifted left by `k`, XORed with the data
shifted left by 32, modulo the polynomial `11EDC6F41`, over GF(2), and that reflected back. This is CRC-32C. -/
@[llvm] def crc32c (crc : BitVec 32) (data : BitVec k) : BitVec 32 :=
  let start : BitVec (k + 32) :=
    ((bitReflect data).setWidth (k + 32) <<< 32) ^^^ ((bitReflect crc).setWidth (k + 32) <<< k)
  let rest := (List.range k).foldl
    (fun acc i => if acc.getLsbD (k + 31 - i) then acc ^^^ (0x11EDC6F41#(k + 32) <<< (k - 1 - i)) else acc)
    start
  bitReflect (rest.setWidth 32)

/-- `llvm.x86.sse42.crc32.32.{8,16,32}` and `llvm.x86.sse42.crc32.64.64`, CRC32: `crc32c` of the low 32 bits of
`crc` and all of `data`, zero-extended to `crc`'s width. -/
@[llvm] def crc32 (crc : Val c) (data : Val k) : Val c :=
  match crc, data with
  | some crc, some data => some ((crc32c (crc.setWidth 32) data).setWidth c)
  | _, _ => none

/-- PTEST's two flags: ZF, whether `a AND b` is all zeros, and CF, whether `(NOT a) AND b` is. `none` if a lane of
either is poison: the flags are computed from all of both. -/
@[llvm] def ptestFlags (a b : Vec n 64) : Option (Bool × Bool) :=
  (List.finRange n).foldl
    (fun acc i =>
      match acc, a[i], b[i] with
      | some (z, c), some x, some y => some (z && (x &&& y == 0), c && (~~~x &&& y == 0))
      | _, _, _ => none)
    (some (true, true))

/-- `llvm.x86.sse41.ptestz` and `llvm.x86.avx.ptestz.256`, PTEST: ZF, as 0 or 1. -/
@[llvm] def ptestz (a b : Vec n 64) : Val 32 := (ptestFlags a b).map fun f => if f.1 then 1 else 0

/-- `llvm.x86.sse41.ptestc` and `llvm.x86.avx.ptestc.256`: CF. -/
@[llvm] def ptestc (a b : Vec n 64) : Val 32 := (ptestFlags a b).map fun f => if f.2 then 1 else 0

/-- `llvm.x86.sse41.ptestnzc` and `llvm.x86.avx.ptestnzc.256`: 1 if ZF and CF are both clear. -/
@[llvm] def ptestnzc (a b : Vec n 64) : Val 32 := (ptestFlags a b).map fun f => if !f.1 && !f.2 then 1 else 0

/-- `llvm.x86.sse41.phminposuw`, PHMINPOSUW: lane 0 is the least of the eight unsigned words, lane 1 the index of
the first that is, and the other lanes are 0.

Lanes 0 and 1 are poison when any lane of `a` is. The others never are. -/
@[llvm] def phminposuw (a : Vec n 16) : Vec n 16 :=
  let best := (List.range 7).foldl
    (fun acc i =>
      match acc, a.lane (i + 1) with
      | some (least, index), some x => if x.ult least then some (x, i + 1) else some (least, index)
      | _, _ => none)
    ((a.lane 0).map fun x => (x, 0))
  Vector.ofFn fun i =>
    if i.val = 0 then best.map (·.1) else if i.val = 1 then best.map fun b => BitVec.ofNat 16 b.2 else some 0

end IRLean.X86
