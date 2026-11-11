import IRLean.Vec

/-! The x86 integer dot-product intrinsics clang emits for `_mm256_maddubs_epi16`, `_mm256_madd_epi16` and
`_mm256_dpbusd_epi32`, and their 128- and 512-bit forms, following the pseudo-code for PMADDUBSW, PMADDWD and
VPDPBUSD in Intel's Software Developer's Manual.

LangRef 23.1.3 doesn't define target intrinsics, and its one rule for poison, "Most instructions return '`poison`'
when one of their arguments is '`poison`'" (Poison Values), doesn't say which lanes. Here a lane of the result is
poison when a lane it's computed from is, the way the model treats every other vector operation. LLVM agrees where it
says anything: at the pin, `simplifyX86pmadd` in `llvm/lib/Target/X86/X86InstCombineIntrinsic.cpp` folds PMADDWD and
PMADDUBSW on constants as shuffles, extensions, `mul` and `add` or `sadd.sat`, lane by lane, and
`createVPDPBUSD` in `X86ISelLowering.cpp` reads VPDPBUSD as `C[i] + A[4i]B[4i] + ... + A[4i+3]B[4i+3]`, with `A`
zero-extended and `B` sign-extended. So does Alive2's `x86_intrinsics.cpp`, for the first two.

`tests/x86check.py` checks PMADDUBSW and PMADDWD at every width against Alive2, both ways, and against LLVM's
constant folder, poison included. Neither knows VPDPBUSD, so only `tests/x86native.py` and `tests/real/x86.ll`
check it, against the processor, which needs AVX-512 VNNI and can't see poison. `tests/x86native.py` checks the
other two against the processor too. -/

namespace IRLean.X86

/-- Signed saturation of an integer to 16 bits. -/
@[llvm] def ssat16 (x : Int) : BitVec 16 := BitVec.ofInt 16 (max (-32768) (min 32767 x))

/-- PMADDUBSW: lane `i` is `a[2i] * b[2i] + a[2i+1] * b[2i+1]`, reading `a`'s bytes as unsigned and `b`'s as
signed, saturated to a signed 16-bit result. -/
@[llvm] def pmaddubsw (n : Nat) (a b : Vec m 8) : Vec n 16 :=
  Vector.ofFn fun i =>
    match a.lane (2 * i), a.lane (2 * i + 1), b.lane (2 * i), b.lane (2 * i + 1) with
    | some x0, some x1, some y0, some y1 => some (ssat16 (x0.toNat * y0.toInt + x1.toNat * y1.toInt))
    | _, _, _, _ => none

/-- PMADDWD: lane `i` is `a[2i] * b[2i] + a[2i+1] * b[2i+1]`, all four signed, wrapped to 32 bits. Only
four copies of -32768 wrap. -/
@[llvm] def pmaddwd (n : Nat) (a b : Vec m 16) : Vec n 32 :=
  Vector.ofFn fun i =>
    match a.lane (2 * i), a.lane (2 * i + 1), b.lane (2 * i), b.lane (2 * i + 1) with
    | some x0, some x1, some y0, some y1 => some (BitVec.ofInt 32 (x0.toInt * y0.toInt + x1.toInt * y1.toInt))
    | _, _, _, _ => none

/-- The sum of four products of an unsigned byte of `a` and a signed byte of `b`, at `4i` to `4i + 3`, or
`none` if one of them is poison. -/
@[llvm] def dot4 (a b : Vec m 8) (i : Nat) : Option Int :=
  match a.lane (4 * i), a.lane (4 * i + 1), a.lane (4 * i + 2), a.lane (4 * i + 3),
      b.lane (4 * i), b.lane (4 * i + 1), b.lane (4 * i + 2), b.lane (4 * i + 3) with
  | some x0, some x1, some x2, some x3, some y0, some y1, some y2, some y3 =>
    some (x0.toNat * y0.toInt + x1.toNat * y1.toInt + x2.toNat * y2.toInt + x3.toNat * y3.toInt)
  | _, _, _, _, _, _, _, _ => none

/-- VPDPBUSD, without saturation: lane `i` is `acc[i]` plus `dot4 a b i`, wrapped to 32 bits. -/
@[llvm] def vpdpbusd (acc : Vec n 32) (a b : Vec m 8) : Vec n 32 :=
  Vector.ofFn fun i =>
    match acc[i], dot4 a b i with
    | some s, some d => some (s + BitVec.ofInt 32 d)
    | _, _ => none

end IRLean.X86
