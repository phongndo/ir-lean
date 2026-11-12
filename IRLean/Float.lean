import IRLean.Int

/-! # Floating point

LLVM's floating-point types and the operations on them, as LangRef 23.1.3 says and
[`docs/float.md`](../docs/float.md) designs. `tests/fpcheck.py` compares each with LLVM's constant folder, Alive2 and the
processor.

A float is its bits. A value of a format with `e` exponent bits and `m` trailing significand bits is a
`Val (1 + e + m)`, the type an integer of that width has: `none` is poison, and `some x` has the sign on top, then the
biased exponent, then the fraction. Every operation takes the format first, as `e` and `m`:

| Type | `e` | `m` | Value |
| --- | --- | --- | --- |
| `half` | 5 | 10 | `Val 16` |
| `bfloat` | 8 | 7 | `Val 16` |
| `float` | 8 | 23 | `Val 32` |
| `double` | 11 | 52 | `Val 64` |
| `fp128` | 15 | 112 | `Val 128` |

So `bitcast` between a float and an integer of its width is the identity, and `select`, `phi`, `freeze`, vectors and
`IRLean.Refines` treat a float as its bits, which is how LLVM compares them: two NaNs with different payloads are
different values, and so are `0.0` and `-0.0`.

This module has the operations that act on a float's bits without computing a new value: LangRef says `fneg`,
`llvm.fabs` and `llvm.copysign` "act directly on the underlying bit representation and never change anything except
possibly for the sign bit", and `fcmp`, `llvm.is.fpclass` and `nofpclass` only look at a value. None of them makes a
choice.

Fast-math flags: `nnan` and `ninf` make the result poison where an operand is, or the result would be, a NaN or an
infinity. `nsz` is a choice: LangRef says "the sign bit of 0.0 or -0.0 input operands can be non-deterministically
flipped", so each operand that's a zero may have its sign flipped first, as bit `4 + i` of the operation's choice says
for operand `i`. The emitter refuses the rest where they mean anything. -/

namespace IRLean.FP

variable {e m : Nat}

/-! ### Fields and classes -/

/-- The biased exponent field. -/
@[bv_normalize, llvm] def expField (x : BitVec (1 + e + m)) : BitVec e := x.extractLsb' m e

/-- The trailing significand field. Its top bit is the quiet bit of a NaN. -/
@[bv_normalize, llvm] def fracField (x : BitVec (1 + e + m)) : BitVec m := x.extractLsb' 0 m

/-- The sign bit, alone. -/
@[bv_normalize, llvm] def signBit : BitVec (1 + e + m) := 1#(1 + e + m) <<< (e + m)

@[bv_normalize, llvm] def isNaN (x : BitVec (1 + e + m)) : Bool := expField x == BitVec.allOnes e && fracField x != 0
@[bv_normalize, llvm] def isInf (x : BitVec (1 + e + m)) : Bool := expField x == BitVec.allOnes e && fracField x == 0
@[bv_normalize, llvm] def isZero (x : BitVec (1 + e + m)) : Bool := expField x == 0 && fracField x == 0
@[bv_normalize, llvm] def isSubnormal (x : BitVec (1 + e + m)) : Bool := expField x == 0 && fracField x != 0
@[bv_normalize, llvm] def isNormal (x : BitVec (1 + e + m)) : Bool := expField x != 0 && expField x != BitVec.allOnes e

/-- A quiet NaN has the top bit of its fraction set, LangRef's "quiet bit". -/
@[bv_normalize, llvm] def isQuietNaN (x : BitVec (1 + e + m)) : Bool := isNaN x && (fracField x).msb
@[bv_normalize, llvm] def isSignalingNaN (x : BitVec (1 + e + m)) : Bool := isNaN x && !(fracField x).msb

/-- Whether `nnan` and `ninf` allow `x`: it isn't a NaN under `nnan`, or an infinity under `ninf`. -/
@[bv_normalize, llvm] def allows (nnan ninf : Bool) (x : BitVec (1 + e + m)) : Bool :=
  !(nnan && isNaN x) && !(ninf && isInf x)

/-- `nsz` on operand `i`: a zero with its sign flipped where bit `4 + i` of the choice `pick` is set, and anything else
as it is. LangRef: "the sign bit of 0.0 or -0.0 input operands can be non-deterministically flipped". -/
@[bv_normalize, llvm] def nszIn (nsz : Bool) (pick : BitVec 8) (i : Nat) (x : BitVec (1 + e + m)) :
    BitVec (1 + e + m) :=
  if nsz && isZero x && pick.getLsbD (4 + i) then x ^^^ signBit else x

/-! ### The sign bit

LangRef: these "act directly on the underlying bit representation and never change anything except possibly for the
sign bit". A NaN keeps its quiet bit and payload. Under `nnan` or `ninf` the result is poison where the operand is a NaN
or an infinity, and the result is one exactly when an operand is. Under `nsz`, a zero operand's sign is a choice,
`pick`, which the emitter passes only with `nsz`: then `fneg` of a zero, and `copysign` with a zero second operand, may
give either zero. `fabs` clears the sign whatever it was, so `nsz` changes nothing there, and it takes no choice. -/

/-- `fneg`: the sign bit flipped. -/
@[llvm] def fneg (e m : Nat) (a : Val (1 + e + m)) (nnan ninf nsz : Bool := false) (pick : Nat := 0) :
    Val (1 + e + m) :=
  match a with
  | some x => if allows nnan ninf x then some (nszIn nsz (BitVec.ofNat 8 pick) 0 x ^^^ signBit) else none
  | none => none

/-- `llvm.fabs`: the sign bit cleared. -/
@[llvm] def fabs (e m : Nat) (a : Val (1 + e + m)) (nnan ninf : Bool := false) : Val (1 + e + m) :=
  match a with
  | some x => if allows nnan ninf x then some (x &&& ~~~signBit) else none
  | none => none

/-- `llvm.copysign`: the first operand with the second's sign bit. Under `nsz` only the second operand's flip can show,
since the first's sign is cleared. -/
@[llvm] def copysign (e m : Nat) (a b : Val (1 + e + m)) (nnan ninf nsz : Bool := false) (pick : Nat := 0) :
    Val (1 + e + m) :=
  match a, b with
  | some x, some y =>
    if allows nnan ninf x && allows nnan ninf y then
      some ((x &&& ~~~signBit) ||| (nszIn nsz (BitVec.ofNat 8 pick) 1 y &&& signBit))
    else none
  | _, _ => none

/-- The fast-math flags of a `select`, which LangRef says "are only applied to the result, not both arms": poison under
`nnan` or `ninf` where the selected value is a NaN or an infinity, and under `nsz`, a zero's sign flipped where bit 4
of `pick` says. Alive2 reads them the same way. -/
@[llvm] def selected (e m : Nat) (a : Val (1 + e + m)) (nnan ninf nsz : Bool := false) (pick : Nat := 0) :
    Val (1 + e + m) :=
  match a with
  | some x => if allows nnan ninf x then some (nszIn nsz (BitVec.ofNat 8 pick) 0 x) else none
  | none => none

/-! ### Comparison -/

/-- IEEE 754's less-than, false if either is a NaN. Zeros of either sign are equal, and otherwise the order is the sign
and then the magnitude, the bits below the sign read as an unsigned integer. -/
@[bv_normalize, llvm] def lt (x y : BitVec (1 + e + m)) : Bool :=
  let mx := x.extractLsb' 0 (e + m)
  let my := y.extractLsb' 0 (e + m)
  if isNaN x || isNaN y then false
  else if isZero x && isZero y then false
  else if x.msb != y.msb then x.msb
  else if x.msb then my.ult mx else mx.ult my

/-- IEEE 754's equality, false if either is a NaN. `0.0` equals `-0.0`. -/
@[bv_normalize, llvm] def eq (x y : BitVec (1 + e + m)) : Bool :=
  !(isNaN x || isNaN y) && (x == y || (isZero x && isZero y))

/-- `fcmp` with the predicate `pred`, numbered as LLVM's `FCmpInst::Predicate` numbers them: from the lowest bit, true
when equal, greater, less, and unordered, so `oeq` is 1, `olt` 4, `uno` 8 and `true` 15. LangRef: "Ordered means that
neither operand is a QNAN while unordered means that either operand may be a QNAN", and LLVM reads a signaling NaN the
same way. Poison if an operand is, even for `false` and `true`, as Alive2 has it. Of the fast-math flags, LangRef says
"the only flags that have any effect on its semantics are ... `nnan`, `ninf`, and `reassoc`", so the emitter allows the
rest and refuses `reassoc`. -/
@[llvm] def fcmp (e m : Nat) (pred : Nat) (a b : Val (1 + e + m)) (nnan ninf : Bool := false) : Val 1 :=
  match a, b with
  | some x, some y =>
    if allows nnan ninf x && allows nnan ninf y then
      let p := BitVec.ofNat 4 pred
      some (BitVec.ofBool ((p.getLsbD 0 && eq x y) || (p.getLsbD 1 && lt y x) || (p.getLsbD 2 && lt x y) ||
        (p.getLsbD 3 && (isNaN x || isNaN y))))
    else none
  | _, _ => none

/-! ### Classes -/

/-- The classes `llvm.is.fpclass` tests and `nofpclass` names, as LangRef numbers them: bit 0 signaling NaN, 1 quiet
NaN, 2 negative infinity, 3 negative normal, 4 negative subnormal, 5 negative zero, 6 positive zero, 7 positive
subnormal, 8 positive normal, 9 positive infinity. `x` is in exactly one. -/
@[bv_normalize, llvm] def classIn (mask : Nat) (x : BitVec (1 + e + m)) : Bool :=
  let k := BitVec.ofNat 10 mask
  let n := x.msb
  (k.getLsbD 0 && isSignalingNaN x) || (k.getLsbD 1 && isQuietNaN x) ||
    (k.getLsbD 2 && n && isInf x) || (k.getLsbD 3 && n && isNormal x) ||
    (k.getLsbD 4 && n && isSubnormal x) || (k.getLsbD 5 && n && isZero x) ||
    (k.getLsbD 6 && !n && isZero x) || (k.getLsbD 7 && !n && isSubnormal x) ||
    (k.getLsbD 8 && !n && isNormal x) || (k.getLsbD 9 && !n && isInf x)

/-- `llvm.is.fpclass`: whether the operand is in a class the mask names. It "does not canonicalize its input value and
does not depend on the floating-point environment". -/
@[llvm] def isFPClass (e m : Nat) (a : Val (1 + e + m)) (mask : Nat) : Val 1 :=
  match a with
  | some x => some (BitVec.ofBool (classIn mask x))
  | none => none

/-- The `nofpclass` attribute: "If the value is a floating-point class indicated by the `nofpclass` test mask, a
poison value is passed or returned instead." -/
@[llvm] def nofpclass (e m : Nat) (mask : Nat) (a : Val (1 + e + m)) : Val (1 + e + m) :=
  match a with
  | some x => if classIn mask x then none else some x
  | none => none

/-! ## Arithmetic

The operations LangRef calls "floating-point math operations": a result that isn't a NaN is IEEE 754's, rounded to
nearest, ties to even, and a NaN result is a choice. Each is a circuit on bit vectors, for every format, following
symfpu's: unpack, compute exactly or with a sticky bit, and round once. `docs/float.md` has the design, and
`tests/fpcheck.py` checks each against Lean's own `Float.Model` is a reference too.

The circuits have no `let` or `have`: each value an operation computes is a definition of its own, of the operation's
inputs, marked `@[bv_normalize]` so that `bv_decide` unfolds it, and not `@[llvm]`, so that `simp [llvm]` leaves it for
`bv_decide`. In Lean 4.35.0 `bv_decide` mishandles a definition that binds a value, and unfolding one with `simp` first
costs more than `bv_decide` itself, as `docs/float.md` measured. -/

/-! ### NaN results

Where IEEE 754 gives a NaN, LangRef 23.1.3 lets an operation return, with either sign, the preferred NaN, or an input
NaN quieted, or one unchanged. The choice `pick` names one: bit 0 is the sign, bit 1 says unchanged rather than
quieted, and bits 2 and 3 name the operand, 0 for the preferred NaN. An operand that isn't a NaN gives the preferred
NaN. So every choice is one LangRef allows, and every one it allows is some choice. The target-specific "extra"
payloads are none, as on x86 and ARM: the emitter refuses floating point for other targets. -/

/-- LangRef's "preferred NaN": positive, quiet, and an all-zero payload. -/
@[bv_normalize, llvm] def preferredNaN : BitVec (1 + e + m) :=
  (0#1 ++ BitVec.allOnes e ++ (1#m <<< (m - 1))).cast (by omega)

/-- `x` with its sign set to `s`. -/
@[bv_normalize, llvm] def withSign (s : Bool) (x : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  (BitVec.ofBool s ++ x.extractLsb' 0 (e + m)).cast (by omega)

/-- The NaN `pick` takes from the operand `x`: `x` quieted, or as it is, or the preferred NaN if `x` isn't a NaN. -/
@[bv_normalize] def nanFrom (pick : BitVec 8) (x : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  if isNaN x then (if pick.getLsbD 1 then x else x ||| (1#(1 + e + m) <<< (m - 1))) else preferredNaN

/-- The NaN result of an operation of one, two or three operands, as `pick` chooses. -/
@[bv_normalize] def nan3 (pick : BitVec 8) (a b c : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  withSign (pick.getLsbD 0)
    (if pick.extractLsb' 2 2 == 1#2 then nanFrom pick a
     else if pick.extractLsb' 2 2 == 2#2 then nanFrom pick b
     else if pick.extractLsb' 2 2 == 3#2 then nanFrom pick c else preferredNaN)

/-! ### Unpacking a finite value

A finite `x` is `M × 2 ^ (t - bias - m)`: `M` the significand, its implicit bit included, and `t` the biased exponent
of its last place, at least 1. Exponents are signed, `e + m + 3` bits wide, which holds every exponent an operation
here forms. -/

/-- The significand, with the implicit bit when `x` is normal. -/
@[bv_normalize] def sig (x : BitVec (1 + e + m)) : BitVec (m + 1) :=
  (BitVec.ofBool (expField x != 0) ++ fracField x).cast (by omega)

/-- The biased exponent of the last place: the exponent field, or 1 for a subnormal or zero. -/
@[bv_normalize] def lsbExp (x : BitVec (1 + e + m)) : BitVec (e + m + 3) :=
  if expField x == 0 then 1#_ else (expField x).setWidth _

/-- The exponent bias, `2 ^ (e - 1) - 1`. -/
@[bv_normalize] def bias : BitVec (e + m + 3) := BitVec.ofNat _ (2 ^ (e - 1) - 1)

/-! ### Rounding

`round e m s S t` is `(-1) ^ s × S × 2 ^ (t - bias - m)` rounded to nearest, ties to even: a finite value or an
infinity, never a NaN. `S` is exact, or has a sticky bit in its last place at least two places below where the result
rounds, which each caller arranges. It finds `S`'s top bit, keeps `m + 1` bits from it, or fewer where the result is
subnormal, rounds on the next bit and the rest, and adds the exponent and the fraction as one integer, so a carry out of
the fraction raises the exponent and the largest finite value rounds up to infinity. `S` is widened to `n + m + 3` bits
to shift. -/

/-- The place of `S`'s top bit. -/
@[bv_normalize] def rTop (e m : Nat) (S : BitVec n) : BitVec (e + m + 3) :=
  BitVec.ofNat _ (n - 1) - S.clz.setWidth _

/-- The biased exponent of the result's last place: `m` places below `S`'s top, or the subnormals' last place if
that's lower. -/
@[bv_normalize] def rLast (e m : Nat) (S : BitVec n) (t : BitVec (e + m + 3)) : BitVec (e + m + 3) :=
  if (t + rTop e m S - BitVec.ofNat _ m).slt 1#_ then 1#_ else t + rTop e m S - BitVec.ofNat _ m

/-- Places to drop from `S`, or to shift it left by, which is exact, when negative. -/
@[bv_normalize] def rDrop (e m : Nat) (S : BitVec n) (t : BitVec (e + m + 3)) : BitVec (e + m + 3) :=
  rLast e m S t - t

/-- The places to drop, at most `n + 1`, as a shift amount. -/
@[bv_normalize] def rShift (e m : Nat) (S : BitVec n) (t : BitVec (e + m + 3)) : BitVec (n + m + 3) :=
  if (rDrop e m S t).msb then 0#_
  else if (rDrop e m S t).ult (BitVec.ofNat _ (n + 1)) then (rDrop e m S t).setWidth _
  else BitVec.ofNat _ (n + 1)

/-- The bits kept, before rounding. -/
@[bv_normalize] def rKept (e m : Nat) (S : BitVec n) (t : BitVec (e + m + 3)) : BitVec (n + m + 3) :=
  if (rDrop e m S t).msb then S.setWidth _ <<< (-(rDrop e m S t)).setWidth (n + m + 3)
  else S.setWidth _ >>> rShift e m S t

/-- Whether to round up: the first bit dropped is set, and so is a later one or the last bit kept. -/
@[bv_normalize] def rUp (e m : Nat) (S : BitVec n) (t : BitVec (e + m + 3)) : Bool :=
  rShift e m S t != 0#_ && (S.setWidth (n + m + 3) >>> (rShift e m S t - 1#_)).getLsbD 0 &&
    ((S.setWidth (n + m + 3) &&& ((1#_ <<< (rShift e m S t - 1#_)) - 1#_)) != 0#_ ||
      (rKept e m S t).getLsbD 0)

/-- The exponent field and the rounded fraction, added as one integer. -/
@[bv_normalize] def rMag (e m : Nat) (S : BitVec n) (t : BitVec (e + m + 3)) : BitVec (e + m + 2) :=
  ((rLast e m S t - 1#_).setWidth (e + m + 2)).shiftLeft m +
    (rKept e m S t + (BitVec.ofBool (rUp e m S t)).setWidth _).setWidth (e + m + 2)

@[bv_normalize] def round (e m : Nat) (s : Bool) (S : BitVec n) (t : BitVec (e + m + 3)) : BitVec (1 + e + m) :=
  if S == 0#n then (BitVec.ofBool s ++ 0#(e + m)).cast (by omega)
  else if !((rLast e m S t).slt (BitVec.ofNat _ (2 ^ e - 1))) ||
      !((rMag e m S t).ult (BitVec.ofNat _ ((2 ^ e - 1) * 2 ^ m))) then
    (BitVec.ofBool s ++ BitVec.allOnes e ++ 0#m).cast (by omega)
  else (BitVec.ofBool s ++ (rMag e m S t).setWidth (e + m)).cast (by omega)

/-! ### Addition

The operand whose last place is higher is `x`, and `y`'s significand is shifted right to meet it, keeping three more
places and folding what's shifted out into a sticky bit. Each part is taken from `a` and `b` before choosing. -/

@[bv_normalize] def aSwap (a b : BitVec (1 + e + m)) : Bool := (lsbExp a).ult (lsbExp b)

/-- A significand with three more places. -/
@[bv_normalize] def sig3 (x : BitVec (1 + e + m)) : BitVec (m + 5) := (sig x).setWidth (m + 5) <<< 3

@[bv_normalize] def aX (a b : BitVec (1 + e + m)) : BitVec (m + 5) := if aSwap a b then sig3 b else sig3 a
@[bv_normalize] def aY (a b : BitVec (1 + e + m)) : BitVec (m + 5) := if aSwap a b then sig3 a else sig3 b
@[bv_normalize] def aXs (a b : BitVec (1 + e + m)) : Bool := if aSwap a b then b.msb else a.msb
@[bv_normalize] def aYs (a b : BitVec (1 + e + m)) : Bool := if aSwap a b then a.msb else b.msb
@[bv_normalize] def aXe (a b : BitVec (1 + e + m)) : BitVec (e + m + 3) :=
  if aSwap a b then lsbExp b else lsbExp a
@[bv_normalize] def aYe (a b : BitVec (1 + e + m)) : BitVec (e + m + 3) :=
  if aSwap a b then lsbExp a else lsbExp b

/-- How far `y` shifts, at most `m + 5`, past which it's all sticky. -/
@[bv_normalize] def aShift (a b : BitVec (1 + e + m)) : BitVec (m + 5) :=
  if (aXe a b - aYe a b).ult (BitVec.ofNat _ (m + 5)) then (aXe a b - aYe a b).setWidth _
  else BitVec.ofNat _ (m + 5)

/-- `y` shifted, with what's shifted out folded into its last bit. -/
@[bv_normalize] def aYj (a b : BitVec (1 + e + m)) : BitVec (m + 5) :=
  (aY a b >>> aShift a b) |||
    (BitVec.ofBool ((aY a b &&& ((1#_ <<< aShift a b) - 1#_)) != 0#_)).setWidth _

@[bv_normalize] def aSum (a b : BitVec (1 + e + m)) : BitVec (m + 5) :=
  if aXs a b == aYs a b then aX a b + aYj a b
  else if (aYj a b).ule (aX a b) then aX a b - aYj a b else aYj a b - aX a b

@[bv_normalize] def aSign (a b : BitVec (1 + e + m)) : Bool :=
  if aXs a b == aYs a b then aXs a b else if (aYj a b).ule (aX a b) then aXs a b else aYs a b

/-- IEEE 754's sum, with a NaN result as `pick` chooses. An exact zero sum is `+0`, or `-0` when both are `-0`. -/
@[bv_normalize] def addBits (pick : BitVec 8) (a b : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  if isNaN a || isNaN b || (isInf a && isInf b && a.msb != b.msb) then nan3 pick a b b
  else if isInf a then a
  else if isInf b then b
  else if aSum a b == 0#_ then (BitVec.ofBool (a.msb && b.msb) ++ 0#(e + m)).cast (by omega)
  else round e m (aSign a b) (aSum a b) (aXe a b - 3#_)

/-! ### Multiplication, division and remainder -/

/-- IEEE 754's product: the significands multiply exactly, then one rounding. -/
@[bv_normalize] def mulBits (pick : BitVec 8) (a b : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  if isNaN a || isNaN b || (isInf a && isZero b) || (isZero a && isInf b) then nan3 pick a b b
  else if isInf a || isInf b then (BitVec.ofBool (a.msb != b.msb) ++ BitVec.allOnes e ++ 0#m).cast (by omega)
  else round e m (a.msb != b.msb) ((sig a).setWidth (2 * m + 2) * (sig b).setWidth (2 * m + 2))
    (lsbExp a + lsbExp b - bias - BitVec.ofNat _ m)

/-- A significand shifted so its top bit is set. -/
@[bv_normalize] def normSig (x : BitVec (1 + e + m)) : BitVec (m + 1) := sig x <<< (sig x).clz

/-- The dividend's significand, normalized, with `m + 3` more places. -/
@[bv_normalize] def dNum (a : BitVec (1 + e + m)) : BitVec (2 * m + 4) := (normSig a).setWidth _ <<< (m + 3)

@[bv_normalize] def dQuot (a b : BitVec (1 + e + m)) : BitVec (2 * m + 4) := dNum a / (normSig b).setWidth _
@[bv_normalize] def dRem (a b : BitVec (1 + e + m)) : BitVec (2 * m + 4) := dNum a % (normSig b).setWidth _

/-- The biased exponent of the quotient's last place, with its sticky bit appended. -/
@[bv_normalize] def dExp (a b : BitVec (1 + e + m)) : BitVec (e + m + 3) :=
  lsbExp a - (sig a).clz.setWidth _ - (lsbExp b - (sig b).clz.setWidth _) - 3#_ + bias - 1#_

/-- IEEE 754's quotient: significands normalized, divided with `m + 3` more places, and the remainder as a sticky
bit. -/
@[bv_normalize] def divBits (pick : BitVec 8) (a b : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  if isNaN a || isNaN b || (isInf a && isInf b) || (isZero a && isZero b) then nan3 pick a b b
  else if isInf a || isZero b then (BitVec.ofBool (a.msb != b.msb) ++ BitVec.allOnes e ++ 0#m).cast (by omega)
  else if isInf b || isZero a then (BitVec.ofBool (a.msb != b.msb) ++ 0#(e + m)).cast (by omega)
  else round e m (a.msb != b.msb) (dQuot a b ++ BitVec.ofBool (dRem a b != 0#_)) (dExp a b)

/-- `a`'s significand shifted left by the difference of the last places' exponents, modulo `b`'s: exact, in
`2 ^ e + m + 1` bits, which holds the largest shift. -/
@[bv_normalize] def remSig (a b : BitVec (1 + e + m)) : BitVec (2 ^ e + m + 1) :=
  ((sig a).setWidth _ <<< (lsbExp a - lsbExp b).setWidth (2 ^ e + m + 1)) % (sig b).setWidth _

/-- `frem`: "the same output as a libm `fmod` function", the remainder of truncated division, which is exact, with
the dividend's sign. -/
@[bv_normalize] def remBits (pick : BitVec 8) (a b : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  if isNaN a || isNaN b || isInf a || isZero b then nan3 pick a b b
  else if isInf b || isZero a then a
  else if (lsbExp a).ult (lsbExp b) then a
  else round e m a.msb (remSig a b) (lsbExp b)

/-! ### Conversions between formats -/

/-- A NaN's payload in another format. LangRef: the payload's low bits that don't fit are dropped, and in a wider
format the payload is "copied to the high order bits of the resulting payload, and the remaining low order bits are
zero". -/
@[bv_normalize] def convPayload (m' : Nat) (x : BitVec (1 + e + m)) : BitVec m' :=
  if m' ≤ m then (fracField x >>> (m - m')).setWidth m' else (fracField x).setWidth m' <<< (m' - m)

/-- A NaN converted to another format, as `pick` chooses. Where dropping bits leaves a payload of zeros, only the
quieted NaN is possible, as LangRef says. -/
@[bv_normalize] def convNaN (e' m' : Nat) (pick : BitVec 8) (x : BitVec (1 + e + m)) : BitVec (1 + e' + m') :=
  if pick.extractLsb' 2 2 == 1#2 && isNaN x then
    (BitVec.ofBool (pick.getLsbD 0) ++ BitVec.allOnes e' ++
      (convPayload m' x |||
        ((BitVec.ofBool (!pick.getLsbD 1 || convPayload m' x == 0#m')).setWidth m' <<< (m' - 1)))).cast (by omega)
  else withSign (pick.getLsbD 0) preferredNaN

/-- A value in another format: exact if it's wider, rounded once if it's narrower. -/
@[bv_normalize] def convBits (e' m' : Nat) (pick : BitVec 8) (x : BitVec (1 + e + m)) : BitVec (1 + e' + m') :=
  if isNaN x then convNaN e' m' pick x
  else if isInf x then (BitVec.ofBool x.msb ++ BitVec.allOnes e' ++ 0#m').cast (by omega)
  else round e' m' x.msb (sig x)
    ((lsbExp x).signExtend (e + m + e' + m' + 3) - (bias (e := e) (m := m)).signExtend _ - BitVec.ofNat _ m +
      (bias (e := e') (m := m')).signExtend _ + BitVec.ofNat _ m' |>.setWidth (e' + m' + 3))

/-! ### Conversions with integers -/

/-- `x`'s integer part, toward zero, in `w + m + 1` bits, which holds every value that fits in `w` bits shifted by
less than `w`. -/
@[bv_normalize] def truncInt (w : Nat) (x : BitVec (1 + e + m)) : BitVec (w + m + 1) :=
  if (lsbExp x - bias - BitVec.ofNat _ m).msb then
    (sig x).setWidth _ >>> (-(lsbExp x - bias - BitVec.ofNat _ m)).setWidth (w + m + 1)
  else (sig x).setWidth _ <<< (lsbExp x - bias - BitVec.ofNat _ m).setWidth (w + m + 1)

/-- Whether `x`'s integer part has a bit at `w` or above, which no shift by `w` or more avoids unless it's zero. -/
@[bv_normalize] def truncBig (w : Nat) (x : BitVec (1 + e + m)) : Bool :=
  (!(lsbExp x - bias - BitVec.ofNat _ m).msb &&
      !((lsbExp x - bias - BitVec.ofNat _ m).ult (BitVec.ofNat _ w)) && !isZero x) ||
    !((truncInt w x).ult (BitVec.ofNat _ (2 ^ w)))

/-- Whether `fptoui` has a value: `x`'s integer part isn't negative and fits, and `x` isn't a NaN or an infinity. -/
@[bv_normalize] def toUIntOk (w : Nat) (x : BitVec (1 + e + m)) : Bool :=
  !(isNaN x || isInf x || truncBig w x || (x.msb && truncInt w x != 0#_))

/-- Whether `fptosi` has a value: `x`'s integer part fits, and `x` isn't a NaN or an infinity. -/
@[bv_normalize] def toSIntOk (w : Nat) (x : BitVec (1 + e + m)) : Bool :=
  !(isNaN x || isInf x || truncBig w x) &&
    (if x.msb then (truncInt w x).ule (BitVec.ofNat _ (2 ^ (w - 1)))
     else (truncInt w x).ult (BitVec.ofNat _ (2 ^ (w - 1))))

/-- `x`'s integer part, in `w` bits, with its sign. -/
@[bv_normalize] def toSIntVal (w : Nat) (x : BitVec (1 + e + m)) : BitVec w :=
  if x.msb then -(truncInt w x).setWidth w else (truncInt w x).setWidth w

/-- `llvm.fptoui.sat`: the integer part, clamped to the type's range, and 0 for a NaN. -/
@[bv_normalize] def toUIntSatBits (w : Nat) (x : BitVec (1 + e + m)) : BitVec w :=
  if isNaN x || x.msb then 0#w
  else if isInf x || truncBig w x then BitVec.allOnes w
  else (truncInt w x).setWidth w

/-- `llvm.fptosi.sat`: the integer part, clamped to the type's range, and 0 for a NaN. -/
@[bv_normalize] def toSIntSatBits (w : Nat) (x : BitVec (1 + e + m)) : BitVec w :=
  if isNaN x then 0#w
  else if x.msb then
    (if !isInf x && !truncBig w x && (truncInt w x).ule (BitVec.ofNat _ (2 ^ (w - 1))) then
      -(truncInt w x).setWidth w
     else BitVec.intMin w)
  else
    (if !isInf x && !truncBig w x && (truncInt w x).ult (BitVec.ofNat _ (2 ^ (w - 1))) then
      (truncInt w x).setWidth w
     else BitVec.intMax w)

/-- An integer's magnitude, rounded once, with the sign `s`: the value `S × 2 ^ 0`. -/
@[bv_normalize] def ofIntBits (e m : Nat) (s : Bool) (S : BitVec w) : BitVec (1 + e + m) :=
  round e m s S (bias + BitVec.ofNat _ m)

/-! ### Fused multiply-add

`a × b + c` rounded once. The product's significand is exact, `2 * m + 2` bits with its last place at `pe`, as
`mulBits` has it. Of the product and `c`, the term `x` whose last place is higher goes `3 * m + 5` places up, and the
other, `y`, meets it: exactly, shifted left, if it's at most that many places lower, and otherwise shifted right with
what's shifted out folded into a sticky bit. A term that far below is less than `x`'s last place, so the sum's top is
at least `3 * m + 4` places up, and it rounds at least `2 * m + 4` places above the sticky bit, which is what `round`
needs. `5 * m + 9` bits hold either term, shifted, and their sum. -/

/-- The product's exact significand. -/
@[bv_normalize] def fP (a b : BitVec (1 + e + m)) : BitVec (5 * m + 9) :=
  ((sig a).setWidth (2 * m + 2) * (sig b).setWidth (2 * m + 2)).setWidth _

/-- The biased exponent of the product's last place. -/
@[bv_normalize] def fPe (a b : BitVec (1 + e + m)) : BitVec (e + m + 3) := lsbExp a + lsbExp b - bias - BitVec.ofNat _ m

/-- How far up `x` goes. -/
@[bv_normalize] def fG : BitVec (e + m + 3) := BitVec.ofNat _ (3 * m + 5)

@[bv_normalize] def fSwap (a b c : BitVec (1 + e + m)) : Bool := (fPe a b).slt (lsbExp c)
@[bv_normalize] def fX (a b c : BitVec (1 + e + m)) : BitVec (5 * m + 9) :=
  if fSwap a b c then (sig c).setWidth _ else fP a b
@[bv_normalize] def fY (a b c : BitVec (1 + e + m)) : BitVec (5 * m + 9) :=
  if fSwap a b c then fP a b else (sig c).setWidth _
@[bv_normalize] def fXs (a b c : BitVec (1 + e + m)) : Bool := if fSwap a b c then c.msb else a.msb != b.msb
@[bv_normalize] def fYs (a b c : BitVec (1 + e + m)) : Bool := if fSwap a b c then a.msb != b.msb else c.msb
@[bv_normalize] def fXe (a b c : BitVec (1 + e + m)) : BitVec (e + m + 3) :=
  if fSwap a b c then lsbExp c else fPe a b
@[bv_normalize] def fYe (a b c : BitVec (1 + e + m)) : BitVec (e + m + 3) :=
  if fSwap a b c then fPe a b else lsbExp c

/-- How many places `y`'s last place is below `x`'s, which isn't negative. -/
@[bv_normalize] def fD (a b c : BitVec (1 + e + m)) : BitVec (e + m + 3) := fXe a b c - fYe a b c

/-- `y`, placed: shifted left to meet `x`, or right past it with a sticky bit, at most `5 * m + 9` places. -/
@[bv_normalize] def fYj (a b c : BitVec (1 + e + m)) : BitVec (5 * m + 9) :=
  if (fD a b c).ule fG then fY a b c <<< (fG - fD a b c).setWidth (5 * m + 9)
  else
    let s : BitVec (5 * m + 9) :=
      if (fD a b c - fG).ult (BitVec.ofNat _ (5 * m + 9)) then (fD a b c - fG).setWidth _
      else BitVec.ofNat _ (5 * m + 9)
    (fY a b c >>> s) ||| (BitVec.ofBool ((fY a b c &&& ((1#_ <<< s) - 1#_)) != 0#_)).setWidth _

@[bv_normalize] def fXj (a b c : BitVec (1 + e + m)) : BitVec (5 * m + 9) :=
  fX a b c <<< (BitVec.ofNat (5 * m + 9) (3 * m + 5))

@[bv_normalize] def fSum (a b c : BitVec (1 + e + m)) : BitVec (5 * m + 9) :=
  if fXs a b c == fYs a b c then fXj a b c + fYj a b c
  else if (fYj a b c).ule (fXj a b c) then fXj a b c - fYj a b c else fYj a b c - fXj a b c

@[bv_normalize] def fSign (a b c : BitVec (1 + e + m)) : Bool :=
  if fXs a b c == fYs a b c then fXs a b c else if (fYj a b c).ule (fXj a b c) then fXs a b c else fYs a b c

/-- IEEE 754's fused multiply-add, with a NaN result as `pick` chooses among the three operands. An exact zero sum
is `+0`, or `-0` when the product and `c` are both `-0`. -/
@[bv_normalize] def fmaBits (pick : BitVec 8) (a b c : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  if isNaN a || isNaN b || isNaN c || (isInf a && isZero b) || (isZero a && isInf b) ||
      ((isInf a || isInf b) && isInf c && (a.msb != b.msb) != c.msb) then nan3 pick a b c
  else if isInf a || isInf b then (BitVec.ofBool (a.msb != b.msb) ++ BitVec.allOnes e ++ 0#m).cast (by omega)
  else if isInf c then c
  else if isZero a || isZero b then
    if isZero c then (BitVec.ofBool ((a.msb != b.msb) && c.msb) ++ 0#(e + m)).cast (by omega) else c
  else if isZero c then
    round e m (a.msb != b.msb) ((sig a).setWidth (2 * m + 2) * (sig b).setWidth (2 * m + 2)) (fPe a b)
  else if fSum a b c == 0#_ then (0#1 ++ 0#(e + m)).cast (by omega)
  else round e m (fSign a b c) (fSum a b c) (fXe a b c - fG)

/-! ### The operations on values

Each is poison if an operand is, and under `nnan` or `ninf` if an operand or the result is a NaN or an infinity. The
operations that can give a NaN take their choice first, as `pick`, which emitted code reads from the run's `Choice`:
`c'.pick k` for the block's `k`th chooser, and for a vector, `(c'.sub k).pick i` for lane `i`, so that each lane
chooses on its own. -/

/-- Poison where `nnan` or `ninf` rules out `r` or an operand. -/
@[llvm] def flagged (nnan ninf : Bool) (ops : List (BitVec (1 + e + m))) (r : BitVec (1 + e + m)) :
    Val (1 + e + m) :=
  if ops.all (allows nnan ninf) && allows nnan ninf r then some r else none

@[llvm] def fadd (e m : Nat) (pick : Nat) (a b : Val (1 + e + m)) (nnan ninf nsz : Bool := false) :
    Val (1 + e + m) :=
  match a, b with
  | some x, some y =>
    flagged nnan ninf [x, y]
      (addBits (BitVec.ofNat 8 pick) (nszIn nsz (BitVec.ofNat 8 pick) 0 x) (nszIn nsz (BitVec.ofNat 8 pick) 1 y))
  | _, _ => none

/-- `fsub`, as `fadd` of the second operand with its sign flipped. A NaN result's sign is the choice's, so where the
choice takes the second operand's NaN, flipping its sign first changes nothing. -/
@[llvm] def fsub (e m : Nat) (pick : Nat) (a b : Val (1 + e + m)) (nnan ninf nsz : Bool := false) :
    Val (1 + e + m) :=
  match a, b with
  | some x, some y =>
    flagged nnan ninf [x, y]
      (addBits (BitVec.ofNat 8 pick) (nszIn nsz (BitVec.ofNat 8 pick) 0 x)
        (nszIn nsz (BitVec.ofNat 8 pick) 1 y ^^^ signBit))
  | _, _ => none

@[llvm] def fmul (e m : Nat) (pick : Nat) (a b : Val (1 + e + m)) (nnan ninf nsz : Bool := false) :
    Val (1 + e + m) :=
  match a, b with
  | some x, some y =>
    flagged nnan ninf [x, y]
      (mulBits (BitVec.ofNat 8 pick) (nszIn nsz (BitVec.ofNat 8 pick) 0 x) (nszIn nsz (BitVec.ofNat 8 pick) 1 y))
  | _, _ => none

@[llvm] def fdiv (e m : Nat) (pick : Nat) (a b : Val (1 + e + m)) (nnan ninf nsz : Bool := false) :
    Val (1 + e + m) :=
  match a, b with
  | some x, some y =>
    flagged nnan ninf [x, y]
      (divBits (BitVec.ofNat 8 pick) (nszIn nsz (BitVec.ofNat 8 pick) 0 x) (nszIn nsz (BitVec.ofNat 8 pick) 1 y))
  | _, _ => none

@[llvm] def frem (e m : Nat) (pick : Nat) (a b : Val (1 + e + m)) (nnan ninf nsz : Bool := false) :
    Val (1 + e + m) :=
  match a, b with
  | some x, some y =>
    flagged nnan ninf [x, y]
      (remBits (BitVec.ofNat 8 pick) (nszIn nsz (BitVec.ofNat 8 pick) 0 x) (nszIn nsz (BitVec.ofNat 8 pick) 1 y))
  | _, _ => none

/-- `llvm.fma`: `a × b + c`, rounded once. -/
@[llvm] def fma (e m : Nat) (pick : Nat) (a b c : Val (1 + e + m)) (nnan ninf nsz : Bool := false) :
    Val (1 + e + m) :=
  match a, b, c with
  | some x, some y, some z =>
    flagged nnan ninf [x, y, z]
      (fmaBits (BitVec.ofNat 8 pick) (nszIn nsz (BitVec.ofNat 8 pick) 0 x) (nszIn nsz (BitVec.ofNat 8 pick) 1 y)
        (nszIn nsz (BitVec.ofNat 8 pick) 2 z))
  | _, _, _ => none

/-- `llvm.fmuladd`. LangRef: it's "equivalent to `a * b + c`, where the result may be computed with or without fusion
(rounding once or twice)". Bit 7 of the choice says which: clear, fused, as `fma`, and set, `fmul` and then `fadd`,
each choosing a NaN as `pick` says. Every NaN the second gives, the first can too. -/
@[llvm] def fmuladd (e m : Nat) (pick : Nat) (a b c : Val (1 + e + m)) (nnan ninf nsz : Bool := false) :
    Val (1 + e + m) :=
  if (BitVec.ofNat 8 pick).getLsbD 7 then fadd e m pick (fmul e m pick a b nnan ninf nsz) c nnan ninf nsz
  else fma e m pick a b c nnan ninf nsz

/-- `fptrunc` and `fpext`: from the format `e`, `m` to `e'`, `m'`. -/
@[llvm] def fconv (e m e' m' : Nat) (pick : Nat) (a : Val (1 + e + m)) (nnan ninf nsz : Bool := false) :
    Val (1 + e' + m') :=
  match a with
  | some x =>
    if allows nnan ninf x then
      flagged nnan ninf [] (convBits e' m' (BitVec.ofNat 8 pick) (nszIn nsz (BitVec.ofNat 8 pick) 0 x))
    else none
  | none => none

/-- `fptoui`: the integer part, toward zero, or poison if it's negative or doesn't fit, or `x` is a NaN or an
infinity. LangRef: "If the value cannot fit in `ty2`, the result is a poison value." -/
@[llvm] def fptoui (e m w : Nat) (a : Val (1 + e + m)) : Val w :=
  match a with
  | some x => if toUIntOk w x then some ((truncInt w x).setWidth w) else none
  | none => none

/-- `fptosi`: the integer part, toward zero, or poison if it doesn't fit, or `x` is a NaN or an infinity. -/
@[llvm] def fptosi (e m w : Nat) (a : Val (1 + e + m)) : Val w :=
  match a with
  | some x => if toSIntOk w x then some (toSIntVal w x) else none
  | none => none

@[llvm] def fptouiSat (e m w : Nat) (a : Val (1 + e + m)) : Val w := Val.map₁ (toUIntSatBits w) a
@[llvm] def fptosiSat (e m w : Nat) (a : Val (1 + e + m)) : Val w := Val.map₁ (toSIntSatBits w) a

/-- `uitofp`, poison under `nneg` if the operand's sign bit is set. Under `nsz`, LangRef: "if the input value is 0, the
sign bit of the result is non-deterministic", which bit 4 of `pick` chooses. -/
@[llvm] def uitofp (e m : Nat) (a : Val w) (nneg nnan ninf nsz : Bool := false) (pick : Nat := 0) :
    Val (1 + e + m) :=
  match a with
  | some x =>
    if nneg && x.msb then none
    else flagged nnan ninf [] (nszIn nsz (BitVec.ofNat 8 pick) 0 (ofIntBits e m false x))
  | none => none

/-- `sitofp`. Under `nsz`, a zero result's sign is a choice, as for `uitofp`: only a zero gives one. -/
@[llvm] def sitofp (e m : Nat) (a : Val w) (nnan ninf nsz : Bool := false) (pick : Nat := 0) : Val (1 + e + m) :=
  match a with
  | some x => flagged nnan ninf [] (nszIn nsz (BitVec.ofNat 8 pick) 0 (ofIntBits e m x.msb (if x.msb then -x else x)))
  | none => none

/-- An operation on each lane of three vectors, lane `i` choosing with `c.pick i`. -/
@[llvm] def lanes3 (c : Choice) (f : Nat → Val w → Val w → Val w → Val v) (a b d : Vector (Val w) n) :
    Vector (Val v) n :=
  Vector.ofFn fun i => f (c.pick i) a[i] b[i] d[i]

/-- An operation on each lane of two vectors, lane `i` choosing with `c.pick i`. -/
@[llvm] def lanes2 (c : Choice) (f : Nat → Val w → Val w → Val v) (a b : Vector (Val w) n) : Vector (Val v) n :=
  Vector.ofFn fun i => f (c.pick i) a[i] b[i]

/-- An operation on each lane of a vector, lane `i` choosing with `c.pick i`. -/
@[llvm] def lanes1 (c : Choice) (f : Nat → Val w → Val v) (a : Vector (Val w) n) : Vector (Val v) n :=
  Vector.ofFn fun i => f (c.pick i) a[i]

end IRLean.FP
