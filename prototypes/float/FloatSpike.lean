import Std.Tactic.BVDecide

/-! # A prototype of IEEE 754 binary formats on bit vectors

This is the spike behind [`docs/float.md`](../../docs/float.md): just enough of floating point to measure what
`bv_decide` costs on `fadd`, `fmul`, `fdiv` and `fcmp`. It isn't the model. It imports only Lean, and nothing of
`IRLean`.

A format has `e` exponent bits and `m` trailing significand bits, and a value is a `BitVec (1 + e + m)`: the sign on
top, then the biased exponent, then the fraction. Every operation is a circuit on bit vectors, so at fixed `e` and `m`
`bv_decide` can bit-blast it, and every one is defined for every `e` and `m`, so facts about all formats can be proved
by hand. The circuits follow symfpu's: unpack, compute exactly or with a sticky bit, and round once.

No definition has a `let` or a `have`. Each value an operation computes is a definition of its own, of the operation's
inputs, marked `@[bv_normalize]` so that `bv_decide` unfolds it. In Lean 4.35.0, `bv_decide`'s normalizer leaves terms
that don't type, such as `BitVec.ult` of two `Bool`s, where a definition it unfolds binds a value with `let` or `have`,
and unfolding with `simp` first, which substitutes them, costs more than `bv_decide` itself at `float` and above.
`docs/float.md` has the measurements. -/

namespace FloatSpike

variable {e m n : Nat}

/-! ### Fields and classes -/

/-- The biased exponent field. -/
@[bv_normalize] def expField (x : BitVec (1 + e + m)) : BitVec e := x.extractLsb' m e

/-- The trailing significand field. -/
@[bv_normalize] def fracField (x : BitVec (1 + e + m)) : BitVec m := x.extractLsb' 0 m

@[bv_normalize] def isNaN (x : BitVec (1 + e + m)) : Bool :=
  expField x == BitVec.allOnes e && fracField x != 0

@[bv_normalize] def isInf (x : BitVec (1 + e + m)) : Bool :=
  expField x == BitVec.allOnes e && fracField x == 0

@[bv_normalize] def isZero (x : BitVec (1 + e + m)) : Bool :=
  expField x == 0 && fracField x == 0

/-- `x` with its sign set to `s`. -/
@[bv_normalize] def withSign (s : Bool) (x : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  (BitVec.ofBool s ++ x.extractLsb' 0 (e + m)).cast (by omega)

@[bv_normalize] def infinity (s : Bool) : BitVec (1 + e + m) :=
  (BitVec.ofBool s ++ BitVec.allOnes e ++ 0#m).cast (by omega)

@[bv_normalize] def zero (s : Bool) : BitVec (1 + e + m) :=
  (BitVec.ofBool s ++ 0#(e + m)).cast (by omega)

/-- The quiet bit is the top bit of the fraction. -/
@[bv_normalize] def quietBit : BitVec (1 + e + m) := 1#(1 + e + m) <<< (m - 1)

/-- LangRef's "preferred NaN": positive, quiet, and an all-zero payload. -/
@[bv_normalize] def preferredNaN : BitVec (1 + e + m) :=
  (0#1 ++ BitVec.allOnes e ++ (1#m <<< (m - 1))).cast (by omega)

/-! ### LangRef's NaN results

When IEEE 754 gives a NaN, LangRef 23.1.3 lets an operation return, with either sign, the preferred NaN, or an input
NaN quieted, or an input NaN unchanged. `pick` chooses among them: bit 0 is the sign, bit 1 says unchanged rather than
quieted, and bits 2 and 3 name the operand, 0 for the preferred NaN. An operand that isn't a NaN gives the preferred
NaN. So every choice is one LangRef allows, and each it allows is some choice. -/

@[bv_normalize] def nanFrom (pick : BitVec 4) (x : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  if isNaN x then (if pick.getLsbD 1 then x else x ||| quietBit) else preferredNaN

@[bv_normalize] def nan2 (pick : BitVec 4) (a b : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  withSign (pick.getLsbD 0)
    (if pick.extractLsb' 2 2 == 1#2 then nanFrom pick a
     else if pick.extractLsb' 2 2 == 2#2 then nanFrom pick b else preferredNaN)

/-! ### Unpacking a finite value

A finite `x` is `M × 2 ^ (t - bias - m)`, with `M` the significand, its implicit bit included, and `t` the biased
exponent of its last place, at least 1. Exponents are signed, `e + m + 3` bits wide, which holds every exponent an
operation here forms. -/

/-- The significand, with the implicit bit when `x` is normal. -/
@[bv_normalize] def sig (x : BitVec (1 + e + m)) : BitVec (m + 1) :=
  (BitVec.ofBool (expField x != 0) ++ fracField x).cast (by omega)

/-- The biased exponent of the last place: the exponent field, or 1 for a subnormal or zero. -/
@[bv_normalize] def lsbExp (x : BitVec (1 + e + m)) : BitVec (e + m + 3) :=
  if expField x == 0 then 1#_ else (expField x).setWidth _

/-- The exponent bias, `2 ^ (e - 1) - 1`. -/
@[bv_normalize] def bias : BitVec (e + m + 3) := BitVec.ofNat _ (2 ^ (e - 1) - 1)

/-! ### Rounding

`round e m s S t` is the value `(-1) ^ s × S × 2 ^ (t - bias - m)` rounded to nearest, ties to even, as IEEE 754's
default: a finite value or an infinity, never a NaN. `S` is exact, or has a sticky bit in its last place that's at
least two places below where the result rounds, which each caller arranges. It finds `S`'s top bit, keeps `m + 1` bits
from it, or fewer where the result is subnormal, rounds on the next bit and the rest, and adds the exponent and the
fraction as one integer, so a carry out of the fraction raises the exponent and the largest finite value rounds up to
infinity. Exponents are `e + m + 3` bits, and `S` is widened to `n + m + 3` to shift. -/

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
  if S == 0#n then zero s
  else if !((rLast e m S t).slt (BitVec.ofNat _ (2 ^ e - 1))) ||
      !((rMag e m S t).ult (BitVec.ofNat _ ((2 ^ e - 1) * 2 ^ m))) then infinity s
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
@[bv_normalize] def aXe (a b : BitVec (1 + e + m)) : BitVec (e + m + 3) := if aSwap a b then lsbExp b else lsbExp a
@[bv_normalize] def aYe (a b : BitVec (1 + e + m)) : BitVec (e + m + 3) := if aSwap a b then lsbExp a else lsbExp b

/-- How far `y` shifts, at most `m + 5`, past which it's all sticky. -/
@[bv_normalize] def aShift (a b : BitVec (1 + e + m)) : BitVec (m + 5) :=
  if (aXe a b - aYe a b).ult (BitVec.ofNat _ (m + 5)) then (aXe a b - aYe a b).setWidth _ else BitVec.ofNat _ (m + 5)

/-- `y` shifted, with what's shifted out folded into its last bit. -/
@[bv_normalize] def aYj (a b : BitVec (1 + e + m)) : BitVec (m + 5) :=
  (aY a b >>> aShift a b) |||
    (BitVec.ofBool ((aY a b &&& ((1#_ <<< aShift a b) - 1#_)) != 0#_)).setWidth _

@[bv_normalize] def aSum (a b : BitVec (1 + e + m)) : BitVec (m + 5) :=
  if aXs a b == aYs a b then aX a b + aYj a b
  else if (aYj a b).ule (aX a b) then aX a b - aYj a b else aYj a b - aX a b

@[bv_normalize] def aSign (a b : BitVec (1 + e + m)) : Bool :=
  if aXs a b == aYs a b then aXs a b else if (aYj a b).ule (aX a b) then aXs a b else aYs a b

/-- The IEEE 754 sum, with a NaN result as `nan2`. An exact zero sum is `+0`, or `-0` when both are `-0`. -/
@[bv_normalize] def fadd (pick : BitVec 4) (a b : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  if isNaN a || isNaN b || (isInf a && isInf b && a.msb != b.msb) then nan2 pick a b
  else if isInf a then a
  else if isInf b then b
  else if aSum a b == 0#_ then zero (a.msb && b.msb)
  else round e m (aSign a b) (aSum a b) (aXe a b - 3#_)

@[bv_normalize] def fneg (a : BitVec (1 + e + m)) : BitVec (1 + e + m) := withSign (!a.msb) a

/-- A NaN result's sign is free, so taking the second operand's NaN negated is the same set of results. -/
@[bv_normalize] def fsub (pick : BitVec 4) (a b : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  fadd pick a (fneg b)

/-! ### Multiplication and division -/

/-- The IEEE 754 product: the significands multiply exactly, then one rounding. -/
@[bv_normalize] def fmul (pick : BitVec 4) (a b : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  if isNaN a || isNaN b || (isInf a && isZero b) || (isZero a && isInf b) then nan2 pick a b
  else if isInf a || isInf b then infinity (a.msb != b.msb)
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

/-- The IEEE 754 quotient: significands normalized, divided with `m + 3` more places, and the remainder as a sticky
bit. -/
@[bv_normalize] def fdiv (pick : BitVec 4) (a b : BitVec (1 + e + m)) : BitVec (1 + e + m) :=
  if isNaN a || isNaN b || (isInf a && isInf b) || (isZero a && isZero b) then nan2 pick a b
  else if isInf a || isZero b then infinity (a.msb != b.msb)
  else if isInf b || isZero a then zero (a.msb != b.msb)
  else round e m (a.msb != b.msb) (dQuot a b ++ BitVec.ofBool (dRem a b != 0#_)) (dExp a b)

/-! ### Comparison -/

/-- Ordered less-than, false if either is a NaN. Zeros of either sign are equal. -/
@[bv_normalize] def flt (a b : BitVec (1 + e + m)) : Bool :=
  if isNaN a || isNaN b then false
  else if isZero a && isZero b then false
  else if a.msb != b.msb then a.msb
  else if a.msb then (b.extractLsb' 0 (e + m)).ult (a.extractLsb' 0 (e + m))
  else (a.extractLsb' 0 (e + m)).ult (b.extractLsb' 0 (e + m))

@[bv_normalize] def feq (a b : BitVec (1 + e + m)) : Bool :=
  !(isNaN a || isNaN b) && (a == b || (isZero a && isZero b))

/-- `fcmp`'s sixteen predicates by LLVM's numbering, `FCmpInst::Predicate`: from the lowest bit, equal, greater,
less and unordered. -/
@[bv_normalize] def fcmp (pred : BitVec 4) (a b : BitVec (1 + e + m)) : Bool :=
  (pred.getLsbD 0 && feq a b) || (pred.getLsbD 1 && flt b a) || (pred.getLsbD 2 && flt a b) ||
    (pred.getLsbD 3 && (isNaN a || isNaN b))

end FloatSpike
