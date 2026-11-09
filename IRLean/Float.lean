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
infinity. The emitter refuses the rest where they mean anything. -/

namespace IRLean.FP

variable {e m : Nat}

/-! ### Fields and classes -/

/-- The biased exponent field. -/
@[llvm] def expField (x : BitVec (1 + e + m)) : BitVec e := x.extractLsb' m e

/-- The trailing significand field. Its top bit is the quiet bit of a NaN. -/
@[llvm] def fracField (x : BitVec (1 + e + m)) : BitVec m := x.extractLsb' 0 m

/-- The sign bit, alone. -/
@[llvm] def signBit : BitVec (1 + e + m) := 1#(1 + e + m) <<< (e + m)

@[llvm] def isNaN (x : BitVec (1 + e + m)) : Bool := expField x == BitVec.allOnes e && fracField x != 0
@[llvm] def isInf (x : BitVec (1 + e + m)) : Bool := expField x == BitVec.allOnes e && fracField x == 0
@[llvm] def isZero (x : BitVec (1 + e + m)) : Bool := expField x == 0 && fracField x == 0
@[llvm] def isSubnormal (x : BitVec (1 + e + m)) : Bool := expField x == 0 && fracField x != 0
@[llvm] def isNormal (x : BitVec (1 + e + m)) : Bool := expField x != 0 && expField x != BitVec.allOnes e

/-- A quiet NaN has the top bit of its fraction set, LangRef's "quiet bit". -/
@[llvm] def isQuietNaN (x : BitVec (1 + e + m)) : Bool := isNaN x && (fracField x).msb
@[llvm] def isSignalingNaN (x : BitVec (1 + e + m)) : Bool := isNaN x && !(fracField x).msb

/-- Whether `nnan` and `ninf` allow `x`: it isn't a NaN under `nnan`, or an infinity under `ninf`. -/
@[llvm] def allows (nnan ninf : Bool) (x : BitVec (1 + e + m)) : Bool :=
  !(nnan && isNaN x) && !(ninf && isInf x)

/-! ### The sign bit

LangRef: these "act directly on the underlying bit representation and never change anything except possibly for the
sign bit". A NaN keeps its quiet bit and payload. Under `nnan` or `ninf` the result is poison where the operand is a NaN
or an infinity, and the result is one exactly when an operand is. -/

/-- `fneg`: the sign bit flipped. -/
@[llvm] def fneg (e m : Nat) (a : Val (1 + e + m)) (nnan ninf : Bool := false) : Val (1 + e + m) :=
  match a with
  | some x => if allows nnan ninf x then some (x ^^^ signBit) else none
  | none => none

/-- `llvm.fabs`: the sign bit cleared. -/
@[llvm] def fabs (e m : Nat) (a : Val (1 + e + m)) (nnan ninf : Bool := false) : Val (1 + e + m) :=
  match a with
  | some x => if allows nnan ninf x then some (x &&& ~~~signBit) else none
  | none => none

/-- `llvm.copysign`: the first operand with the second's sign bit. -/
@[llvm] def copysign (e m : Nat) (a b : Val (1 + e + m)) (nnan ninf : Bool := false) : Val (1 + e + m) :=
  match a, b with
  | some x, some y =>
    if allows nnan ninf x && allows nnan ninf y then some ((x &&& ~~~signBit) ||| (y &&& signBit)) else none
  | _, _ => none

/-! ### Comparison -/

/-- IEEE 754's less-than, false if either is a NaN. Zeros of either sign are equal, and otherwise the order is the sign
and then the magnitude, the bits below the sign read as an unsigned integer. -/
@[llvm] def lt (x y : BitVec (1 + e + m)) : Bool :=
  let mx := x.extractLsb' 0 (e + m)
  let my := y.extractLsb' 0 (e + m)
  if isNaN x || isNaN y then false
  else if isZero x && isZero y then false
  else if x.msb != y.msb then x.msb
  else if x.msb then my.ult mx else mx.ult my

/-- IEEE 754's equality, false if either is a NaN. `0.0` equals `-0.0`. -/
@[llvm] def eq (x y : BitVec (1 + e + m)) : Bool :=
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
@[llvm] def classIn (mask : Nat) (x : BitVec (1 + e + m)) : Bool :=
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

end IRLean.FP
