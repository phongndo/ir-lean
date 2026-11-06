import LLVMLean.Basic

/-! LLVM's integer instructions and intrinsics, following the LangRef. `tests/opcheck.py` compares
each of these with LLVM's own constant folder. -/

namespace LLVMLean.Val

variable {w v : Nat}

/-- Applies `f` unless an operand is poison. -/
@[llvm, inline] def map₂ (f : BitVec w → BitVec w → BitVec v) : Val w → Val w → Val v
  | some a, some b => some (f a b)
  | _, _ => none

/-- Applies `f` unless the operand is poison. -/
@[llvm, inline] def map₁ (f : BitVec w → BitVec v) : Val w → Val v
  | some a => some (f a)
  | none => none

/-! ### Arithmetic -/

@[llvm, inline] def add (a b : Val w) (nuw nsw : Bool := false) : Val w :=
  match a, b with
  | some x, some y =>
    if (nuw && x.uaddOverflow y) || (nsw && x.saddOverflow y) then none else some (x + y)
  | _, _ => none

@[llvm, inline] def sub (a b : Val w) (nuw nsw : Bool := false) : Val w :=
  match a, b with
  | some x, some y =>
    if (nuw && x.usubOverflow y) || (nsw && x.ssubOverflow y) then none else some (x - y)
  | _, _ => none

@[llvm, inline] def mul (a b : Val w) (nuw nsw : Bool := false) : Val w :=
  match a, b with
  | some x, some y =>
    if (nuw && x.umulOverflow y) || (nsw && x.smulOverflow y) then none else some (x * y)
  | _, _ => none

/-! ### Division. A zero or poison divisor, or signed overflow, is immediate undefined behavior. -/

@[llvm, inline] def udiv (a b : Val w) (exact : Bool := false) : Outcome (Val w) :=
  match b with
  | none => Outcome.ub .divByPoison
  | some y =>
    if y == 0#w then Outcome.ub .divByZero else
    match a with
    | none => Outcome.ok none
    | some x => Outcome.ok (if exact && x % y != 0#w then none else some (x / y))

@[llvm, inline] def urem (a b : Val w) : Outcome (Val w) :=
  match b with
  | none => Outcome.ub .divByPoison
  | some y =>
    if y == 0#w then Outcome.ub .divByZero else
    match a with
    | none => Outcome.ok none
    | some x => Outcome.ok (some (x % y))

/-- Whether `y` is the all-ones divisor, which overflows if the dividend is the minimum value. A
poison dividend could be that minimum, so the model treats that case as undefined too. -/
@[llvm, inline] def divOverflows (a : Val w) (y : BitVec w) : Bool :=
  match a with
  | none => y == BitVec.allOnes w
  | some x => x.sdivOverflow y

@[llvm, inline] def sdiv (a b : Val w) (exact : Bool := false) : Outcome (Val w) :=
  match b with
  | none => Outcome.ub .divByPoison
  | some y =>
    if y == 0#w then Outcome.ub .divByZero else
    if divOverflows a y then Outcome.ub .divOverflow else
    match a with
    | none => Outcome.ok none
    | some x => Outcome.ok (if exact && x.srem y != 0#w then none else some (x.sdiv y))

@[llvm, inline] def srem (a b : Val w) : Outcome (Val w) :=
  match b with
  | none => Outcome.ub .divByPoison
  | some y =>
    if y == 0#w then Outcome.ub .divByZero else
    if divOverflows a y then Outcome.ub .divOverflow else
    match a with
    | none => Outcome.ok none
    | some x => Outcome.ok (some (x.srem y))

/-! ### Bitwise -/

@[llvm, inline] def and : Val w → Val w → Val w := map₂ (· &&& ·)
@[llvm, inline] def xor : Val w → Val w → Val w := map₂ (· ^^^ ·)

@[llvm, inline] def or (a b : Val w) (disjoint : Bool := false) : Val w :=
  match a, b with
  | some x, some y => if disjoint && x &&& y != 0#w then none else some (x ||| y)
  | _, _ => none

/-- Whether a shift amount is in range. Comparing as bitvectors, rather than through `toNat`, keeps
this decidable by `bv_decide`. `w` always fits in `w` bits. -/
@[llvm, inline] def shiftOk (y : BitVec w) : Bool := y < BitVec.ofNat w w

@[llvm, inline] def shl (a b : Val w) (nuw nsw : Bool := false) : Val w :=
  match a, b with
  | some x, some y =>
    if !shiftOk y then none
    else if nuw && (x <<< y) >>> y != x then none
    else if nsw && (x <<< y).sshiftRight' y != x then none
    else some (x <<< y)
  | _, _ => none

@[llvm, inline] def lshr (a b : Val w) (exact : Bool := false) : Val w :=
  match a, b with
  | some x, some y =>
    if !shiftOk y then none
    else if exact && (x >>> y) <<< y != x then none
    else some (x >>> y)
  | _, _ => none

@[llvm, inline] def ashr (a b : Val w) (exact : Bool := false) : Val w :=
  match a, b with
  | some x, some y =>
    if !shiftOk y then none
    else if exact && (x.sshiftRight' y) <<< y != x then none
    else some (x.sshiftRight' y)
  | _, _ => none

/-! ### Comparison. `samesign` gives poison if the operands' signs differ. -/

@[llvm, inline] def icmp (p : BitVec w → BitVec w → Bool) (a b : Val w) (samesign : Bool := false) :
    Val 1 :=
  match a, b with
  | some x, some y =>
    if samesign && x.msb != y.msb then none else some (BitVec.ofBool (p x y))
  | _, _ => none

@[llvm, inline] def icmpEq (a b : Val w) (samesign : Bool := false) : Val 1 :=
  icmp (· == ·) a b samesign
@[llvm, inline] def icmpNe (a b : Val w) (samesign : Bool := false) : Val 1 :=
  icmp (· != ·) a b samesign
@[llvm, inline] def icmpUlt (a b : Val w) (samesign : Bool := false) : Val 1 :=
  icmp BitVec.ult a b samesign
@[llvm, inline] def icmpUle (a b : Val w) (samesign : Bool := false) : Val 1 :=
  icmp BitVec.ule a b samesign
@[llvm, inline] def icmpUgt (a b : Val w) (samesign : Bool := false) : Val 1 :=
  icmp (fun x y => BitVec.ult y x) a b samesign
@[llvm, inline] def icmpUge (a b : Val w) (samesign : Bool := false) : Val 1 :=
  icmp (fun x y => BitVec.ule y x) a b samesign
@[llvm, inline] def icmpSlt (a b : Val w) (samesign : Bool := false) : Val 1 :=
  icmp BitVec.slt a b samesign
@[llvm, inline] def icmpSle (a b : Val w) (samesign : Bool := false) : Val 1 :=
  icmp BitVec.sle a b samesign
@[llvm, inline] def icmpSgt (a b : Val w) (samesign : Bool := false) : Val 1 :=
  icmp (fun x y => BitVec.slt y x) a b samesign
@[llvm, inline] def icmpSge (a b : Val w) (samesign : Bool := false) : Val 1 :=
  icmp (fun x y => BitVec.sle y x) a b samesign

/-! ### Casts -/

@[llvm, inline] def zext (v : Nat) (a : Val w) (nneg : Bool := false) : Val v :=
  match a with
  | some x => if nneg && x.msb then none else some (x.setWidth v)
  | none => none

@[llvm, inline] def sext (v : Nat) (a : Val w) : Val v := map₁ (·.signExtend v) a

@[llvm, inline] def trunc (v : Nat) (a : Val w) (nuw nsw : Bool := false) : Val v :=
  match a with
  | some x =>
    if nuw && (x.setWidth v).setWidth w != x then none
    else if nsw && (x.setWidth v).signExtend w != x then none
    else some (x.setWidth v)
  | none => none

/-- `freeze` keeps a value. Poison would become an arbitrary value, which the model doesn't choose:
see `ModelStop.freezePoison`. -/
@[llvm, inline] def freeze {τ : Type} (a : Option τ) : Outcome (Option τ) :=
  match a with
  | some x => Outcome.ok (some x)
  | none => Outcome.stop .freezePoison

/-- The `range` attribute: values outside the half-open, possibly wrapping range become poison. -/
@[llvm, inline] def range (lo hi : BitVec w) (a : Val w) : Val w :=
  match a with
  | some x => if BitVec.ult (x - lo) (hi - lo) then some x else none
  | none => none

/-! ### Intrinsics -/

@[llvm, inline] def umin : Val w → Val w → Val w := map₂ fun x y => if BitVec.ule x y then x else y
@[llvm, inline] def umax : Val w → Val w → Val w := map₂ fun x y => if BitVec.ule x y then y else x
@[llvm, inline] def smin : Val w → Val w → Val w := map₂ fun x y => if BitVec.sle x y then x else y
@[llvm, inline] def smax : Val w → Val w → Val w := map₂ fun x y => if BitVec.sle x y then y else x

@[llvm, inline] def abs (a : Val w) (intMinPoison : Bool) : Val w :=
  match a with
  | some x =>
    if intMinPoison && x == BitVec.intMin w then none
    else some (if x.msb then -x else x)
  | none => none

@[llvm, inline] def ctpop : Val w → Val w := map₁ BitVec.cpop
@[llvm, inline] def bitreverse : Val w → Val w := map₁ BitVec.reverse

@[llvm, inline] def ctlz (a : Val w) (zeroPoison : Bool) : Val w :=
  match a with
  | some x => if zeroPoison && x == 0#w then none else some x.clz
  | none => none

@[llvm, inline] def cttz (a : Val w) (zeroPoison : Bool) : Val w :=
  match a with
  | some x => if zeroPoison && x == 0#w then none else some x.ctz
  | none => none

/-- Reverses the bytes of a value whose width is a multiple of 16. -/
def bswapRaw (x : BitVec w) : BitVec w :=
  (List.range (w / 8)).foldl
    (fun acc i => acc ||| (((x >>> (8 * i)) &&& BitVec.ofNat w 0xff) <<< (w - 8 - 8 * i))) 0#w

@[llvm, inline] def bswap : Val w → Val w := map₁ bswapRaw

/-- Concatenates `x` and `y`, shifts left by `s` modulo `w`, and keeps the high half. -/
def fshlRaw (x y s : BitVec w) : BitVec w :=
  let k := s.toNat % w
  if k = 0 then x else (x <<< k) ||| (y >>> (w - k))

/-- Concatenates `x` and `y`, shifts right by `s` modulo `w`, and keeps the low half. -/
def fshrRaw (x y s : BitVec w) : BitVec w :=
  let k := s.toNat % w
  if k = 0 then y else (x <<< (w - k)) ||| (y >>> k)

@[llvm, inline] def fshl : Val w → Val w → Val w → Val w
  | some x, some y, some s => some (fshlRaw x y s)
  | _, _, _ => none

@[llvm, inline] def fshr : Val w → Val w → Val w → Val w
  | some x, some y, some s => some (fshrRaw x y s)
  | _, _, _ => none

@[llvm, inline] def uaddSat : Val w → Val w → Val w :=
  map₂ fun x y => if x.uaddOverflow y then BitVec.allOnes w else x + y
@[llvm, inline] def usubSat : Val w → Val w → Val w :=
  map₂ fun x y => if BitVec.ult x y then 0#w else x - y

/-- The saturated value when a signed operation overflows: the sign of `x` decides the direction. -/
@[llvm, inline] def signedLimit (x : BitVec w) : BitVec w :=
  if x.msb then BitVec.intMin w else BitVec.intMax w

@[llvm, inline] def saddSat : Val w → Val w → Val w :=
  map₂ fun x y => if x.saddOverflow y then signedLimit x else x + y
@[llvm, inline] def ssubSat : Val w → Val w → Val w :=
  map₂ fun x y => if x.ssubOverflow y then signedLimit x else x - y

/-- Helper for `*.with.overflow`: the wrapped result and whether it overflowed. -/
@[llvm, inline] def withOverflow (f : BitVec w → BitVec w → BitVec w)
    (o : BitVec w → BitVec w → Bool) : Val w → Val w → Val w × Val 1
  | some x, some y => (some (f x y), some (BitVec.ofBool (o x y)))
  | _, _ => (none, none)

@[llvm, inline] def uaddWithOverflow : Val w → Val w → Val w × Val 1 :=
  withOverflow (· + ·) BitVec.uaddOverflow
@[llvm, inline] def saddWithOverflow : Val w → Val w → Val w × Val 1 :=
  withOverflow (· + ·) BitVec.saddOverflow
@[llvm, inline] def usubWithOverflow : Val w → Val w → Val w × Val 1 :=
  withOverflow (· - ·) BitVec.usubOverflow
@[llvm, inline] def ssubWithOverflow : Val w → Val w → Val w × Val 1 :=
  withOverflow (· - ·) BitVec.ssubOverflow
@[llvm, inline] def umulWithOverflow : Val w → Val w → Val w × Val 1 :=
  withOverflow (· * ·) BitVec.umulOverflow
@[llvm, inline] def smulWithOverflow : Val w → Val w → Val w × Val 1 :=
  withOverflow (· * ·) BitVec.smulOverflow

/-- `llvm.ucmp` and `llvm.scmp`: -1, 0 or 1. -/
@[llvm, inline] def threeWay (lt : BitVec w → BitVec w → Bool) (v : Nat) : Val w → Val w → Val v
  | some x, some y =>
    some (if lt x y then BitVec.allOnes v else if x == y then 0#v else BitVec.ofNat v 1)
  | _, _ => none

@[llvm, inline] def ucmp (v : Nat) : Val w → Val w → Val v := threeWay BitVec.ult v
@[llvm, inline] def scmp (v : Nat) : Val w → Val w → Val v := threeWay BitVec.slt v

end LLVMLean.Val
