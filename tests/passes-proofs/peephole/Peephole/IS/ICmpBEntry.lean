import Peephole.IS.ICmpBBinOp
import Peephole.IS.ICmpBAndOr
import Peephole.IS.ICmpBSelectCond

/-! # Where InstSimplify's dispatcher reaches the `icmp-b` folds, for the comparison with `opt`

None of this family's folds is called on an instruction. `simplifyInstructionWithOperands` calls `simplifyICmpInst` on
an `icmp`, `simplifySelectInst` on a `select`, and `simplifyAndInst` and `simplifyOrInst` on an `and` and an `or`, with
`MaxRecurse` at `RecursionLimit`, 3, and those reach these folds after steps of their own, which other families model.
Each `onInst` here follows its dispatcher's function to the folds:

- Every statement before the folds that could end the function, where it could, is a `.delegate`: the entry claims
  nothing there. Where none could, the folds run, as the C++ runs them. Whether one could is read from the C++'s
  guards, below, and errs towards delegating.
- After the folds, the rest of the function is a `.delegate`.
- What the folds take as parameters is what's faithful to delegate: the recursive `simplifyICmpInst` delegates every
  call, `simplifyUnsignedRangeCheck` delegates where its first compare is `icmp eq/ne Y, 0` and declines elsewhere,
  as the C++ does, and `matchDecomposedSelectPattern`'s limit test may fire for every relational predicate, since it
  answers for no equality.
- `simplifyAndOrOfICmpsWithConstants` asks `ConstantRange`: `CRQuery.llvm` computes its answers as
  `llvm/lib/IR/ConstantRange.cpp` does. Nothing proves it sound; the folds' theorems hold for every sound `CRQuery`.

`Term` carries no metadata and no attributes, so `simplifyICmpInst`'s step on `!range` and `range` finds none, as the
comparison's cases, which have none, don't either. -/

namespace Peephole.IS.ICmpB

open IRLean

variable {w : Nat}

/-! ### `ConstantRange`, computed -/

/-- LLVM's `ConstantRange` on `BitVec w`: `[lo, hi)`, wrapping, and `lo == hi` the full set at the maximum value and
the empty set at zero. -/
structure CR (w : Nat) where
  lo : BitVec w
  hi : BitVec w

namespace CR

def full (w : Nat) : CR w := ⟨BitVec.allOnes w, BitVec.allOnes w⟩
def empty (w : Nat) : CR w := ⟨0#w, 0#w⟩
def isFull (c : CR w) : Bool := c.lo == c.hi && c.lo == BitVec.allOnes w
def isEmpty (c : CR w) : Bool := c.lo == c.hi && c.lo == 0#w
/-- `isUpperWrapped`: `Lower.ugt(Upper)`. -/
def wrapped (c : CR w) : Bool := BitVec.ult c.hi c.lo
/-- `getNonEmpty`. -/
def nonEmpty (lo hi : BitVec w) : CR w := if lo == hi then full w else ⟨lo, hi⟩
/-- `isSizeStrictlySmallerThan`. -/
def smaller (a b : CR w) : Bool :=
  if a.isFull then false else if b.isFull then true else BitVec.ult (a.hi - a.lo) (b.hi - b.lo)
/-- `getPreferredRange` with `Smallest`, the default. -/
def preferred (a b : CR w) : CR w := if a.smaller b then a else b

/-- `makeExactICmpRegion(Pred, C)`: `makeAllowedICmpRegion` of the single element `C`, whose unsigned and signed
minimum and maximum are all `C`. -/
def exactICmp (p : Pred) (c : BitVec w) : CR w :=
  match p with
  | .eq => ⟨c, c + 1#w⟩
  | .ne => ⟨c + 1#w, c⟩
  | .ult => if c == 0#w then empty w else ⟨0#w, c⟩
  | .slt => if c == BitVec.intMin w then empty w else ⟨BitVec.intMin w, c⟩
  | .ule => nonEmpty 0#w (c + 1#w)
  | .sle => nonEmpty (BitVec.intMin w) (c + 1#w)
  | .ugt => if c == BitVec.allOnes w then empty w else ⟨c + 1#w, 0#w⟩
  | .sgt => if c == BitVec.intMax w then empty w else ⟨c + 1#w, BitVec.intMin w⟩
  | .uge => nonEmpty c 0#w
  | .sge => nonEmpty c (BitVec.intMin w)

/-- `intersectWith`, once neither is empty or full and `a` is wrapped where `b` is. -/
def intersectCore (a b : CR w) : CR w :=
  if !a.wrapped && !b.wrapped then
    if BitVec.ult a.lo b.lo then
      if BitVec.ule a.hi b.lo then empty w else if BitVec.ult a.hi b.hi then ⟨b.lo, a.hi⟩ else b
    else if BitVec.ult a.hi b.hi then a else if BitVec.ult a.lo b.hi then ⟨a.lo, b.hi⟩ else empty w
  else if a.wrapped && !b.wrapped then
    if BitVec.ult b.lo a.hi then
      if BitVec.ult b.hi a.hi then b else if BitVec.ule b.hi a.lo then ⟨b.lo, a.hi⟩ else preferred a b
    else if BitVec.ult b.lo a.lo then
      if BitVec.ule b.hi a.lo then empty w else ⟨a.lo, b.hi⟩
    else b
  else if BitVec.ult b.hi a.hi then
    if BitVec.ult b.lo a.hi then preferred a b else if BitVec.ult b.lo a.lo then ⟨a.lo, b.hi⟩ else b
  else if BitVec.ule b.hi a.lo then
    if BitVec.ult b.lo a.lo then a else ⟨b.lo, a.hi⟩
  else preferred a b

/-- `intersectWith(CR, Smallest)`. -/
def intersect (a b : CR w) : CR w :=
  if a.isEmpty || b.isFull then a
  else if b.isEmpty || a.isFull then b
  else if !a.wrapped && b.wrapped then intersectCore b a
  else intersectCore a b

/-- `unionWith`, once neither is empty or full and `a` is wrapped where `b` is. -/
def unionCore (a b : CR w) : CR w :=
  if !a.wrapped && !b.wrapped then
    if BitVec.ult b.hi a.lo || BitVec.ult a.hi b.lo then preferred ⟨a.lo, b.hi⟩ ⟨b.lo, a.hi⟩
    else
      let l := if BitVec.ult b.lo a.lo then b.lo else a.lo
      let u := if BitVec.ult (a.hi - 1#w) (b.hi - 1#w) then b.hi else a.hi
      if l == 0#w && u == 0#w then full w else ⟨l, u⟩
  else if !b.wrapped then
    if BitVec.ule b.hi a.hi || BitVec.ule a.lo b.lo then a
    else if BitVec.ule b.lo a.hi && BitVec.ule a.lo b.hi then full w
    else if BitVec.ult a.hi b.lo && BitVec.ult b.hi a.lo then preferred ⟨a.lo, b.hi⟩ ⟨b.lo, a.hi⟩
    else if BitVec.ult a.hi b.lo && BitVec.ule a.lo b.hi then ⟨b.lo, a.hi⟩
    else ⟨a.lo, b.hi⟩
  else if BitVec.ule b.lo a.hi || BitVec.ule a.lo b.hi then full w
  else ⟨if BitVec.ult b.lo a.lo then b.lo else a.lo, if BitVec.ult a.hi b.hi then b.hi else a.hi⟩

/-- `unionWith(CR, Smallest)`. -/
def union (a b : CR w) : CR w :=
  if a.isFull || b.isEmpty then a
  else if b.isFull || a.isEmpty then b
  else if !a.wrapped && b.wrapped then unionCore b a
  else unionCore a b

/-- `contains(Other)`. -/
def contains (a b : CR w) : Bool :=
  if a.isFull || b.isEmpty then true
  else if a.isEmpty || b.isFull then false
  else if !a.wrapped then !b.wrapped && BitVec.ule a.lo b.lo && BitVec.ule b.hi a.hi
  else if !b.wrapped then BitVec.ule b.hi a.hi || BitVec.ule a.lo b.lo
  else BitVec.ule b.hi a.hi && BitVec.ule a.lo b.lo

end CR

/-- `ConstantRange`'s answers as LLVM computes them. Nothing here proves them sound. -/
def CRQuery.llvm : CRQuery where
  emptyAnd p0 c0 p1 c1 := ((CR.exactICmp p0 c0).intersect (CR.exactICmp p1 c1)).isEmpty
  fullOr p0 c0 p1 c1 := ((CR.exactICmp p0 c0).union (CR.exactICmp p1 c1)).isFull
  contains p0 c0 p1 c1 := (CR.exactICmp p0 c0).contains (CR.exactICmp p1 c1)

/-! ### What the folds take, where they're reached from an instruction -/

/-- The recursive `simplifyICmpInst`, which another family models: every call delegated. -/
def ICmpSimp.delegating : ICmpSimp := fun _ _ {_} _ _ _ => .delegated "simplifyICmpInst"

/-- `simplifyUnsignedRangeCheck`, which another family models: it declines unless its first compare is
`icmp eq/ne Y, 0`, as its first statement says, and is delegated there. -/
def URC.delegating : URC := fun z _ _ =>
  match z with
  | .icmp _ p _ _ r => if isEquality p && zero r then .delegated "simplifyUnsignedRangeCheck" else .null
  | _ => .null

/-- `matchDecomposedSelectPattern`'s limit test, unmodelled: it may fire for any relational predicate, and never for
an equality, where `matchDecomposedSelectPattern` answers `SPF_UNKNOWN`. -/
def SPLimit.relational : SPLimit := fun c {_} _ _ =>
  match c with
  | .icmp _ p _ _ _ => isRelational p
  | _ => false

/-! ### `icmp` -/

/-- `isa<CastInst>(V)`. -/
def isCast : Term w → Bool
  | .zext .. | .sext .. | .trunc .. => true
  | _ => false

/-- Whether a statement of `simplifyICmpInst` before `simplifyICmpWithBinOp` could end it, once a lone constant is on
the right: `icmp X, poison`, `icmp X, undef` and `icmp X, X`; `simplifyICmpOfBools`, for `i1` operands;
`simplifyICmpWithZero` and `simplifyICmpWithConstant`, which need a `ConstantInt` on the right; a compare of a cast
with a constant or a cast; and `isKnownNonEqual`. -/
def icmpEarlier (o : Oracle) (p : Pred) (lhs rhs : Term w) : Bool :=
  isUndefValue rhs || specific lhs rhs || w == 1 || (apint rhs).isSome ||
    (isCast lhs && (rhs.isConstant || isCast rhs)) || (isEquality p && !zero rhs && o.nonEqual lhs rhs)

/-- `simplifyICmpInst` from where a lone constant is on the right, to its last forward into this family. -/
def icmpEntry.steps (o : Oracle) (p : Pred) (s : Bool) (lhs rhs : Term w) : List (Step 1) :=
  [ if icmpEarlier o p lhs rhs then .delegate "simplifyICmpInst: a step before simplifyICmpWithBinOp" else .next,
    fwd "IS.simplifyICmpWithBinOp" (simplifyICmpWithBinOp o ICmpSimp.delegating p s lhs rhs 3),
    fwd "IS.simplifyICmpWithMinMax" (simplifyICmpWithMinMax ICmpSimp.delegating p lhs rhs 3),
    fwd "IS.simplifyICmpWithIntrinsicOnLHS" (simplifyICmpWithIntrinsicOnLHS p lhs rhs),
    fwd "IS.simplifyICmpWithIntrinsicOnLHS" (simplifyICmpWithIntrinsicOnLHS (swapP p) rhs lhs),
    .delegate "simplifyICmpInst: a step after simplifyICmpWithIntrinsicOnLHS" ]

/-- `simplifyICmpInst`'s first statements: two constants go to the constant folder, and a lone constant moves to the
right, with the predicate swapped and `samesign` dropped. -/
def icmpEntry (o : Oracle) (p : Pred) (s : Bool) (lhs rhs : Term w) : Result 1 :=
  if lhs.isConstant then
    if rhs.isConstant then .delegated "ConstantFoldCompareInstOperands"
    else run (icmpEntry.steps o (swapP p) false rhs lhs)
  else run (icmpEntry.steps o p s lhs rhs)

/-- What InstSimplify does with an `icmp`, as far as it reaches this family's folds. -/
def icmpOnInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .icmp _ p s a b => icmpEntry o p s a b
  | _, _ => .null

/-! ### `select` -/

/-- Whether a statement of `simplifySelectInst` before `simplifySelectWithICmpCond` could end it: a constant condition,
the `i1` logic folds where the condition has the arms' type, `select ?, X, X`, and a poison or `undef` arm. -/
def selectEarlier (c : Term 1) (t e : Term w) : Bool :=
  c.isConstant || w == 1 || specific t e || isUndefValue t || isUndefValue e

def selectEntry.steps (c : Term 1) (t e : Term w) : List (Step w) :=
  [ if selectEarlier c t e then .delegate "simplifySelectInst: a step before simplifySelectWithICmpCond" else .next,
    fwd "IS.simplifySelectWithICmpCond" (simplifySelectWithICmpCond SPLimit.relational c t e),
    .delegate "simplifySelectInst: a step after simplifySelectWithICmpCond" ]

/-- What InstSimplify does with a `select`, as far as it reaches this family's folds. -/
def selectOnInst (_o : Oracle) : {w : Nat} → Term w → Result w
  | _, .select _ c t e => run (selectEntry.steps c t e)
  | _, _ => .null

/-! ### `and` and `or` -/

/-- Two compares, or two casts of one kind of compares: the operands `simplifyAndOrOfCmps` can answer for. -/
def cmpPair : Term w → Term w → Bool
  | .icmp .., .icmp .. => true
  | .zext _ _ (.icmp ..), .zext _ _ (.icmp ..) => true
  | .sext _ (.icmp ..), .sext _ (.icmp ..) => true
  | .trunc _ _ _ (.icmp ..), .trunc _ _ _ (.icmp ..) => true
  | _, _ => false

/-- `m_ICmpLike` with an equality predicate: an equality compare, or `trunc nuw X to i1`, which is `X != 0`. -/
def icmpLikeEq : {w : Nat} → Term w → Bool
  | _, .icmp _ p .. => isEquality p
  | w, .trunc _ true _ _ => w == 1
  | _, _ => false

/-- Whether a statement of `simplifyAndInst` or `simplifyOrInst` before `simplifyAndOrOfCmps` could end it, where the
operands are a pair `simplifyAndOrOfCmps` answers for: a constant operand, `X op X`, and `simplifyAndOrWithICmpEq`,
both ways round, on an equality compare. `simplifyAndCommutative`, `simplifyOrLogic`, `simplifyLogicOfAddSub` and the
shift, mask and rotate folds each need a `not`, `xor`, `and`, `or`, `add`, `sub`, shift or funnel shift operand, or an
`extractvalue`, which a compare or a cast isn't. Any other pair delegates. -/
def logicEarlier (a b : Term w) : Bool :=
  !cmpPair a b || a.isConstant || b.isConstant || specific a b || icmpLikeEq a || icmpLikeEq b

def logicEntry.steps (isAnd : Bool) (a b : Term w) : List (Step w) :=
  [ if logicEarlier a b then .delegate "simplifyAndInst/simplifyOrInst: a step before simplifyAndOrOfCmps" else .next,
    fwd "IS.simplifyAndOrOfCmps" (simplifyAndOrOfCmps URC.delegating CRQuery.llvm a b isAnd),
    .delegate "simplifyAndInst/simplifyOrInst: a step after simplifyAndOrOfCmps" ]

/-- What InstSimplify does with an `and`, as far as it reaches this family's folds. -/
def andOnInst (_o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .and _ a b => run (logicEntry.steps true a b)
  | _, _ => .null

/-- What InstSimplify does with an `or`, as far as it reaches this family's folds. -/
def orOnInst (_o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .or _ a b => run (logicEntry.steps false a b)
  | _, _ => .null

end Peephole.IS.ICmpB
