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

`Term` carries no metadata and no attributes, so `simplifyICmpInst`'s step on `!range` and `range` finds none, as the
comparison's cases, which have none, don't either. -/

namespace Peephole.IS.ICmpB

open IRLean

variable {w : Nat}

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
    fwd "IS.simplifyAndOrOfCmps" (simplifyAndOrOfCmps URC.delegating a b isAnd),
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
