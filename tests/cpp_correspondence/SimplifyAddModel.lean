/-! # A model of LLVM's `simplifyAddInst`, as the pinned C++ decides

`simplifyAddInst` in `llvm/lib/Analysis/InstructionSimplify.cpp` at `llvmorg-23.1.3` takes the two operands of an
integer `add` and its `nsw` and `nuw` flags, and returns a value the `add` can be replaced with, or `nullptr`.
InstSimplify calls it on each `add`, and InstCombine's `visitAdd` calls it first. This file restates it as a Lean
function over what its matchers can see of the operands, step by step in the same order. `SimplifyAddSound.lean`
proves each value it returns is right, for every width.

This is a manual translation, and nothing proves it matches the C++. Each step is tagged `[cpp:<id>]`, and
`anchors.json` gives the C++ text for each id, at a line of a file whose SHA-256 is pinned. `tests/cpp_correspondence.py`
checks those lines say what's recorded, that every tag here has an anchor and every anchor a tag, and compares this
function's answers with the pinned `opt -passes=instsimplify` on generated inputs. That comparison is finitely many
cases, so it's evidence, not proof. `docs/llvm-cpp-correspondence.md` has the boundary.

The model covers scalar integer operands. Vectors, constant expressions, and constants other than `ConstantInt`,
`PoisonValue` and `UndefValue` aren't representable, so nothing here is about them. Calls into code it doesn't model
come back as `Result.delegated`, which claims nothing. -/

namespace CppCorrespondence.SimplifyAdd

/-- What the matchers can see of a `Value *` of type `iw`.

`sub`, `xor` and `add` are instructions, with their operands, since the matchers look into them. `id` stands for the
instruction's address: two operands are the same `Value *` exactly when their `ident`s are equal, however their trees
look. `other` is an argument or any other instruction, which no matcher here looks into. -/
inductive Operand (w : Nat) where
  /-- A `ConstantInt`. -/
  | const (c : BitVec w)
  /-- The `PoisonValue` of type `iw`. -/
  | poison
  /-- The `UndefValue` of type `iw` that isn't poison. IRLean has no such value. -/
  | undef
  /-- A `sub` instruction, with its `nuw` and `nsw` flags. -/
  | sub (id : Nat) (nuw nsw : Bool) (a b : Operand w)
  /-- An `xor` instruction. -/
  | xor (id : Nat) (a b : Operand w)
  /-- An `add` instruction, with its `nuw` and `nsw` flags. -/
  | add (id : Nat) (nuw nsw : Bool) (a b : Operand w)
  /-- An `Argument`, or an instruction other than `sub`, `xor` and `add`. Never a `Constant`. -/
  | other (id : Nat)
  deriving DecidableEq, Repr

/-- Which `Value *` an operand is. LLVM keeps one `ConstantInt` per value and type, one `PoisonValue` and one
`UndefValue` per type, so those are the same pointer exactly when they're the same constant. -/
inductive Ident (w : Nat) where
  | const (c : BitVec w)
  | poison
  | undef
  | node (id : Nat)
  deriving DecidableEq, Repr

variable {w : Nat}

def Operand.ident : Operand w → Ident w
  | .const c => .const c
  | .poison => .poison
  | .undef => .undef
  | .sub id .. | .xor id .. | .add id .. | .other id => .node id

/-- `dyn_cast<Constant>(V)` succeeds. -/
def Operand.isConstant : Operand w → Bool
  | .const _ | .poison | .undef => true
  | _ => false

/-! ### Matchers, from `llvm/include/llvm/IR/PatternMatch.h` -/

/-- `m_Specific(S)` on `V`: the same pointer. [cpp:m_Specific] -/
def specific (s v : Operand w) : Bool := v.ident == s.ident

/-- `cst_pred_ty<P>` on a scalar: a `ConstantInt` whose value satisfies `P`. Poison and undef aren't `ConstantInt`s.
[cpp:cstval_pred_ty] -/
def cstPred (p : BitVec w → Bool) : Operand w → Bool
  | .const c => p c
  | _ => false

/-- `m_Zero()`: a null constant, or a `ConstantInt` zero, which for a scalar integer are the same. [cpp:m_Zero] -/
def zero : Operand w → Bool := cstPred (· == 0#w)

/-- `m_ZeroInt()`. [cpp:m_ZeroInt] -/
def zeroInt : Operand w → Bool := cstPred (· == 0#w)

/-- `m_AllOnes()`. [cpp:m_AllOnes] -/
def allOnes : Operand w → Bool := cstPred (· == BitVec.allOnes w)

/-- `m_SignMask()`: `APInt::isSignMask`, only the sign bit set. [cpp:m_SignMask] -/
def signMask : Operand w → Bool := cstPred (· == BitVec.intMin w)

/-- `m_Undef()`, through `SimplifyQuery::isUndefValue` with `CanUseUndef` true, as InstSimplify's query has it. It
matches poison too. [cpp:isUndefValue] [cpp:m_Undef] [cpp:CanUseUndef] -/
def isUndefValue : Operand w → Bool
  | .undef | .poison => true
  | _ => false

/-- `m_Sub(m_Value(Y), m_Specific(S))` on `V`, binding `Y`. `BinaryOp_match` matches only an instruction, operand 0
then operand 1, in that order only. [cpp:BinaryOp_match] [cpp:m_Sub] -/
def subSpecific (s v : Operand w) : Option (Operand w) :=
  match v with
  | .sub _ _ _ y b => if specific s b then some y else none
  | _ => none

/-- `m_Not(m_Specific(S))` on `V`, which is `m_c_Xor(m_AllOnes(), m_Specific(S))`: an `xor` of `S` and all ones, in
either order. [cpp:m_Not] [cpp:m_c_Xor] -/
def notSpecific (s v : Operand w) : Bool :=
  match v with
  | .xor _ a b => (allOnes a && specific s b) || (allOnes b && specific s a)
  | _ => false

/-- `m_Xor(m_Value(Y), m_SignMask())` on `V`, binding `Y`. Not commutative: the sign mask has to be operand 1.
[cpp:m_Xor] -/
def xorSignMask (v : Operand w) : Option (Operand w) :=
  match v with
  | .xor _ y b => if signMask b then some y else none
  | _ => none

/-- `isKnownNegation(X, Y)` from `llvm/lib/Analysis/ValueTracking.cpp`, with its defaults `NeedNSW = false` and
`AllowPoison = true`, as `simplifyAddInst` calls it. [cpp:isKnownNegation] [cpp:isKnownNegation.defaults] -/
def isKnownNegation (x y : Operand w) : Bool :=
  negationOf x y || negationOf y x || subSwapped x y
where
  /-- `match(X, m_Neg(m_Specific(Y)))`, where `m_Neg(V)` is `m_Sub(m_ZeroInt(), V)`. With `NeedNSW` false and
  `AllowPoison` true, the lambda's other two checks always pass. [cpp:isKnownNegation.negationOf] [cpp:m_Neg] -/
  negationOf (x y : Operand w) : Bool :=
    match x with
    | .sub _ _ _ z v => zeroInt z && specific y v
    | _ => false
  /-- `match(X, m_Sub(m_Value(A), m_Value(B))) && match(Y, m_Sub(m_Specific(B), m_Specific(A)))`, flags ignored.
  [cpp:isKnownNegation.subSwapped] -/
  subSwapped (x y : Operand w) : Bool :=
    match x, y with
    | .sub _ _ _ a b, .sub _ _ _ b' a' => specific b b' && specific a a'
    | _, _ => false

/-! ### The function -/

/-- Code `simplifyAddInst` calls that this model doesn't follow. -/
inductive Callee where
  /-- `ConstantFoldBinaryOpOperands`, when both operands are constants. -/
  | constantFold
  /-- `simplifyXorInst`, for `i1`. -/
  | simplifyXorInst
  /-- `simplifyAssociativeBinOp`, when an operand is an `add`, so it could recurse. -/
  | simplifyAssociativeBinOp
  deriving DecidableEq, Repr

/-- What `simplifyAddInst` returns. -/
inductive Result (w : Nat) where
  /-- This `Value *`. -/
  | value (v : Operand w)
  /-- `nullptr`: no simplification. -/
  | null
  /-- Whatever this callee returns, which the model doesn't say. -/
  | delegated (c : Callee)
  deriving DecidableEq, Repr

/-- `simplifyAddInst` once `foldOrCommuteConstant` has put a lone constant on the right. Each step returns as the C++
does, in its order. -/
def afterFold (op0 op1 : Operand w) (isNSW isNUW : Bool) (maxRecurse : Nat) : Result w :=
  -- X + poison -> poison [cpp:add.poison]
  if op1 == .poison then .value op1
  -- X + undef -> undef [cpp:add.undef]
  else if isUndefValue op1 then .value op1
  -- X + 0 -> X [cpp:add.zero]
  else if zero op1 then .value op0
  -- If two operands are negative, return 0. [cpp:add.negation]
  else if isKnownNegation op0 op1 then .value (.const 0#w)
  -- X + (Y - X) -> Y, (Y - X) + X -> Y [cpp:add.subCancel]
  else match subSpecific op0 op1 with
  | some y => .value y
  | none =>
  match subSpecific op1 op0 with
  | some y => .value y
  | none =>
  -- X + ~X -> -1 [cpp:add.not]
  if notSpecific op1 op0 || notSpecific op0 op1 then .value (.const (BitVec.allOnes w))
  -- add nsw/nuw (xor Y, signmask), signmask --> Y [cpp:add.signMask]
  else match (isNSW || isNUW) && signMask op1, xorSignMask op0 with
  | true, some y => .value y
  | _, _ =>
  -- add nuw %x, -1  ->  -1 [cpp:add.nuwAllOnes]
  if isNUW && allOnes op1 then .value op1
  -- i1 add -> xor [cpp:add.i1]
  else if maxRecurse != 0 && w == 1 then .delegated .simplifyXorInst
  -- simplifyAssociativeBinOp: `if (!MaxRecurse--) return nullptr;` [cpp:add.assoc] [cpp:assoc.limit]
  else if maxRecurse == 0 then .null
  -- Every transform it tries needs an operand that's a `BinaryOperator` with opcode `Add`. [cpp:assoc.guards]
  else match op0, op1 with
  | .add .., _ | _, .add .. => .delegated .simplifyAssociativeBinOp
  -- Threading over selects and phis is skipped. [cpp:add.null]
  | _, _ => .null

/-- `simplifyAddInst(Op0, Op1, IsNSW, IsNUW, Q, MaxRecurse)`. InstSimplify calls `simplifyInstruction` on each
`add` that has a use, and replaces its uses with any value it returns [cpp:instsimplify.loop]. That reaches this with
`MaxRecurse` at `RecursionLimit`, 3 [cpp:dispatch] [cpp:RecursionLimit], and the instruction's own flags, since
InstSimplify's query reads them [cpp:IIQ.flags] [cpp:instsimplify.query]. [cpp:add.entry] -/
def simplifyAddInst (op0 op1 : Operand w) (isNSW isNUW : Bool) (maxRecurse : Nat) : Result w :=
  -- foldOrCommuteConstant: two constants fold, and a lone constant on the left swaps to the right, since `add`
  -- commutes. [cpp:add.fold] [cpp:fold.both] [cpp:fold.swap]
  if op0.isConstant then
    if op1.isConstant then .delegated .constantFold
    else afterFold op1 op0 isNSW isNUW maxRecurse
  else afterFold op0 op1 isNSW isNUW maxRecurse

end CppCorrespondence.SimplifyAdd
