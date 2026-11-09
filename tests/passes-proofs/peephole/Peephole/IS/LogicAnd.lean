import Peephole.IS.Logic
import IRLean.Generic.Bitwise

/-! # InstSimplify's `simplifyAndInst` and `simplifyAndCommutative`, and their rewrites for every input

`simplifyAndCommutative` and `simplifyAndInst` are at `llvm/lib/Analysis/InstructionSimplify.cpp:2019-2248` at
`llvmorg-23.1.3`. This is their model on `Peephole.Term`, step by step in the C++'s order. Each step that rewrites
carries its ID from `tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyAndCommutative.L2024` | `~A & A` to 0 |
| `IS.simplifyAndCommutative.L2028` | `(A \| ?) & A` to `A` |
| `IS.simplifyAndCommutative.L2034` | `(X \| ~Y) & (X \| Y)` to `X` |
| `IS.simplifyAndCommutative.L2045` | `-A & A` to `A` where `A` is a power of two or 0 |
| `IS.simplifyAndCommutative.L2051` | `(A - 1) & A` to 0 where `A` is a power of two or 0 |
| `IS.simplifyAndCommutative.L2060` | `(X << N) & ((X << M) - 1)` to 0 where `X` is a power of two or 0 and `M ≤ N` |
| `IS.simplifyAndInst.L2078` | `X & poison` to poison |
| `IS.simplifyAndInst.L2082` | `X & undef` to 0. IRLean has no `undef`, so this is about poison only |
| `IS.simplifyAndInst.L2086` | `X & X` to `X` |
| `IS.simplifyAndInst.L2090` | `X & 0` to 0 |
| `IS.simplifyAndInst.L2094` | `X & -1` to `X` |
| `IS.simplifyAndInst.L2113` | `(shl X, C) & Mask` to the `shl` where `Mask` keeps every bit it can set |
| `IS.simplifyAndInst.L2119` | `(lshr X, C) & Mask` to the `lshr` where `Mask` keeps every bit it can set |
| `IS.simplifyAndInst.L2132` | `(2^x - 1) & 2^C` to 0 where `x ≤ C`, from known bits |
| `IS.simplifyAndInst.L2157` | `A & (A && B)` to `A && B`, on `i1` |
| `IS.simplifyAndInst.L2159` | `(A && B) & A` to `A && B`, on `i1` |
| `IS.simplifyAndInst.L2203` | `((X << A) \| Y) & Mask` to `Y`, from known bits |
| `IS.simplifyAndInst.L2205` | `((X << A) \| Y) & Mask` to `X << A`, from known bits |
| `IS.simplifyAndInst.L2216` | `((X \| Y) ^ X) & ((X \| Y) ^ Y)` to 0 |
| `IS.simplifyAndInst.L2223` | `(A ^ C) & (A ^ ~C)` to 0 |
| `IS.simplifyAndInst.L2229` | `A & B` to `A` on `i1`, where `A` implies `B` |
| `IS.simplifyAndInst.L2232` | `A & B` to false on `i1`, where `A` implies `!B` |
| `IS.simplifyAndInst.L2237` | `A & B` to `B` on `i1`, where `B` implies `A` |
| `IS.simplifyAndInst.L2240` | `A & B` to false on `i1`, where `B` implies `!A` |

`IS.simplifyAndCommutative.L2040` isn't proved: the overflow bit of `umul.with.overflow`, an `extractvalue`, isn't a
`Term`, so the model hands over to `isCheckForZeroAndMulWithOverflow` wherever `Op1` could be one.

`simplifyAndInst.sound` puts them together with the folds it calls: every value the model returns refines the `and`, at
every width and recursion budget, poison included, in every run where the `Oracle`'s answers, and the `Logic.Ext`'s if
given, are sound. -/

namespace Peephole.IS

open IRLean Logic

variable {w : Nat}

namespace Logic

/-! ### Helpers `simplifyAndInst` calls -/

/-- `isa<ICmpInst>`. -/
def isICmp : {w : Nat} → Term w → Bool
  | _, .icmp .. => true
  | _, _ => false

/-- Whether `simplifyAndOrOfCmps(Q, Op0, Op1, IsAnd)` could answer: both operands are `icmp`s, after looking through
casts of one opcode from one type on both. It isn't modelled, so this only says when the model hands over to it. -/
def isCmpPair : Term w → Term w → Bool
  | .zext (v := v0) _ _ a, .zext (v := v1) _ _ b => v0 == v1 && isICmp a && isICmp b
  | .sext (v := v0) _ a, .sext (v := v1) _ b => v0 == v1 && isICmp a && isICmp b
  | .trunc (v := v0) _ _ _ a, .trunc (v := v1) _ _ _ b => v0 == v1 && isICmp a && isICmp b
  | a, b => isICmp a && isICmp b

/-- An instruction no matcher here looks into: it could be a `phi`, or the `extractvalue` of an overflow bit. -/
def isOpaque : Term w → Bool
  | .var _ => true
  | _ => false

/-- `isa<SelectInst>`. -/
def isSelect : Term w → Bool
  | .select .. => true
  | _ => false

/-- `m_ICmp(Pred, m_Value(X), m_Zero())`: the predicate. -/
def icmpZeroPred : {w : Nat} → Term w → Option Pred
  | _, .icmp _ p _ _ b => if zero b then some p else none
  | _, _ => none

/-- Whether `isCheckForZeroAndMulWithOverflow(Op0, Op1, IsAnd)`, in `llvm/lib/Analysis/OverflowInstAnalysis.cpp`,
could hold: `Op0` is `icmp ne X, 0` for `and`, or `icmp eq X, 0` for `or`, and `Op1` for `and`, or what `Op1` negates
for `or`, could be the overflow bit of `umul.with.overflow` or `smul.with.overflow`, an `extractvalue`, which only
an opaque operand can be. It isn't modelled, so this only says when the model hands over to it. -/
def mulOverflowCheck (x : Option Ext) (isAnd : Bool) (op0 op1 : Term w) : Bool :=
  if isAnd then icmpZeroPred op0 == some .ne && overflowBit op1
  else icmpZeroPred op0 == some .eq && (match not? op1 with | some v => overflowBit v | none => false)
where
  /-- Whether an operand could be the overflow bit: one the model doesn't look into, which `Ext` says is one. -/
  overflowBit (v : Term w) : Bool :=
    isOpaque v && match x with
      | none => true
      | some e => e.isMulOverflowBit v

/-- Whether `simplifyAssociativeBinOp(Opcode, LHS, RHS, Q, MaxRecurse)`, for a commutative `Opcode`, could answer: it
answers `nullptr` at `MaxRecurse == 0`, and unless the first `simplifyBinOp` of one of its four transforms answers.
With no `Ext`, wherever an operand has the opcode. -/
def assocMayAnswer (x : Option Ext) (opc : BinOp) (lhs rhs : Term w) (n : Nat) : Bool :=
  n != 0 && match x with
    | none => isBin opc lhs || isBin opc rhs
    | some e =>
      -- "(A op B) op C" ==> "A op (B op C)", then "(A op B) op C" ==> "(C op A) op B"
      (match binop? opc lhs with
        | some (_, a, b) => e.simplifies (n - 1) opc false b rhs || e.simplifies (n - 1) opc false rhs a
        | none => false) ||
      -- "A op (B op C)" ==> "(A op B) op C", then "A op (B op C)" ==> "B op (C op A)"
      (match binop? opc rhs with
        | some (_, b, c) => e.simplifies (n - 1) opc false lhs b || e.simplifies (n - 1) opc false c lhs
        | none => false)

/-- Whether `expandCommutativeBinOp(Opcode, L, R, OpcodeToExpand, Q, MaxRecurse)` could answer: it answers `nullptr` at
`MaxRecurse == 0`, and unless, for `L` or `R` an `OpcodeToExpand` of `B0` and `B1`, `simplifyBinOp(Opcode, B0, other,
Q.getWithoutUndef(), ...)` answers. With no `Ext`, wherever an operand has `OpcodeToExpand`. -/
def expandMayAnswer (x : Option Ext) (opc opEx : BinOp) (l r : Term w) (n : Nat) : Bool :=
  n != 0 && match x with
    | none => isBin opEx l || isBin opEx r
    | some e =>
      (match binop? opEx l with
        | some (_, b0, _) => e.simplifies (n - 1) opc true b0 r
        | none => false) ||
      (match binop? opEx r with
        | some (_, b0, _) => e.simplifies (n - 1) opc true b0 l
        | none => false)

/-- Whether `threadBinOpOverSelect(Opcode, LHS, RHS, Q, MaxRecurse)` could answer: it answers `nullptr` at
`MaxRecurse == 0`, and where the operation on neither of the select's values simplifies. With no `Ext`, wherever it's
called. -/
def selectMayAnswer (x : Option Ext) (opc : BinOp) (lhs rhs : Term w) (n : Nat) : Bool :=
  n != 0 && match x with
    | none => true
    | some e =>
      match lhs with
      | .select _ _ t f => e.simplifies (n - 1) opc false t rhs || e.simplifies (n - 1) opc false f rhs
      | _ =>
        match rhs with
        | .select _ _ t f => e.simplifies (n - 1) opc false lhs t || e.simplifies (n - 1) opc false lhs f
        | _ => false

/-- Whether `threadBinOpOverPHI(Opcode, LHS, RHS, Q, MaxRecurse)` is called and could answer: an operand is a `phi`,
which only an operand the model doesn't look into can be, and `MaxRecurse` isn't 0. With no `Ext`, wherever an operand
is one the model doesn't look into. -/
def phiMayAnswer (x : Option Ext) (lhs rhs : Term w) (n : Nat) : Bool :=
  n != 0 && match x with
    | none => isOpaque lhs || isOpaque rhs
    | some e => (isOpaque lhs && e.isPhi lhs) || (isOpaque rhs && e.isPhi rhs)

/-- `m_<Shift>(m_Value(X), m_APInt(C))`: `X` and `C`. -/
def shiftConst? (op : BinOp) (t : Term w) : Option (Term w × BitVec w) :=
  match binop? op t with
  | some (_, x, s) => (apint s).map fun c => (x, c)
  | none => none

/-- `m_Add(m_Value(X), m_AllOnes())`: `X`. -/
def addAllOnes? (t : Term w) : Option (Term w) :=
  match binop? .add t with
  | some (_, x, m) => if allOnes m then some x else none
  | none => none

/-- `m_Select(m_Specific(A), m_Value(), m_Zero())` on `T`, for `and`, or `m_Select(m_Specific(A), m_One(),
m_Value())`, for `or`. The condition is `i1`, and `A` is compared by address. -/
def selectOf (isAnd : Bool) (a t : Term w) : Bool :=
  match t with
  | .select _ c tv fv => c.ident == a.ident && (if isAnd then zero fv else one tv)
  | _ => false

/-- `APInt::getActiveBits`: the bits up to the highest set one, `BitWidth - countl_zero()`. -/
def activeBits (x : BitVec w) : Nat := if x.toNat = 0 then 0 else x.toNat.log2 + 1

/-- `APInt::countl_one`: how many of the top bits are set, from bit `w - 1` down. -/
def countlOne (z : BitVec w) : Nat := go w
where
  /-- How many bits are set from bit `k - 1` down. -/
  go : Nat → Nat
    | 0 => 0
    | k + 1 => if z.getLsbD k then go k + 1 else 0

/-- `KnownBits::countMaxActiveBits` of known bits whose `Zero` is `z`: `BitWidth - Zero.countl_one()`. -/
def countMaxActiveBits (z : BitVec w) : Nat := w - countlOne z

/-- `APInt::getLowBitsSet(w, n)`: the low `n` bits set, for `n ≤ w`. -/
def lowBitsSet (w n : Nat) : BitVec w := BitVec.allOnes w >>> (w - n)

/-- `m_c_Or(m_CombineAnd(m_NUWShl(m_Value(X), m_APInt(ShAmt)), m_Value(XShifted)), m_Value(Y))`: `X`, `ShAmt`,
`XShifted` and `Y`. -/
def orNUWShl? (t : Term w) : Option ((Term w × BitVec w × Term w) × Term w) :=
  cbind .or (fun u => match binop? .shl u with
      | some (f, x, s) => if f.nuw then (apint s).map fun c => (x, c, u) else none
      | none => none) some t

/-- `EffBitsY` in `simplifyAndInst`: the bits `Y` may have set, `APInt::getLowBitsSet(Width, EffWidthY)`. -/
def effBitsY (o : Oracle) (Y : Term w) : BitVec w := lowBitsSet w (countMaxActiveBits (o.knownZero Y))

/-- `EffBitsX` in `simplifyAndInst`: the bits `X << ShAmt` may have set,
`APInt::getLowBitsSet(Width, EffWidthX) << ShftCnt`, where `ShftCnt` is `ShAmt->getLimitedValue(Width)`. -/
def effBitsX (o : Oracle) (X : Term w) (shAmt : BitVec w) : BitVec w :=
  lowBitsSet w (countMaxActiveBits (o.knownZero X)) <<< min shAmt.toNat w

/-- `m_c_Xor(m_Value(X), m_CombineAnd(m_BinOp(Or), m_c_Or(m_Deferred(X), m_Value(Y))))`: `X`, `Or` and `Y`. -/
def xorOrDeferred? (t : Term w) : Option (Term w × Term w × Term w) :=
  match binop? .xor t with
  | some (_, a, b) =>
    match orWith a b with
    | some y => some (a, b, y)
    | none =>
      match orWith b a with
      | some y => some (b, a, y)
      | none => none
  | none => none
where
  /-- `m_c_Or(m_Deferred(X), m_Value(Y))` on `O`: `Y`. -/
  orWith (x o : Term w) : Option (Term w) :=
    match binop? .or o with
    | some (_, p, q) => if specific x p then some q else if specific x q then some p else none
    | none => none

/-- `m_Xor(m_Value(A), m_APInt(C))`: `A` and `C`. -/
def xorConst? (t : Term w) : Option (Term w × BitVec w) := shiftConst? .xor t

/-- Reads an operand of an `i1` operation as `i1`. -/
def asI1 (h : w = 1) (t : Term w) : Term 1 := h ▸ t

/-- `simplifyByDomEq(Opcode, Op0, Op1, Q, MaxRecurse)`: it answers only at the top of the recursion, and only where
`isImpliedByDomCondition` says `Op0 == Op1`. It isn't modelled, so the model hands over to it there, and wherever no
`Ext` answers that. -/
def domEqStep (x : Option Ext) (op0 op1 : Term w) (n : Nat) : Step w :=
  if n == 3 then
    match x with
    | none => .delegate "simplifyByDomEq"
    | some e => if e.domEq op0 op1 == some true then .delegate "simplifyByDomEq" else .next
  else .next

end Logic

/-! ## `simplifyAndCommutative` -/

/-- `simplifyAndCommutative(Op0, Op1, Q, MaxRecurse)`, step by step. -/
def simplifyAndCommutative.steps (o : Oracle) (x : Option Ext) (op0 op1 : Term w) (n : Nat) : List (Step w) :=
  [ -- ~A & A =  0
    if notWith (specific op1) op0 then .fire "IS.simplifyAndCommutative.L2024" (.const 0#w) else .next,
    -- (A | ?) & A = A
    if chas .or (specific op1) (fun _ => true) op0 then .fire "IS.simplifyAndCommutative.L2028" (.old op1)
    else .next,
    -- (X | ~Y) & (X | Y) --> X
    match cbind .or some not? op0 with
    | some (X, Y) => if isOf .or X Y op1 then .fire "IS.simplifyAndCommutative.L2034" (.old X) else .next
    | none => .next,
    -- If we have a multiplication overflow check that is being 'and'ed with a
    -- check that one of the multipliers is not zero, we can omit the 'and', and
    -- only keep the overflow check.
    if mulOverflowCheck x true op0 op1 then .delegate "isCheckForZeroAndMulWithOverflow" else .next,
    -- -A & A = A if A is a power of two or zero.
    match neg? op0 with
    | some v =>
      if specific op1 v && o.powerOfTwo true op1 then .fire "IS.simplifyAndCommutative.L2045" (.old op1) else .next
    | none => .next,
    -- This is a similar pattern used for checking if a value is a power-of-2:
    -- (A - 1) & A --> 0 (if A is a power-of-2 or 0)
    match addAllOnes? op0 with
    | some a =>
      if specific op1 a && o.powerOfTwo true op1 then .fire "IS.simplifyAndCommutative.L2051" (.const 0#w)
      else .next
    | none => .next,
    -- (x << N) & ((x << M) - 1) --> 0, where x is known to be a power of 2 and
    -- M <= N.
    match shiftConst? .shl op0, addAllOnes? op1 with
    | some (X, shift1), some sh =>
      match shiftConst? .shl sh with
      | some (X', shift2) =>
        if specific X X' && o.powerOfTwo true X && shift2.toNat ≤ shift1.toNat then
          .fire "IS.simplifyAndCommutative.L2060" (.const 0#w)
        else .next
      | none => .next
    | _, _ => .next,
    forward (simplifyAndOrWithICmpEq.steps x true op0 op1 n) ]

/-! ## `simplifyAndInst` -/

/-- `simplifyAndInst` once `foldOrCommuteConstant` has put a lone constant on the right, step by step. `Q.IIQ
.UseInstrInfo` is true, as InstSimplify has it. -/
def simplifyAndInst.steps (o : Oracle) (x : Option Ext) (op0 op1 : Term w) (n : Nat) : List (Step w) :=
  [ -- X & poison -> poison
    if isPoison op1 then .fire "IS.simplifyAndInst.L2078" (.old op1) else .next,
    -- X & undef -> 0
    if isUndefValue op1 then .fire "IS.simplifyAndInst.L2082" (.const 0#w) else .next,
    -- X & X = X
    if specific op0 op1 then .fire "IS.simplifyAndInst.L2086" (.old op0) else .next,
    -- X & 0 = 0
    if zero op1 then .fire "IS.simplifyAndInst.L2090" (.const 0#w) else .next,
    -- X & -1 = X
    if allOnes op1 then .fire "IS.simplifyAndInst.L2094" (.old op0) else .next,
    forward (simplifyAndCommutative.steps o x op0 op1 n),
    forward (simplifyAndCommutative.steps o x op1 op0 n),
    forward (simplifyLogicOfAddSub.steps op0 op1 .and),
    -- A mask that only clears known zeros of a shifted value is a no-op.
    -- If all bits in the inverted and shifted mask are clear:
    -- and (shl X, ShAmt), Mask --> shl X, ShAmt
    match apint op1, shiftConst? .shl op0 with
    | some mask, some (_, shAmt) =>
      if ~~~mask >>> shAmt.toNat == 0#w then .fire "IS.simplifyAndInst.L2113" (.old op0) else .next
    | _, _ => .next,
    -- If all bits in the inverted and shifted mask are clear:
    -- and (lshr X, ShAmt), Mask --> lshr X, ShAmt
    match apint op1, shiftConst? .lshr op0 with
    | some mask, some (_, shAmt) =>
      if ~~~mask <<< shAmt.toNat == 0#w then .fire "IS.simplifyAndInst.L2119" (.old op0) else .next
    | _, _ => .next,
    -- and 2^x-1, 2^C --> 0 where x <= C.
    -- Use getActiveBits() to make use of the additional power of two knowledge
    match apint op1, addAllOnes? op0 with
    | some powerC, some shift =>
      if powerC.toNat.isPowerOfTwo && o.powerOfTwo false shift &&
          activeBits (~~~(o.knownZero shift)) ≤ activeBits powerC then
        .fire "IS.simplifyAndInst.L2132" (.const 0#w)
      else .next
    | _, _ => .next,
    if isCmpPair op0 op1 then .delegate "simplifyAndOrOfCmps" else .next,
    -- Try some generic simplifications for associative operations.
    if assocMayAnswer x .and op0 op1 n then .delegate "simplifyAssociativeBinOp" else .next,
    -- And distributes over Or.  Try some generic simplifications based on this.
    if expandMayAnswer x .and .or op0 op1 n then .delegate "expandCommutativeBinOp" else .next,
    -- And distributes over Xor.  Try some generic simplifications based on this.
    if expandMayAnswer x .and .xor op0 op1 n then .delegate "expandCommutativeBinOp" else .next,
    -- A & (A && B) -> A && B
    if (isSelect op0 || isSelect op1) && w == 1 && selectOf true op0 op1 then
      .fire "IS.simplifyAndInst.L2157" (.old op1)
    else .next,
    if (isSelect op0 || isSelect op1) && w == 1 && selectOf true op1 op0 then
      .fire "IS.simplifyAndInst.L2159" (.old op0)
    else .next,
    -- If the operation is with the result of a select instruction, check
    -- whether operating on either branch of the select always yields the same
    -- value.
    if (isSelect op0 || isSelect op1) && selectMayAnswer x .and op0 op1 n then .delegate "threadBinOpOverSelect"
    else .next,
    -- If the operation is with the result of a phi instruction, check whether
    -- operating on all incoming values of the phi always yields the same value.
    if phiMayAnswer x op0 op1 n then .delegate "threadBinOpOverPHI" else .next,
    -- ((X << A) | Y) & Mask -> Y,
    --     if Mask = ((1 << effective_width_of(Y)) - 1)
    -- ((X << A) | Y) & Mask -> X << A,
    --     if Mask = ((1 << effective_width_of(X)) - 1) << A
    -- If the mask is extracting all bits from X or Y as is, we can skip
    -- this AND op. (`EffWidthY <= ShftCnt`, then `EffBitsY.isSubsetOf(*Mask) && !EffBitsX.intersects(*Mask)`.)
    match apint op1, orNUWShl? op0 with
    | some mask, some ((X, shAmt, _), Y) =>
      if countMaxActiveBits (o.knownZero Y) ≤ min shAmt.toNat w && effBitsY o Y &&& ~~~mask == 0#w &&
          effBitsX o X shAmt &&& mask == 0#w then
        .fire "IS.simplifyAndInst.L2203" (.old Y)
      else .next
    | _, _ => .next,
    match apint op1, orNUWShl? op0 with
    | some mask, some ((X, shAmt, XShifted), Y) =>
      if countMaxActiveBits (o.knownZero Y) ≤ min shAmt.toNat w && effBitsX o X shAmt &&& ~~~mask == 0#w &&
          effBitsY o Y &&& mask == 0#w then
        .fire "IS.simplifyAndInst.L2205" (.old XShifted)
      else .next
    | _, _ => .next,
    -- ((X | Y) ^ X ) & ((X | Y) ^ Y) --> 0
    -- ((X | Y) ^ Y ) & ((X | Y) ^ X) --> 0
    match xorOrDeferred? op0 with
    | some (_, Or, Y) => if isOf .xor Or Y op1 then .fire "IS.simplifyAndInst.L2216" (.const 0#w) else .next
    | none => .next,
    -- (A ^ C) & (A ^ ~C) -> 0
    match xorConst? op0, xorConst? op1 with
    | some (A, c1), some (A', c2) =>
      if specific A A' && c2 == ~~~c1 then .fire "IS.simplifyAndInst.L2223" (.const 0#w) else .next
    | _, _ => .next,
    -- If Op0 is true implies Op1 is true, then Op0 is a subset of Op1.
    if h : w = 1 then
      if o.implies (asI1 h op0) (asI1 h op1) == some true then .fire "IS.simplifyAndInst.L2229" (.old op0) else .next
    else .next,
    -- If Op0 is true implies Op1 is false, then they are not true together.
    if h : w = 1 then
      if o.implies (asI1 h op0) (asI1 h op1) == some false then .fire "IS.simplifyAndInst.L2232" (.const 0#w)
      else .next
    else .next,
    -- If Op1 is true implies Op0 is true, then Op1 is a subset of Op0.
    if h : w = 1 then
      if o.implies (asI1 h op1) (asI1 h op0) == some true then .fire "IS.simplifyAndInst.L2237" (.old op1) else .next
    else .next,
    -- If Op1 is true implies Op0 is false, then they are not true together.
    if h : w = 1 then
      if o.implies (asI1 h op1) (asI1 h op0) == some false then .fire "IS.simplifyAndInst.L2240" (.const 0#w)
      else .next
    else .next,
    domEqStep x op0 op1 n ]

/-- `simplifyAndInst(Op0, Op1, Q, MaxRecurse)`. `foldOrCommuteConstant` folds two constants, which the constant folder
does, at `IS.foldOrCommuteConstant.L582`, and swaps a lone constant to the right. -/
def simplifyAndInst (o : Oracle) (x : Option Ext) (op0 op1 : Term w) (n : Nat) : Result w :=
  if op0.isConstant then
    if op1.isConstant then .delegated "ConstantFoldBinaryOpOperands"
    else run (simplifyAndInst.steps o x op1 op0 n)
  else run (simplifyAndInst.steps o x op0 op1 n)

/-- What InstSimplify does with an instruction it reaches: `simplifyInstruction` calls `simplifyAndInst` on an `and`,
with `MaxRecurse` at `RecursionLimit`, 3. What the core `Oracle` doesn't answer, `Logic.Ext.none` answers: nothing. -/
def simplifyAndInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .and _ a b => simplifyAndInst o (some Ext.none) a b 3
  | _, _ => .null

/-! ### What the helpers' matches say about values -/

namespace Logic

variable {ρ : Env}

theorem shiftConst?_shl {t x : Term w} {c : BitVec w} (h : shiftConst? .shl t = some (x, c)) (hc : t.Consistent ρ) :
    x.Consistent ρ ∧ ∃ nuw nsw, t.denote ρ = Val.shl (x.denote ρ) (some c) nuw nsw := by
  unfold shiftConst? at h
  split at h
  · next f x' s hb =>
    obtain ⟨h1, h2, hd⟩ := shl_denote hb hc
    cases hs : apint s <;> simp only [hs, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h1, _, _, by rw [hd, apint_denote hs]⟩
  · cases h

theorem shiftConst?_lshr {t x : Term w} {c : BitVec w} (h : shiftConst? .lshr t = some (x, c))
    (hc : t.Consistent ρ) : x.Consistent ρ ∧ ∃ e, t.denote ρ = Val.lshr (x.denote ρ) (some c) e := by
  unfold shiftConst? at h
  split at h
  · next f x' s hb =>
    obtain ⟨h1, h2, hd⟩ := lshr_denote hb hc
    cases hs : apint s <;> simp only [hs, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h1, _, by rw [hd, apint_denote hs]⟩
  · cases h

theorem xorConst?_denote {t x : Term w} {c : BitVec w} (h : xorConst? t = some (x, c)) (hc : t.Consistent ρ) :
    t.denote ρ = Val.xor (x.denote ρ) (some c) := by
  unfold xorConst? shiftConst? at h
  split at h
  · next f x' s hb =>
    obtain ⟨h1, h2, hd⟩ := xor_denote' hb hc
    cases hs : apint s <;> simp only [hs, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [hd, apint_denote hs]
  · cases h

theorem addAllOnes?_denote {t x : Term w} (h : addAllOnes? t = some x) (hc : t.Consistent ρ) :
    x.Consistent ρ ∧ ∃ nuw nsw, t.denote ρ = Val.add (x.denote ρ) (some (BitVec.allOnes w)) nuw nsw := by
  unfold addAllOnes? at h
  split at h
  · next f x' m hb =>
    obtain ⟨h1, h2, hd⟩ := add_denote hb hc
    split at h
    · next hm => cases h; exact ⟨h1, _, _, by rw [hd, cst_eq hm]⟩
    · cases h
  · cases h

theorem neg?_denote {t v : Term w} (h : neg? t = some v) (hc : t.Consistent ρ) :
    ∃ nuw nsw, t.denote ρ = Val.sub (some 0#w) (v.denote ρ) nuw nsw := by
  unfold neg? at h
  split at h
  · next f z v' hb =>
    obtain ⟨-, -, hd⟩ := sub_denote' hb hc
    split at h
    · next hz => cases h; exact ⟨_, _, by rw [hd, cst_eq hz]⟩
    · cases h
  · cases h

/-- `m_Select(m_Specific(A), m_Value(), m_Zero())` on an `i1` `T`: `T` is `select A, t, false`. -/
theorem selectOf_and {a t : Term 1} (h : selectOf true a t = true) (hc : t.Consistent ρ) :
    ∃ tv : Term 1, t.denote ρ = select (a.denote ρ) (tv.denote ρ) (some 0#1) := by
  cases t with
  | select id c tv fv =>
    simp only [selectOf, ite_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨-, -, -, hd⟩ := hc
    exact ⟨tv, by rw [Term.denote, ← hd, Term.denote_of_ident h.1, cst_eq h.2]⟩
  | _ => simp [selectOf] at h

/-- `m_Select(m_Specific(A), m_One(), m_Value())` on an `i1` `T`: `T` is `select A, true, f`. -/
theorem selectOf_or {a t : Term 1} (h : selectOf false a t = true) (hc : t.Consistent ρ) :
    ∃ fv : Term 1, t.denote ρ = select (a.denote ρ) (some 1#1) (fv.denote ρ) := by
  cases t with
  | select id c tv fv =>
    simp only [selectOf, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨-, -, -, hd⟩ := hc
    exact ⟨fv, by rw [Term.denote, ← hd, Term.denote_of_ident h.1, cst_eq h.2]⟩
  | _ => simp [selectOf] at h

/-! ### Known bits: what `countMaxActiveBits` and `getActiveBits` say -/

theorem countlOne_go_spec (z : BitVec w) : ∀ k i, k - countlOne.go z k ≤ i → i < k → z.getLsbD i = true := by
  intro k
  induction k with
  | zero => intro i _ h; omega
  | succ k ih =>
    intro i h1 h2
    simp only [countlOne.go] at h1
    split at h1
    · next hk =>
      by_cases hik : i = k
      · subst hik; exact hk
      · exact ih i (by omega) (by omega)
    · omega

/-- Above a value's maximum active bits, from known zeros, every bit is clear. -/
theorem getLsbD_of_knownZero {x z : BitVec w} (hz : x &&& z = 0#w) {i : Nat} (hi : countMaxActiveBits z ≤ i) :
    x.getLsbD i = false := by
  by_cases hiw : i < w
  · have hzi : z.getLsbD i = true :=
      countlOne_go_spec z w i (by unfold countMaxActiveBits countlOne at hi; omega) hiw
    have := congrArg (BitVec.getLsbD · i) hz
    simpa [BitVec.getLsbD_and, hzi] using this
  · exact BitVec.getLsbD_of_ge x i (by omega)

theorem countMaxActiveBits_le (z : BitVec w) : countMaxActiveBits z ≤ w := by
  unfold countMaxActiveBits; omega

theorem getLsbD_lowBitsSet {n i : Nat} (hn : n ≤ w) : (lowBitsSet w n).getLsbD i = decide (i < n) := by
  simp only [lowBitsSet, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
  by_cases h : i < n
  · simp [h]; omega
  · simp [h]; omega

theorem and_eq_self_of_knownZero {v z mask : BitVec w} (hz : v &&& z = 0#w)
    (hm : lowBitsSet w (countMaxActiveBits z) &&& ~~~mask = 0#w) : v &&& mask = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  cases hv : v.getLsbD i
  · simp
  · have hlt : i < countMaxActiveBits z := by
      refine Nat.lt_of_not_le fun hge => ?_
      rw [getLsbD_of_knownZero hz hge] at hv; cases hv
    have := congrArg (BitVec.getLsbD · i) hm
    simp only [BitVec.getLsbD_and, getLsbD_lowBitsSet (countMaxActiveBits_le z), hlt, decide_true,
      BitVec.getLsbD_not, hi, Bool.true_and, BitVec.getLsbD_zero, Bool.not_eq_false'] at this
    simp [this]

theorem and_eq_zero_of_knownZero {v z mask : BitVec w} (hz : v &&& z = 0#w)
    (hm : lowBitsSet w (countMaxActiveBits z) &&& mask = 0#w) : v &&& mask = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  cases hv : v.getLsbD i
  · simp
  · have hlt : i < countMaxActiveBits z := by
      refine Nat.lt_of_not_le fun hge => ?_
      rw [getLsbD_of_knownZero hz hge] at hv; cases hv
    have := congrArg (BitVec.getLsbD · i) hm
    simpa [BitVec.getLsbD_and, getLsbD_lowBitsSet (countMaxActiveBits_le z), hlt] using this

theorem shiftLeft_and_eq_zero_of_knownZero {u z mask : BitVec w} {s : Nat} (hz : u &&& z = 0#w)
    (hm : (lowBitsSet w (countMaxActiveBits z) <<< min s w) &&& mask = 0#w) : (u <<< s) &&& mask = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  by_cases his : i < s
  · simp [his]
  · cases hu : u.getLsbD (i - s)
    · simp
    · have hlt : i - s < countMaxActiveBits z := by
        refine Nat.lt_of_not_le fun hge => ?_
        rw [getLsbD_of_knownZero hz hge] at hu; cases hu
      have hsw : min s w = s := Nat.min_eq_left (by omega)
      have := congrArg (BitVec.getLsbD · i) hm
      simp only [hsw, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and, his,
        decide_false, Bool.not_false, getLsbD_lowBitsSet (countMaxActiveBits_le z), hlt,
        BitVec.getLsbD_zero] at this
      simp [this]

theorem shiftLeft_and_eq_self_of_knownZero {u z mask : BitVec w} {s : Nat} (hz : u &&& z = 0#w)
    (hm : (lowBitsSet w (countMaxActiveBits z) <<< min s w) &&& ~~~mask = 0#w) :
    (u <<< s) &&& mask = u <<< s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  by_cases his : i < s
  · simp [his]
  · cases hu : u.getLsbD (i - s)
    · simp
    · have hlt : i - s < countMaxActiveBits z := by
        refine Nat.lt_of_not_le fun hge => ?_
        rw [getLsbD_of_knownZero hz hge] at hu; cases hu
      have hsw : min s w = s := Nat.min_eq_left (by omega)
      have := congrArg (BitVec.getLsbD · i) hm
      simp only [hsw, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and, his,
        decide_false, Bool.not_false, getLsbD_lowBitsSet (countMaxActiveBits_le z), hlt,
        BitVec.getLsbD_not, BitVec.getLsbD_zero, Bool.not_eq_false'] at this
      simp [his, this]

theorem toNat_lt_two_pow_activeBits (x : BitVec w) : x.toNat < 2 ^ activeBits x := by
  unfold activeBits
  split
  · next h => rw [h]; exact Nat.one_pos
  · exact Nat.lt_log2_self

theorem activeBits_mono {x y : BitVec w} (h : x.toNat ≤ y.toNat) : activeBits x ≤ activeBits y := by
  unfold activeBits
  split
  · exact Nat.zero_le _
  · next hx =>
    split
    · next hy => omega
    · next hy =>
      have := (Nat.log2_lt hx).2 (Nat.lt_of_le_of_lt h (Nat.lt_log2_self (n := y.toNat)))
      omega

theorem activeBits_of_twoPow {c : BitVec w} {j : Nat} (h : c.toNat = 2 ^ j) : activeBits c = j + 1 := by
  unfold activeBits
  simp [h, Nat.log2_two_pow]

/-- A value with no known-zero bit set is at most the largest value the known zeros allow. -/
theorem toNat_le_not_of_and {x z : BitVec w} (hz : x &&& z = 0#w) : x.toNat ≤ (~~~z).toNat := by
  have : x &&& ~~~z = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (BitVec.getLsbD · i) hz
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
    cases hx : x.getLsbD i <;> simp_all
  rw [← this, BitVec.toNat_and]
  exact Nat.and_le_right

end Logic

/-! ### `simplifyAndCommutative`'s rewrites, one theorem each -/

/-- `IS.simplifyAndCommutative.L2024`: `~A & A` to 0. -/
theorem simplifyAndCommutative.L2024 (ρ : Env) (op0 op1 : Term w) (c0 : op0.Consistent ρ)
    (h : notWith (specific op1) op0 = true) : Refines ((andSrc op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  obtain ⟨a, ha, -, hd⟩ := notWith_denote h c0
  rw [andSrc_eval, hd, specific_denote ha]
  exact refines_ok (Lemmas.and_not_self_refines _)

/-- `IS.simplifyAndCommutative.L2028`: `(A | ?) & A` to `A`. -/
theorem simplifyAndCommutative.L2028 (ρ : Env) (op0 op1 : Term w) (c0 : op0.Consistent ρ)
    (h : chas .or (specific op1) (fun _ => true) op0 = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.old op1).eval ρ) := by
  obtain ⟨a, b, d, ha, -, -, -, hd⟩ := chas_or h c0
  rw [andSrc_eval, hd, specific_denote ha, Lemmas.Logic.and_comm]
  exact refines_ok (Generic.and_or_absorb_refines _ _ _)

/-- `IS.simplifyAndCommutative.L2034`: `(X | ~Y) & (X | Y)` to `X`. -/
theorem simplifyAndCommutative.L2034 (ρ : Env) (op0 op1 X Y : Term w) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (h0 : cbind .or some not? op0 = some (X, Y)) (h1 : isOf .or X Y op1 = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.old X).eval ρ) := by
  obtain ⟨a, b, d, ha, hb, -, cb, hd⟩ := cbind_or h0 c0
  cases ha
  obtain ⟨-, hbd⟩ := not?_denote hb cb
  obtain ⟨d', h1d⟩ := isOf_or h1 c1
  rw [andSrc_eval, hd, hbd, h1d]
  exact refines_ok (Lemmas.and_or_not_or_refines _ _ _ _)

/-- `IS.simplifyAndCommutative.L2045`: `-A & A` to `A` where `A` is a power of two or 0. -/
theorem simplifyAndCommutative.L2045 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 v : Term w)
    (c0 : op0.Consistent ρ) (hn : neg? op0 = some v) (h : (specific op1 v && o.powerOfTwo true op1) = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.old op1).eval ρ) := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨f1, f2, hd⟩ := neg?_denote hn c0
  rw [andSrc_eval, hd, specific_denote h.1]
  refine refines_ok (Lemmas.and_neg_self_refines _ _ _ fun x hx => ?_)
  rcases ho.powerOfTwo true op1 x h.2 hx with hp | ⟨-, h0⟩
  · exact .inl hp
  · exact .inr h0

/-- `IS.simplifyAndCommutative.L2051`: `(A - 1) & A` to 0 where `A` is a power of two or 0. -/
theorem simplifyAndCommutative.L2051 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 a : Term w)
    (c0 : op0.Consistent ρ) (ha : addAllOnes? op0 = some a) (h : (specific op1 a && o.powerOfTwo true op1) = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, f1, f2, hd⟩ := addAllOnes?_denote ha c0
  rw [andSrc_eval, hd, specific_denote h.1]
  refine refines_ok (Lemmas.and_add_allOnes_self_refines _ _ _ fun x hx => ?_)
  rcases ho.powerOfTwo true op1 x h.2 hx with hp | ⟨-, h0⟩
  · exact .inl hp
  · exact .inr h0

/-- `IS.simplifyAndCommutative.L2060`: `(X << N) & ((X << M) - 1)` to 0 where `X` is a power of two or 0 and
`M ≤ N`. -/
theorem simplifyAndCommutative.L2060 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 X X' sh : Term w)
    (shift1 shift2 : BitVec w) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (h0 : shiftConst? .shl op0 = some (X, shift1)) (h1 : addAllOnes? op1 = some sh)
    (h2 : shiftConst? .shl sh = some (X', shift2))
    (h : (specific X X' && o.powerOfTwo true X && decide (shift2.toNat ≤ shift1.toNat)) = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hX, hp⟩, hle⟩ := h
  obtain ⟨-, f1, f2, hd0⟩ := shiftConst?_shl h0 c0
  obtain ⟨csh, f5, f6, hd1⟩ := addAllOnes?_denote h1 c1
  obtain ⟨-, f3, f4, hdsh⟩ := shiftConst?_shl h2 csh
  rw [andSrc_eval, hd0, hd1, hdsh, specific_denote hX]
  refine refines_ok (Lemmas.and_shl_shl_add_allOnes_refines _ _ _ _ _ _ _ _ _ (fun x hx => ?_) hle)
  rcases ho.powerOfTwo true X x hp hx with hp | ⟨-, h0⟩
  · exact .inl hp
  · exact .inr h0

/-- Theorem 1 for `simplifyAndCommutative`: what it returns refines the `and`, in a run where the `Oracle`'s answers,
and the `Logic.Ext`'s if given, are sound. -/
theorem simplifyAndCommutative.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (x : Option Ext)
    (hx : ∀ e, x = some e → e.Sound ρ) (op0 op1 : Term w) (n : Nat) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) {r : Repl w} (h : run (simplifyAndCommutative.steps o x op0 op1 n) = .value r) :
    Refines ((andSrc op0 op1).eval ρ) (r.eval ρ) := by
  refine run_sound (P := fun r => Refines ((andSrc op0 op1).eval ρ) (r.eval ρ)) (fun s r hmem => ?_) h
  simp only [simplifyAndCommutative.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAndCommutative.L2024 ρ op0 op1 c0 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAndCommutative.L2028 ρ op0 op1 c0 (by assumption)
  · split at h
    · next X Y h0 =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndCommutative.L2034 ρ op0 op1 X Y c0 c1 h0 (by assumption)
    · simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h
    · next v hn =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndCommutative.L2045 ρ o ho op0 op1 v c0 hn (by assumption)
    · simp only [reduceCtorEq] at h
  · split at h
    · next a ha =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndCommutative.L2051 ρ o ho op0 op1 a c0 ha (by assumption)
    · simp only [reduceCtorEq] at h
  · split at h
    · next X shift1 sh h0 h1 =>
      split at h
      · next X' shift2 h2 =>
        split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
        obtain ⟨-, rfl⟩ := h
        exact simplifyAndCommutative.L2060 ρ o ho op0 op1 X X' sh shift1 shift2 c0 c1 h0 h1 h2 (by assumption)
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  · have := simplifyAndOrWithICmpEq.sound ρ x hx true false op0 op1 n c0 (run_of_forward h.symm)
    simpa [andOrSrc] using this

/-! ### `simplifyAndInst`'s rewrites, one theorem each -/

namespace Logic

variable {ρ : Env}

theorem orNUWShl?_denote {t X XS Y : Term w} {s : BitVec w} (h : orNUWShl? t = some ((X, s, XS), Y))
    (hc : t.Consistent ρ) : ∃ d nuw nsw, XS.denote ρ = Val.shl (X.denote ρ) (some s) nuw nsw ∧
      t.denote ρ = Val.or (Val.shl (X.denote ρ) (some s) nuw nsw) (Y.denote ρ) d := by
  obtain ⟨a, b, d, ha, hb, ca, -, hd⟩ := cbind_or h hc
  cases hb
  split at ha
  · next f x s' hs =>
    split at ha
    · cases hs' : apint s' <;> simp only [hs', Option.map_none, Option.map_some, reduceCtorEq,
        Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      obtain ⟨-, -, had⟩ := shl_denote hs ca
      rw [apint_denote hs'] at had
      exact ⟨d, _, _, had, by rw [hd, had]⟩
    · cases ha
  · cases ha

theorem orWith_denote {x o y : Term w} (h : xorOrDeferred?.orWith x o = some y) (hc : o.Consistent ρ) :
    ∃ d, o.denote ρ = Val.or (x.denote ρ) (y.denote ρ) d := by
  unfold xorOrDeferred?.orWith at h
  split at h
  · next f p q hb =>
    obtain ⟨-, -, hd⟩ := or_denote hb hc
    split at h
    · next hp => cases h; exact ⟨_, by rw [hd, specific_denote hp]⟩
    · split at h
      · next hq => cases h; exact ⟨_, by rw [hd, specific_denote hq, Lemmas.Logic.or_comm]⟩
      · cases h
  · cases h

theorem xorOrDeferred?_denote {t X Or Y : Term w} (h : xorOrDeferred? t = some (X, Or, Y)) (hc : t.Consistent ρ) :
    ∃ d, Or.denote ρ = Val.or (X.denote ρ) (Y.denote ρ) d ∧ t.denote ρ = Val.xor (Or.denote ρ) (X.denote ρ) := by
  unfold xorOrDeferred? at h
  split at h
  · next f a b hb =>
    obtain ⟨ca, cb, hd⟩ := xor_denote' hb hc
    split at h
    · next y hy =>
      cases h
      obtain ⟨d, hod⟩ := orWith_denote hy cb
      exact ⟨d, hod, by rw [hd, Lemmas.Logic.xor_comm]⟩
    · split at h
      · next y hy =>
        cases h
        obtain ⟨d, hod⟩ := orWith_denote hy ca
        exact ⟨d, hod, hd⟩
      · cases h
  · cases h

end Logic

/-- `IS.simplifyAndInst.L2078`: `X & poison` to poison. -/
theorem simplifyAndInst.L2078 (ρ : Env) (op0 op1 : Term w) (h : isPoison op1 = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [andSrc_eval, isPoison_denote h, Lemmas.Logic.and_none_right]
  exact refines_ok (Refine.val_none _)

/-- `IS.simplifyAndInst.L2082`: `X & undef` to 0, which without `undef` is `X & poison` to 0. -/
theorem simplifyAndInst.L2082 (ρ : Env) (op0 op1 : Term w) (u1 : op1.hasUndef = false)
    (h : isUndefValue op1 = true) : Refines ((andSrc op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [andSrc_eval, isUndefValue_denote h u1, Lemmas.Logic.and_none_right]
  exact refines_ok (Refine.val_none _)

/-- `IS.simplifyAndInst.L2086`: `X & X` to `X`. -/
theorem simplifyAndInst.L2086 (ρ : Env) (op0 op1 : Term w) (h : specific op0 op1 = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [andSrc_eval, specific_denote h, Generic.and_self]
  exact refines_ok (Refine.refl_val _)

/-- `IS.simplifyAndInst.L2090`: `X & 0` to 0. -/
theorem simplifyAndInst.L2090 (ρ : Env) (op0 op1 : Term w) (h : zero op1 = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [andSrc_eval, cst_eq h]
  exact refines_ok (Generic.and_zero_refines _)

/-- `IS.simplifyAndInst.L2094`: `X & -1` to `X`. -/
theorem simplifyAndInst.L2094 (ρ : Env) (op0 op1 : Term w) (h : allOnes op1 = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [andSrc_eval, cst_eq h, Generic.and_allOnes]
  exact refines_ok (Refine.refl_val _)

/-- `IS.simplifyAndInst.L2113`: `and (shl X, ShAmt), Mask` to the `shl` where `~Mask >> ShAmt` is 0. -/
theorem simplifyAndInst.L2113 (ρ : Env) (op0 op1 X : Term w) (mask shAmt : BitVec w) (c0 : op0.Consistent ρ)
    (hm : apint op1 = some mask) (hs : shiftConst? .shl op0 = some (X, shAmt))
    (h : (~~~mask >>> shAmt.toNat == 0#w) = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  obtain ⟨-, nuw, nsw, hd⟩ := shiftConst?_shl hs c0
  rw [andSrc_eval, apint_denote hm, Repl.eval_old, hd, Lemmas.and_shl_mask _ _ _ _ _ (by simpa using h)]
  exact refines_ok (Refine.refl_val _)

/-- `IS.simplifyAndInst.L2119`: `and (lshr X, ShAmt), Mask` to the `lshr` where `~Mask << ShAmt` is 0. -/
theorem simplifyAndInst.L2119 (ρ : Env) (op0 op1 X : Term w) (mask shAmt : BitVec w) (c0 : op0.Consistent ρ)
    (hm : apint op1 = some mask) (hs : shiftConst? .lshr op0 = some (X, shAmt))
    (h : (~~~mask <<< shAmt.toNat == 0#w) = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  obtain ⟨-, e, hd⟩ := shiftConst?_lshr hs c0
  rw [andSrc_eval, apint_denote hm, Repl.eval_old, hd, Lemmas.and_lshr_mask _ _ _ _ (by simpa using h)]
  exact refines_ok (Refine.refl_val _)

/-- `IS.simplifyAndInst.L2132`: `and (add Shift, -1), 2^C` to 0, where `Shift` is a power of two whose active bits,
from its known zeros, are at most `C + 1`'s. -/
theorem simplifyAndInst.L2132 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 shift : Term w) (powerC : BitVec w)
    (c0 : op0.Consistent ρ) (hm : apint op1 = some powerC) (hs : addAllOnes? op0 = some shift)
    (h : (decide powerC.toNat.isPowerOfTwo && o.powerOfTwo false shift &&
      decide (activeBits (~~~(o.knownZero shift)) ≤ activeBits powerC)) = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, hp⟩, ha⟩ := h
  obtain ⟨-, nuw, nsw, hd⟩ := addAllOnes?_denote hs c0
  rw [andSrc_eval, apint_denote hm, hd]
  refine refines_ok (Lemmas.and_add_allOnes_twoPow_refines _ _ _ _ (fun x hx => ?_) hc)
  have hx2 : x.toNat.isPowerOfTwo := by
    rcases ho.powerOfTwo false shift x hp hx with h2 | ⟨h2, -⟩
    · exact h2
    · cases h2
  refine ⟨hx2, ?_⟩
  obtain ⟨j, hj⟩ := hc
  have h1 := toNat_lt_two_pow_activeBits x
  have h2 := activeBits_mono (toNat_le_not_of_and (ho.knownZero shift x hx))
  rw [activeBits_of_twoPow hj] at ha
  have h3 : 2 ^ activeBits x ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [hj, ← Nat.pow_succ']
  omega

/-- `IS.simplifyAndInst.L2157`: `A & (A && B)` to `A && B`, on `i1`. -/
theorem simplifyAndInst.L2157 (ρ : Env) (op0 op1 : Term 1) (c1 : op1.Consistent ρ)
    (h : selectOf true op0 op1 = true) : Refines ((andSrc op0 op1).eval ρ) ((Repl.old op1).eval ρ) := by
  obtain ⟨tv, hd⟩ := selectOf_and h c1
  rw [andSrc_eval, Repl.eval_old, hd]
  exact refines_ok (Lemmas.and_select_refines _ _)

/-- `IS.simplifyAndInst.L2159`: `(A && B) & A` to `A && B`, on `i1`. -/
theorem simplifyAndInst.L2159 (ρ : Env) (op0 op1 : Term 1) (c0 : op0.Consistent ρ)
    (h : selectOf true op1 op0 = true) : Refines ((andSrc op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  obtain ⟨tv, hd⟩ := selectOf_and h c0
  rw [andSrc_eval, Repl.eval_old, hd, Lemmas.Logic.and_comm]
  exact refines_ok (Lemmas.and_select_refines _ _)

/-- `IS.simplifyAndInst.L2203`: `((X << A) | Y) & Mask` to `Y`, where `Mask` has every bit `Y` may have, and none of
those `X << A` may have, from known bits. -/
theorem simplifyAndInst.L2203 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 X XS Y : Term w)
    (mask shAmt : BitVec w) (c0 : op0.Consistent ρ) (hm : apint op1 = some mask)
    (hs : orNUWShl? op0 = some ((X, shAmt, XS), Y))
    (h : (decide (countMaxActiveBits (o.knownZero Y) ≤ min shAmt.toNat w) && effBitsY o Y &&& ~~~mask == 0#w &&
      effBitsX o X shAmt &&& mask == 0#w) = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.old Y).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨-, hy⟩, hx⟩ := h
  obtain ⟨d, nuw, nsw, -, hd⟩ := orNUWShl?_denote hs c0
  rw [andSrc_eval, apint_denote hm, hd, Repl.eval_old]
  exact refines_ok (Lemmas.and_or_shl_mask_refines_right _ _ _ _ _ _ _
    (fun v hv => and_eq_self_of_knownZero (ho.knownZero Y v hv) hy)
    (fun u hu => shiftLeft_and_eq_zero_of_knownZero (ho.knownZero X u hu) hx))

/-- `IS.simplifyAndInst.L2205`: `((X << A) | Y) & Mask` to `X << A`, where `Mask` has every bit `X << A` may have,
and none of those `Y` may have, from known bits. -/
theorem simplifyAndInst.L2205 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 X XS Y : Term w)
    (mask shAmt : BitVec w) (c0 : op0.Consistent ρ) (hm : apint op1 = some mask)
    (hs : orNUWShl? op0 = some ((X, shAmt, XS), Y))
    (h : (decide (countMaxActiveBits (o.knownZero Y) ≤ min shAmt.toNat w) && effBitsX o X shAmt &&& ~~~mask == 0#w &&
      effBitsY o Y &&& mask == 0#w) = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.old XS).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨-, hx⟩, hy⟩ := h
  obtain ⟨d, nuw, nsw, hxs, hd⟩ := orNUWShl?_denote hs c0
  rw [andSrc_eval, apint_denote hm, hd, Repl.eval_old, hxs]
  exact refines_ok (Lemmas.and_or_shl_mask_refines_left _ _ _ _ _ _ _
    (fun v hv => and_eq_zero_of_knownZero (ho.knownZero Y v hv) hy)
    (fun u hu => shiftLeft_and_eq_self_of_knownZero (ho.knownZero X u hu) hx))

/-- `IS.simplifyAndInst.L2216`: `((X | Y) ^ X) & ((X | Y) ^ Y)` to 0, either way round. -/
theorem simplifyAndInst.L2216 (ρ : Env) (op0 op1 X Or Y : Term w) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (h0 : xorOrDeferred? op0 = some (X, Or, Y)) (h1 : isOf .xor Or Y op1 = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  obtain ⟨d, hor, hd0⟩ := xorOrDeferred?_denote h0 c0
  rw [andSrc_eval, hd0, isOf_xor h1 c1, hor]
  exact refines_ok (Lemmas.and_xor_or_xor_or_refines _ _ _)

/-- `IS.simplifyAndInst.L2223`: `(A ^ C) & (A ^ ~C)` to 0. -/
theorem simplifyAndInst.L2223 (ρ : Env) (op0 op1 A A' : Term w) (c1 c2 : BitVec w) (cs0 : op0.Consistent ρ)
    (cs1 : op1.Consistent ρ) (h0 : xorConst? op0 = some (A, c1)) (h1 : xorConst? op1 = some (A', c2))
    (h : (specific A A' && c2 == ~~~c1) = true) :
    Refines ((andSrc op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hA, rfl⟩ := h
  rw [andSrc_eval, xorConst?_denote h0 cs0, xorConst?_denote h1 cs1, specific_denote hA]
  exact refines_ok (Lemmas.and_xor_xor_not_refines _ _)

/-- `IS.simplifyAndInst.L2229`: `A & B` to `A` on `i1`, where `A` true implies `B` true. -/
theorem simplifyAndInst.L2229 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 : Term 1)
    (h : o.implies op0 op1 = some true) : Refines ((andSrc op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [andSrc_eval, Repl.eval_old]
  exact refines_ok (Lemmas.and_refines_left_of_implies _ _ fun ha => by
    simpa using ho.implies op0 op1 true h ha)

/-- `IS.simplifyAndInst.L2232`: `A & B` to false on `i1`, where `A` true implies `B` false. -/
theorem simplifyAndInst.L2232 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 : Term 1)
    (h : o.implies op0 op1 = some false) : Refines ((andSrc op0 op1).eval ρ) ((Repl.const 0#1).eval ρ) := by
  rw [andSrc_eval, Repl.eval_const]
  exact refines_ok (Lemmas.and_refines_false_of_implies _ _ fun ha => by
    simpa using ho.implies op0 op1 false h ha)

/-- `IS.simplifyAndInst.L2237`: `A & B` to `B` on `i1`, where `B` true implies `A` true. -/
theorem simplifyAndInst.L2237 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 : Term 1)
    (h : o.implies op1 op0 = some true) : Refines ((andSrc op0 op1).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [andSrc_comm]
  exact simplifyAndInst.L2229 ρ o ho op1 op0 h

/-- `IS.simplifyAndInst.L2240`: `A & B` to false on `i1`, where `B` true implies `A` false. -/
theorem simplifyAndInst.L2240 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 : Term 1)
    (h : o.implies op1 op0 = some false) : Refines ((andSrc op0 op1).eval ρ) ((Repl.const 0#1).eval ρ) := by
  rw [andSrc_comm]
  exact simplifyAndInst.L2232 ρ o ho op1 op0 h

/-! ### The fold -/

/-- Every step of `simplifyAndInst` that fires is right, the folds it forwards to included. -/
theorem simplifyAndInst.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (x : Option Ext)
    (hx : ∀ e, x = some e → e.Sound ρ) (op0 op1 : Term w) (n : Nat) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) :
    ∀ s r, Step.fire s r ∈ simplifyAndInst.steps o x op0 op1 n → Refines ((andSrc op0 op1).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyAndInst.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h
  -- X & poison, X & undef, X & X, X & 0, X & -1
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAndInst.L2078 ρ op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAndInst.L2082 ρ op0 op1 u1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAndInst.L2086 ρ op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAndInst.L2090 ρ op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAndInst.L2094 ρ op0 op1 (by assumption)
  -- simplifyAndCommutative both ways, and simplifyLogicOfAddSub
  · exact simplifyAndCommutative.sound ρ o ho x hx op0 op1 n c0 c1 (run_of_forward h.symm)
  · rw [andSrc_comm]
    exact simplifyAndCommutative.sound ρ o ho x hx op1 op0 n c1 c0 (run_of_forward h.symm)
  · exact simplifyLogicOfAddSub.sound ρ .and false op0 op1 c0 c1 u0 u1 (.inl rfl) (run_of_forward h.symm)
  -- the masks of shifts
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndInst.L2113 ρ op0 op1 _ _ _ c0 (by assumption) (by assumption) (by assumption)
    · simp only [reduceCtorEq] at h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndInst.L2119 ρ op0 op1 _ _ _ c0 (by assumption) (by assumption) (by assumption)
    · simp only [reduceCtorEq] at h
  · split at h
    · next powerC shift hm hs =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndInst.L2132 ρ o ho op0 op1 shift powerC c0 hm hs (by assumption)
    · simp only [reduceCtorEq] at h
  -- simplifyAndOrOfCmps, simplifyAssociativeBinOp and expandCommutativeBinOp hand over
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  -- A & (A && B), (A && B) & A
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨-, rfl⟩, hs⟩ := hc
    exact simplifyAndInst.L2157 ρ op0 op1 c1 hs
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨-, rfl⟩, hs⟩ := hc
    exact simplifyAndInst.L2159 ρ op0 op1 c0 hs
  -- threadBinOpOverSelect and threadBinOpOverPHI hand over
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  -- ((X << A) | Y) & Mask
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndInst.L2203 ρ o ho op0 op1 _ _ _ _ _ c0 (by assumption) (by assumption) (by assumption)
    · simp only [reduceCtorEq] at h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndInst.L2205 ρ o ho op0 op1 _ _ _ _ _ c0 (by assumption) (by assumption) (by assumption)
    · simp only [reduceCtorEq] at h
  -- ((X | Y) ^ X) & ((X | Y) ^ Y), (A ^ C) & (A ^ ~C)
  · split at h
    · next X Or Y h0 =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndInst.L2216 ρ op0 op1 X Or Y c0 c1 h0 (by assumption)
    · simp only [reduceCtorEq] at h
  · split at h
    · next A c1' A' c2 h0 h1 =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndInst.L2223 ρ op0 op1 A A' c1' c2 c0 c1 h0 h1 (by assumption)
    · simp only [reduceCtorEq] at h
  -- implied conditions, on i1
  · split at h
    · next hw =>
      subst hw
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hi =>
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndInst.L2229 ρ o ho op0 op1 (by simpa [asI1] using hi)
    · simp only [reduceCtorEq] at h
  · split at h
    · next hw =>
      subst hw
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hi =>
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndInst.L2232 ρ o ho op0 op1 (by simpa [asI1] using hi)
    · simp only [reduceCtorEq] at h
  · split at h
    · next hw =>
      subst hw
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hi =>
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndInst.L2237 ρ o ho op0 op1 (by simpa [asI1] using hi)
    · simp only [reduceCtorEq] at h
  · split at h
    · next hw =>
      subst hw
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hi =>
      obtain ⟨-, rfl⟩ := h
      exact simplifyAndInst.L2240 ρ o ho op0 op1 (by simpa [asI1] using hi)
    · simp only [reduceCtorEq] at h
  -- simplifyByDomEq hands over
  · unfold domEqStep at h
    repeat' (split at h <;> try simp only [reduceCtorEq] at h)

/-- Theorem 1 for `simplifyAndInst`: every value the model returns refines the `and` it replaces, at every width and
recursion budget, in every run its operands are consistent with, poison included, where the `Oracle`'s answers are
sound (PASS-01's) and, if a `Logic.Ext` is given, its answers are too: `isImpliedCondition`'s, and
`simplifyWithOpReplaced`'s, the recursive simplifier's. It says nothing about operands that reach an `undef`. -/
theorem simplifyAndInst.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (x : Option Ext)
    (hx : ∀ e, x = some e → e.Sound ρ) (op0 op1 : Term w) (n : Nat) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) {r : Repl w}
    (h : simplifyAndInst o x op0 op1 n = .value r) : Refines ((andSrc op0 op1).eval ρ) (r.eval ρ) := by
  unfold simplifyAndInst at h
  split at h
  · split at h
    · cases h
    · rw [andSrc_comm]
      exact run_sound (simplifyAndInst.steps_sound ρ o ho x hx op1 op0 n c1 c0 u1 u0) h
  · exact run_sound (simplifyAndInst.steps_sound ρ o ho x hx op0 op1 n c0 c1 u0 u1) h

/-- What `onInst` answers for an `and` refines it. -/
theorem simplifyAndInst.onInst_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (t : Term w) (ht : t.Consistent ρ)
    (hu : t.hasUndef = false) {r : Repl w} (h : simplifyAndInst.onInst o t = .value r) :
    Refines (t.top.eval ρ) (r.eval ρ) := by
  cases t with
  | bin id op f a b =>
    cases op <;> simp only [simplifyAndInst.onInst, reduceCtorEq] at h
    obtain ⟨ca, cb, -⟩ := ht
    simp only [Term.hasUndef, Bool.or_eq_false_iff] at hu
    exact simplifyAndInst.sound ρ o ho _ (some_none_sound ρ) a b 3 ca cb hu.1 hu.2 h
  | _ => simp [simplifyAndInst.onInst] at h

end Peephole.IS
