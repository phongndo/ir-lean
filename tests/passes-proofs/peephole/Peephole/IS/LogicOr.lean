import Peephole.IS.LogicAnd

/-! # InstSimplify's `simplifyOrInst` and `simplifyOrLogic`, and their rewrites for every input

`simplifyOrLogic` and `simplifyOrInst` are at `llvm/lib/Analysis/InstructionSimplify.cpp:2255-2526` at
`llvmorg-23.1.3`. This is their model on `Peephole.Term`, step by step in the C++'s order. Each step that rewrites
carries its ID from `tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyOrLogic.L2261` | `X \| ~X` to -1 |
| `IS.simplifyOrLogic.L2265` | `X \| ~(X & ?)` to -1 |
| `IS.simplifyOrLogic.L2269` | `X \| (X & ?)` to `X` |
| `IS.simplifyOrLogic.L2277` | `(A ^ B) \| (A \| B)` to `A \| B` |
| `IS.simplifyOrLogic.L2283` | `~(A ^ B) \| (A \| B)` to -1 |
| `IS.simplifyOrLogic.L2291` | `(A & ~B) \| (A ^ B)` to `A ^ B` |
| `IS.simplifyOrLogic.L2299` | `(~A ^ B) \| (A & B)` to `~A ^ B` |
| `IS.simplifyOrLogic.L2307` | `(~A \| B) \| (A ^ B)` to -1 |
| `IS.simplifyOrLogic.L2317` | `(~A & B) \| ~(A \| B)` to `~A` |
| `IS.simplifyOrLogic.L2324` | `(~A && B) \| ~(A \|\| B)` to `~A`, with logical `and` and `or`, on `i1` |
| `IS.simplifyOrLogic.L2332` | `~(A ^ B) \| (A & B)` to `~(A ^ B)` |
| `IS.simplifyOrLogic.L2339` | `~(A & B) \| (A ^ B)` to `~(A & B)` |
| `IS.simplifyOrInst.L2353` | `X \| poison` to poison |
| `IS.simplifyOrInst.L2359` | `X \| undef` and `X \| -1` to -1. IRLean has no `undef`, so the first is about poison only |
| `IS.simplifyOrInst.L2364` | `X \| X` and `X \| 0` to `X` |
| `IS.simplifyOrInst.L2387` | `(-1 << X) \| (-1 >> (C - X))` to -1, with `C` at most the width, either way round |
| `IS.simplifyOrInst.L2399` | `(fshl X, ?, Y) \| (shl X, Y)` to the `fshl` |
| `IS.simplifyOrInst.L2403` | `(shl X, Y) \| (fshl X, ?, Y)` to the `fshl` |
| `IS.simplifyOrInst.L2410` | `(fshr ?, X, Y) \| (lshr X, Y)` to the `fshr` |
| `IS.simplifyOrInst.L2414` | `(lshr X, Y) \| (fshr ?, X, Y)` to the `fshr` |
| `IS.simplifyOrInst.L2448` | `A \| (A \|\| B)` to `A \|\| B`, on `i1` |
| `IS.simplifyOrInst.L2450` | `(A \|\| B) \| A` to `A \|\| B`, on `i1` |
| `IS.simplifyOrInst.L2475` | `((B + N) & ~C) \| (B & C)` to `B + N`, where `C` is a mask of low bits `N` has none of |
| `IS.simplifyOrInst.L2481` | `(A & C) \| ((A + N) & ~C)` to `A + N`, the same the other way round |
| `IS.simplifyOrInst.L2495` | `(A ^ C) \| (A ^ ~C)` to -1 |
| `IS.simplifyOrInst.L2502` | `A \| B` to `A` on `i1`, where `A` false implies `B` false |
| `IS.simplifyOrInst.L2505` | `A \| B` to true on `i1`, where `A` false implies `B` true |
| `IS.simplifyOrInst.L2511` | `A \| B` to `B` on `i1`, where `B` false implies `A` false |
| `IS.simplifyOrInst.L2514` | `A \| B` to true on `i1`, where `B` false implies `A` true |

`IS.simplifyOrInst.L2430` and `L2432` aren't proved: the overflow bit of `umul.with.overflow`, an `extractvalue`, isn't
a `Term`, so the model hands over to `isCheckForZeroAndMulWithOverflow` wherever an operand could be one.

`simplifyOrInst.sound` puts them together with the folds it calls: every value the model returns refines the `or`, with
or without `disjoint`, at every width and recursion budget, poison included, in every run where the `Oracle`'s answers,
and the `Logic.Ext`'s if given, are sound. -/

namespace Peephole.IS

open IRLean Logic

variable {w : Nat}

namespace Logic

/-! ### Matchers `simplifyOrLogic` and `simplifyOrInst` use -/

/-- `m_c_LogicalAnd(L, R)` on an `i1`: `and` either way round, or `select C, T, false` with `L` on `C` and `R` on
`T`, or the other way round, and what they bound in the first order that matches. -/
def logicalAnd? {α β : Type} (l : Term 1 → Option α) (r : Term 1 → Option β) : Term 1 → Option (α × β)
  | .bin _ .and _ a b => both a b
  | .select _ c t f => if zero f then both c t else none
  | _ => none
where
  /-- `(L.match(P) && R.match(Q)) || (L.match(Q) && R.match(P))`. -/
  both (p q : Term 1) : Option (α × β) :=
    match l p, r q with
    | some x, some y => some (x, y)
    | _, _ =>
      match l q, r p with
      | some x, some y => some (x, y)
      | _, _ => none

/-- `m_c_LogicalOr(m_Specific(A), m_Specific(B))` on an `i1`: `or` either way round, or `select C, true, F` with
`{C, F}` being `{A, B}`. -/
def isLogicalOrOf (a b : Term 1) : Term 1 → Bool
  | .bin _ .or _ p q => (specific a p && specific b q) || (specific a q && specific b p)
  | .select _ c t f => one t && ((specific a c && specific b f) || (specific a f && specific b c))
  | _ => false

/-- A step of an `i1` operation, as a step of the operation's width. -/
def castStep (h : w = 1) (s : Step 1) : Step w := h ▸ s

/-- `m_Shl(m_AllOnes(), m_Value(X))` or `m_LShr(m_AllOnes(), m_Value(X))`: `X`. -/
def allOnesShift? (op : BinOp) (t : Term w) : Option (Term w) :=
  match binop? op t with
  | some (_, a, x) => if allOnes a then some x else none
  | none => none

/-- `(match(Op0, m_Shl(m_AllOnes(), m_Value(X))) && match(Op1, m_LShr(m_AllOnes(), m_Value(Y)))) ||
(match(Op1, m_Shl(m_AllOnes(), m_Value(X))) && match(Op0, m_LShr(m_AllOnes(), m_Value(Y))))`: `X` and `Y`. -/
def rotatedAllOnes? (op0 op1 : Term w) : Option (Term w × Term w) :=
  match allOnesShift? .shl op0, allOnesShift? .lshr op1 with
  | some X, some Y => some (X, Y)
  | _, _ =>
    match allOnesShift? .shl op1, allOnesShift? .lshr op0 with
    | some X, some Y => some (X, Y)
    | _, _ => none

/-- `m_Sub(m_APInt(C), m_Specific(S))` on `V`: `C`. -/
def subFrom? (s v : Term w) : Option (BitVec w) :=
  match binop? .sub v with
  | some (_, c, s') => if specific s s' then apint c else none
  | none => none

/-- `match(X, m_Sub(m_APInt(C), m_Specific(Y))) || match(Y, m_Sub(m_APInt(C), m_Specific(X)))`: `C`. -/
def rotateC? (X Y : Term w) : Option (BitVec w) :=
  match subFrom? Y X with
  | some c => some c
  | none => subFrom? X Y

/-- `match(A, m_Intrinsic<fshl>(m_Value(X), m_Value(), m_Value(Y))) && match(B, m_Shl(m_Specific(X),
m_Specific(Y)))`. -/
def fshlShl (a b : Term w) : Bool :=
  match a with
  | .fsh _ true x _ y =>
    match binop? .shl b with
    | some (_, p, q) => specific x p && specific y q
    | none => false
  | _ => false

/-- `match(A, m_Intrinsic<fshr>(m_Value(), m_Value(X), m_Value(Y))) && match(B, m_LShr(m_Specific(X),
m_Specific(Y)))`. -/
def fshrLshr (a b : Term w) : Bool :=
  match a with
  | .fsh _ false _ x y =>
    match binop? .lshr b with
    | some (_, p, q) => specific x p && specific y q
    | none => false
  | _ => false

/-- `m_And(m_Value(A), m_APInt(C))`: `A` and `C`. -/
def andConst? (t : Term w) : Option (Term w × BitVec w) := shiftConst? .and t

/-- `m_c_Add(m_Specific(S), m_Value(N))` on `T`: `N`. -/
def addOf? (s t : Term w) : Option (Term w) :=
  match binop? .add t with
  | some (_, p, q) => if specific s p then some q else if specific s q then some p else none
  | none => none

/-- `MaskedValueIsZero(V, M, Q)`: `M` is in the known zeros of `V`, `M.isSubsetOf(Known.Zero)`. -/
def maskedValueIsZero (o : Oracle) (v : Term w) (m : BitVec w) : Bool := m &&& ~~~(o.knownZero v) == 0#w

end Logic

/-! ## `simplifyOrLogic` -/

/-- The step for the logical `and` and `or` in `simplifyOrLogic`, on `i1`. -/
def simplifyOrLogic.logicalStep (X Y : Term 1) : Step 1 :=
  match logicalAnd? (fun u => (not? u).map fun a => (u, a)) some X with
  | some ((NotA, A), B) =>
    if notWith (isLogicalOrOf A B) Y then .fire "IS.simplifyOrLogic.L2324" (.old NotA) else .next
  | none => .next

/-- `simplifyOrLogic(X, Y)`, step by step. -/
def simplifyOrLogic.steps (X Y : Term w) : List (Step w) :=
  [ -- X | ~X --> -1
    if notWith (specific X) Y then .fire "IS.simplifyOrLogic.L2261" (.const (BitVec.allOnes w)) else .next,
    -- X | ~(X & ?) = -1
    if notWith (chas .and (specific X) (fun _ => true)) Y then
      .fire "IS.simplifyOrLogic.L2265" (.const (BitVec.allOnes w))
    else .next,
    -- X | (X & ?) --> X
    if chas .and (specific X) (fun _ => true) Y then .fire "IS.simplifyOrLogic.L2269" (.old X) else .next,
    -- (A ^ B) | (A | B) --> A | B
    -- (A ^ B) | (B | A) --> B | A
    match ops? .xor X with
    | some (A, B) => if isOf .or A B Y then .fire "IS.simplifyOrLogic.L2277" (.old Y) else .next
    | none => .next,
    -- ~(A ^ B) | (A | B) --> -1
    -- ~(A ^ B) | (B | A) --> -1
    match notBind (ops? .xor) X with
    | some (A, B) =>
      if isOf .or A B Y then .fire "IS.simplifyOrLogic.L2283" (.const (BitVec.allOnes w)) else .next
    | none => .next,
    -- (A & ~B) | (A ^ B) --> A ^ B
    -- (~B & A) | (A ^ B) --> A ^ B
    -- (A & ~B) | (B ^ A) --> B ^ A
    -- (~B & A) | (B ^ A) --> B ^ A
    match cbind .and some not? X with
    | some (A, B) => if isOf .xor A B Y then .fire "IS.simplifyOrLogic.L2291" (.old Y) else .next
    | none => .next,
    -- (~A ^ B) | (A & B) --> ~A ^ B
    -- (B ^ ~A) | (A & B) --> B ^ ~A
    -- (~A ^ B) | (B & A) --> ~A ^ B
    -- (B ^ ~A) | (B & A) --> B ^ ~A
    match cbind .xor not? some X with
    | some (A, B) => if isOf .and A B Y then .fire "IS.simplifyOrLogic.L2299" (.old X) else .next
    | none => .next,
    -- (~A | B) | (A ^ B) --> -1
    -- (~A | B) | (B ^ A) --> -1
    -- (B | ~A) | (A ^ B) --> -1
    -- (B | ~A) | (B ^ A) --> -1
    match cbind .or not? some X with
    | some (A, B) =>
      if isOf .xor A B Y then .fire "IS.simplifyOrLogic.L2307" (.const (BitVec.allOnes w)) else .next
    | none => .next,
    -- (~A & B) | ~(A | B) --> ~A
    -- (~A & B) | ~(B | A) --> ~A
    -- (B & ~A) | ~(A | B) --> ~A
    -- (B & ~A) | ~(B | A) --> ~A
    match cbind .and (fun u => (not? u).map fun a => (u, a)) some X with
    | some ((NotA, A), B) =>
      if notWith (isOf .or A B) Y then .fire "IS.simplifyOrLogic.L2317" (.old NotA) else .next
    | none => .next,
    -- The same is true of Logical And
    if h : w = 1 then castStep h (simplifyOrLogic.logicalStep (asI1 h X) (asI1 h Y)) else .next,
    -- ~(A ^ B) | (A & B) --> ~(A ^ B)
    -- ~(A ^ B) | (B & A) --> ~(A ^ B)
    match notBind (ops? .xor) X with
    | some (A, B) => if isOf .and A B Y then .fire "IS.simplifyOrLogic.L2332" (.old X) else .next
    | none => .next,
    -- ~(A & B) | (A ^ B) --> ~(A & B)
    -- ~(A & B) | (B ^ A) --> ~(A & B)
    match notBind (ops? .and) X with
    | some (A, B) => if isOf .xor A B Y then .fire "IS.simplifyOrLogic.L2339" (.old X) else .next
    | none => .next ]

/-! ## `simplifyOrInst` -/

/-- The steps for the implied conditions in `simplifyOrInst`, on `i1`: `isImpliedCondition(A, B, DL, false)`, which
`Logic.Ext` answers. With no `Ext`, the model hands over. -/
def simplifyOrInst.impliedStep (x : Option Ext) (isFalse swap : Bool) (op0 op1 : Term 1) : Step 1 :=
  match x with
  | none => .delegate "isImpliedCondition"
  | some e =>
    if swap then
      if isFalse then
        if e.impliesFalse op1 op0 == some false then .fire "IS.simplifyOrInst.L2511" (.old op1) else .next
      else
        if e.impliesFalse op1 op0 == some true then .fire "IS.simplifyOrInst.L2514" (.const 1#1) else .next
    else
      if isFalse then
        if e.impliesFalse op0 op1 == some false then .fire "IS.simplifyOrInst.L2502" (.old op0) else .next
      else
        if e.impliesFalse op0 op1 == some true then .fire "IS.simplifyOrInst.L2505" (.const 1#1) else .next

/-- `simplifyOrInst` once `foldOrCommuteConstant` has put a lone constant on the right, step by step. -/
def simplifyOrInst.steps (o : Oracle) (x : Option Ext) (op0 op1 : Term w) (n : Nat) : List (Step w) :=
  [ -- X | poison -> poison
    if isPoison op1 then .fire "IS.simplifyOrInst.L2353" (.old op1) else .next,
    -- X | undef -> -1
    -- X | -1 = -1
    -- Do not return Op1 because it may contain undef elements if it's a vector.
    if isUndefValue op1 || allOnes op1 then .fire "IS.simplifyOrInst.L2359" (.const (BitVec.allOnes w)) else .next,
    -- X | X = X
    -- X | 0 = X
    if specific op0 op1 || zero op1 then .fire "IS.simplifyOrInst.L2364" (.old op0) else .next,
    forward (simplifyOrLogic.steps op0 op1),
    forward (simplifyOrLogic.steps op1 op0),
    forward (simplifyLogicOfAddSub.steps op0 op1 .or),
    -- Rotated -1 is still -1:
    -- (-1 << X) | (-1 >> (C - X)) --> -1
    -- (-1 >> X) | (-1 << (C - X)) --> -1
    -- ...with C <= bitwidth (and commuted variants).
    match rotatedAllOnes? op0 op1 with
    | some (X, Y) =>
      match rotateC? X Y with
      | some c => if c.toNat ≤ w then .fire "IS.simplifyOrInst.L2387" (.const (BitVec.allOnes w)) else .next
      | none => .next
    | none => .next,
    -- A funnel shift (rotate) can be decomposed into simpler shifts. See if we
    -- are mixing in another shift that is redundant with the funnel shift.
    -- (fshl X, ?, Y) | (shl X, Y) --> fshl X, ?, Y
    -- (shl X, Y) | (fshl X, ?, Y) --> fshl X, ?, Y
    if fshlShl op0 op1 then .fire "IS.simplifyOrInst.L2399" (.old op0) else .next,
    if fshlShl op1 op0 then .fire "IS.simplifyOrInst.L2403" (.old op1) else .next,
    -- (fshr ?, X, Y) | (lshr X, Y) --> fshr ?, X, Y
    -- (lshr X, Y) | (fshr ?, X, Y) --> fshr ?, X, Y
    if fshrLshr op0 op1 then .fire "IS.simplifyOrInst.L2410" (.old op0) else .next,
    if fshrLshr op1 op0 then .fire "IS.simplifyOrInst.L2414" (.old op1) else .next,
    forward (simplifyAndOrWithICmpEq.steps x false op0 op1 n),
    forward (simplifyAndOrWithICmpEq.steps x false op1 op0 n),
    if isCmpPair op0 op1 then .delegate "simplifyAndOrOfCmps" else .next,
    -- If we have a multiplication overflow check that is being 'and'ed with a
    -- check that one of the multipliers is not zero, we can omit the 'and', and
    -- only keep the overflow check.
    if mulOverflowCheck false op0 op1 then .delegate "isCheckForZeroAndMulWithOverflow" else .next,
    if mulOverflowCheck false op1 op0 then .delegate "isCheckForZeroAndMulWithOverflow" else .next,
    -- Try some generic simplifications for associative operations.
    if n != 0 && (isBin .or op0 || isBin .or op1) then .delegate "simplifyAssociativeBinOp" else .next,
    -- Or distributes over And.  Try some generic simplifications based on this.
    if n != 0 && (isBin .and op0 || isBin .and op1) then .delegate "expandCommutativeBinOp" else .next,
    -- A | (A || B) -> A || B
    if (isSelect op0 || isSelect op1) && w == 1 && selectOf false op0 op1 then
      .fire "IS.simplifyOrInst.L2448" (.old op1)
    else .next,
    if (isSelect op0 || isSelect op1) && w == 1 && selectOf false op1 op0 then
      .fire "IS.simplifyOrInst.L2450" (.old op0)
    else .next,
    -- If the operation is with the result of a select instruction, check
    -- whether operating on either branch of the select always yields the same
    -- value.
    if (isSelect op0 || isSelect op1) && n != 0 then .delegate "threadBinOpOverSelect" else .next,
    -- (A & C1)|(B & C2)
    -- If we have: ((V + N) & C1) | (V & C2)
    -- .. and C2 = ~C1 and C2 is 0+1+ and (N & C2) == 0
    -- replace with V+N.
    match andConst? op0, andConst? op1 with
    | some (A, c1), some (B, c2) =>
      if c1 == ~~~c2 && isMask c2 then
        match addOf? B A with
        | some N => if maskedValueIsZero o N c2 then .fire "IS.simplifyOrInst.L2475" (.old A) else .next
        | none => .next
      else .next
    | _, _ => .next,
    -- Or commutes, try both ways.
    match andConst? op0, andConst? op1 with
    | some (A, c1), some (B, c2) =>
      if c1 == ~~~c2 && isMask c1 then
        match addOf? A B with
        | some N => if maskedValueIsZero o N c1 then .fire "IS.simplifyOrInst.L2481" (.old B) else .next
        | none => .next
      else .next
    | _, _ => .next,
    -- If the operation is with the result of a phi instruction, check whether
    -- operating on all incoming values of the phi always yields the same value.
    if (isOpaque op0 || isOpaque op1) && n != 0 then .delegate "threadBinOpOverPHI" else .next,
    -- (A ^ C) | (A ^ ~C) -> -1, i.e. all bits set to one.
    match xorConst? op0, xorConst? op1 with
    | some (A, c1), some (A', c2) =>
      if specific A A' && c2 == ~~~c1 then .fire "IS.simplifyOrInst.L2495" (.const (BitVec.allOnes w)) else .next
    | _, _ => .next,
    -- If Op0 is false implies Op1 is false, then Op1 is a subset of Op0.
    if h : w = 1 then castStep h (simplifyOrInst.impliedStep x true false (asI1 h op0) (asI1 h op1)) else .next,
    -- If Op0 is false implies Op1 is true, then at least one is always true.
    if h : w = 1 then castStep h (simplifyOrInst.impliedStep x false false (asI1 h op0) (asI1 h op1)) else .next,
    -- If Op1 is false implies Op0 is false, then Op0 is a subset of Op1.
    if h : w = 1 then castStep h (simplifyOrInst.impliedStep x true true (asI1 h op0) (asI1 h op1)) else .next,
    -- If Op1 is false implies Op0 is true, then at least one is always true.
    if h : w = 1 then castStep h (simplifyOrInst.impliedStep x false true (asI1 h op0) (asI1 h op1)) else .next,
    domEqStep x op0 op1 n ]

/-- `simplifyOrInst(Op0, Op1, Q, MaxRecurse)`. `foldOrCommuteConstant` folds two constants, which the constant folder
does, at `IS.foldOrCommuteConstant.L582`, and swaps a lone constant to the right. -/
def simplifyOrInst (o : Oracle) (x : Option Ext) (op0 op1 : Term w) (n : Nat) : Result w :=
  if op0.isConstant then
    if op1.isConstant then .delegated "ConstantFoldBinaryOpOperands"
    else run (simplifyOrInst.steps o x op1 op0 n)
  else run (simplifyOrInst.steps o x op0 op1 n)

/-- What InstSimplify does with an instruction it reaches: `simplifyInstruction` calls `simplifyOrInst` on an `or`,
whatever its `disjoint` flag, with `MaxRecurse` at `RecursionLimit`, 3. What the core `Oracle` doesn't answer, the
model hands over. -/
def simplifyOrInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .or _ a b => simplifyOrInst o none a b 3
  | _, _ => .null

/-! ### What the matchers say about values -/

namespace Logic

variable {ρ : Env}

theorem ops?_eq {op : BinOp} {t a b : Term w} (h : ops? op t = some (a, b)) : ∃ f, binop? op t = some (f, a, b) := by
  unfold ops? at h
  cases hb : binop? op t with
  | none => simp [hb] at h
  | some p =>
    obtain ⟨f, a', b'⟩ := p
    simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨f, rfl⟩

theorem logicalAnd?_spec {α β : Type} {l : Term 1 → Option α} {r : Term 1 → Option β} {t : Term 1} {x : α} {y : β}
    (h : logicalAnd? l r t = some (x, y)) (hc : t.Consistent ρ) :
    ∃ a b, l a = some x ∧ r b = some y ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      Lemmas.IsLogicalAnd (t.denote ρ) (a.denote ρ) (b.denote ρ) := by
  have both {p q : Term 1} (hp : p.Consistent ρ) (hq : q.Consistent ρ) (hb : logicalAnd?.both l r p q = some (x, y)) :
      (l p = some x ∧ r q = some y) ∨ (l q = some x ∧ r p = some y) := by
    unfold logicalAnd?.both at hb
    split at hb
    · next x' y' h1 h2 => cases hb; exact .inl ⟨h1, h2⟩
    · split at hb
      · next x' y' h1 h2 => cases hb; exact .inr ⟨h1, h2⟩
      · cases hb
  cases t with
  | bin id op f p q =>
    cases op <;> simp only [logicalAnd?, reduceCtorEq] at h
    obtain ⟨hp, hq, hd⟩ := hc
    have hd' : Term.denote ρ (.bin id .and f p q) = Val.and (p.denote ρ) (q.denote ρ) := (ok_inj hd).symm
    rcases both hp hq h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨p, q, h1, h2, hp, hq, .inl hd'⟩
    · exact ⟨q, p, h1, h2, hq, hp, .inr (.inl hd')⟩
  | select id c tv fv =>
    simp only [logicalAnd?] at h
    split at h
    · next hz =>
      obtain ⟨hcc, ht, -, hd⟩ := hc
      have hd' : Term.denote ρ (.select id c tv fv) = select (c.denote ρ) (tv.denote ρ) (some 0#1) := by
        rw [← cst_eq hz]; exact hd.symm
      rcases both hcc ht h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨c, tv, h1, h2, hcc, ht, .inr (.inr (.inl hd'))⟩
      · exact ⟨tv, c, h1, h2, ht, hcc, .inr (.inr (.inr hd'))⟩
    · cases h
  | _ => simp [logicalAnd?] at h

theorem isLogicalOrOf_spec {a b t : Term 1} (h : isLogicalOrOf a b t = true) (hc : t.Consistent ρ) :
    Lemmas.IsLogicalOr (t.denote ρ) (a.denote ρ) (b.denote ρ) := by
  cases t with
  | bin id op f p q =>
    cases op <;> simp only [isLogicalOrOf, Bool.false_eq_true] at h
    obtain ⟨-, -, hd⟩ := hc
    have hd' : Term.denote ρ (.bin id .or f p q) = Val.or (p.denote ρ) (q.denote ρ) f.disjoint := (ok_inj hd).symm
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨f.disjoint, .inl (by rw [hd', specific_denote h1, specific_denote h2])⟩
    · exact .inl ⟨f.disjoint, .inr (by rw [hd', specific_denote h1, specific_denote h2])⟩
  | select id c tv fv =>
    simp only [isLogicalOrOf, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨hone, h⟩ := h
    obtain ⟨-, -, -, hd⟩ := hc
    have hd' : Term.denote ρ (.select id c tv fv) = select (c.denote ρ) (some 1#1) (fv.denote ρ) := by
      rw [← cst_eq hone]; exact hd.symm
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inr (.inl (by rw [hd', specific_denote h1, specific_denote h2]))
    · exact .inr (.inr (by rw [hd', specific_denote h1, specific_denote h2]))
  | _ => simp [isLogicalOrOf] at h

theorem allOnesShift?_shl {t X : Term w} (h : allOnesShift? .shl t = some X) (hc : t.Consistent ρ) :
    X.Consistent ρ ∧ ∃ f1 f2, t.denote ρ = Val.shl (some (BitVec.allOnes w)) (X.denote ρ) f1 f2 := by
  unfold allOnesShift? at h
  split at h
  · next f a x hb =>
    obtain ⟨-, cx, hd⟩ := shl_denote hb hc
    split at h
    · next ha => cases h; exact ⟨cx, _, _, by rw [hd, cst_eq ha]⟩
    · cases h
  · cases h

theorem allOnesShift?_lshr {t X : Term w} (h : allOnesShift? .lshr t = some X) (hc : t.Consistent ρ) :
    X.Consistent ρ ∧ ∃ e, t.denote ρ = Val.lshr (some (BitVec.allOnes w)) (X.denote ρ) e := by
  unfold allOnesShift? at h
  split at h
  · next f a x hb =>
    obtain ⟨-, cx, hd⟩ := lshr_denote hb hc
    split at h
    · next ha => cases h; exact ⟨cx, _, by rw [hd, cst_eq ha]⟩
    · cases h
  · cases h

/-- The `or` of a `shl` of -1 by `X` and an `lshr` of -1 by `Y`, either way round. -/
theorem rotatedAllOnes?_spec {op0 op1 X Y : Term w} (h : rotatedAllOnes? op0 op1 = some (X, Y))
    (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) :
    X.Consistent ρ ∧ Y.Consistent ρ ∧ ∃ f1 f2 e, ∀ d, (Val.or (op0.denote ρ) (op1.denote ρ) d =
      Val.or (Val.shl (some (BitVec.allOnes w)) (X.denote ρ) f1 f2) (Val.lshr (some (BitVec.allOnes w)) (Y.denote ρ) e) d) := by
  unfold rotatedAllOnes? at h
  split at h
  · next X' Y' hx hy =>
    cases h
    obtain ⟨cx, f1, f2, hx⟩ := allOnesShift?_shl hx c0
    obtain ⟨cy, e, hy⟩ := allOnesShift?_lshr hy c1
    exact ⟨cx, cy, f1, f2, e, fun d => by rw [hx, hy]⟩
  · split at h
    · next X' Y' hx hy =>
      cases h
      obtain ⟨cx, f1, f2, hx⟩ := allOnesShift?_shl hx c1
      obtain ⟨cy, e, hy⟩ := allOnesShift?_lshr hy c0
      exact ⟨cx, cy, f1, f2, e, fun d => by rw [hx, hy, Lemmas.Logic.or_comm]⟩
    · cases h

theorem subFrom?_spec {s v : Term w} {c : BitVec w} (h : subFrom? s v = some c) (hc : v.Consistent ρ) :
    ∃ f1 f2, v.denote ρ = Val.sub (some c) (s.denote ρ) f1 f2 := by
  unfold subFrom? at h
  split at h
  · next f c' s' hb =>
    obtain ⟨-, -, hd⟩ := sub_denote' hb hc
    split at h
    · next hs => exact ⟨_, _, by rw [hd, apint_denote h, specific_denote hs]⟩
    · cases h
  · cases h

theorem fshlShl_spec {a b : Term w} (h : fshlShl a b = true) (ca : a.Consistent ρ) (cb : b.Consistent ρ) :
    ∃ x z y : Val w, ∃ f1 f2, a.denote ρ = Val.fshl x z y ∧ b.denote ρ = Val.shl x y f1 f2 := by
  unfold fshlShl at h
  split at h
  · next id x z y =>
    split at h
    · next f p q hb =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨-, -, -, hd⟩ := ca
      obtain ⟨-, -, hdb⟩ := shl_denote hb cb
      exact ⟨x.denote ρ, z.denote ρ, y.denote ρ, f.nuw, f.nsw, Eq.symm (by simpa [Term.denote] using hd),
        by rw [hdb, specific_denote h.1, specific_denote h.2]⟩
    · cases h
  · cases h

theorem fshrLshr_spec {a b : Term w} (h : fshrLshr a b = true) (ca : a.Consistent ρ) (cb : b.Consistent ρ) :
    ∃ z x y : Val w, ∃ e, a.denote ρ = Val.fshr z x y ∧ b.denote ρ = Val.lshr x y e := by
  unfold fshrLshr at h
  split at h
  · next id z x y =>
    split at h
    · next f p q hb =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨-, -, -, hd⟩ := ca
      obtain ⟨-, -, hdb⟩ := lshr_denote hb cb
      exact ⟨z.denote ρ, x.denote ρ, y.denote ρ, f.exact, Eq.symm (by simpa [Term.denote] using hd),
        by rw [hdb, specific_denote h.1, specific_denote h.2]⟩
    · cases h
  · cases h

theorem andConst?_denote {t x : Term w} {c : BitVec w} (h : andConst? t = some (x, c)) (hc : t.Consistent ρ) :
    x.Consistent ρ ∧ t.denote ρ = Val.and (x.denote ρ) (some c) := by
  unfold andConst? shiftConst? at h
  split at h
  · next f x' s hb =>
    obtain ⟨cx, -, hd⟩ := and_denote hb hc
    cases hs : apint s <;> simp only [hs, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨cx, by rw [hd, apint_denote hs]⟩
  · cases h

theorem addOf?_spec {s t n : Term w} (h : addOf? s t = some n) (hc : t.Consistent ρ) :
    ∃ f1 f2, t.denote ρ = Val.add (s.denote ρ) (n.denote ρ) f1 f2 := by
  unfold addOf? at h
  split at h
  · next f p q hb =>
    obtain ⟨-, -, hd⟩ := add_denote hb hc
    split at h
    · next hp => cases h; exact ⟨_, _, by rw [hd, specific_denote hp]⟩
    · split at h
      · next hq => cases h; exact ⟨_, _, by rw [hd, specific_denote hq, Lemmas.add_comm]⟩
      · cases h
  · cases h

theorem maskedValueIsZero_spec {o : Oracle} (ho : o.Sound ρ) {n : Term w} {m : BitVec w}
    (h : maskedValueIsZero o n m = true) : ∀ v, n.denote ρ = some v → v &&& m = 0#w := by
  intro v hv
  have hz := ho.knownZero n v hv
  simp only [maskedValueIsZero, beq_iff_eq] at h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 := congrArg (BitVec.getLsbD · i) hz
  have h2 := congrArg (BitVec.getLsbD · i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero, hi, decide_true, Bool.true_and] at h1 h2 ⊢
  cases hv' : v.getLsbD i <;> cases hm : m.getLsbD i <;> simp_all

end Logic

/-! ### `simplifyOrLogic`'s rewrites, one theorem each -/

theorem allOnes_one : BitVec.allOnes 1 = 1#1 := by decide

/-- `IS.simplifyOrLogic.L2261`: `X | ~X` to -1. -/
theorem simplifyOrLogic.L2261 (ρ : Env) (X Y : Term w) (d : Bool) (cY : Y.Consistent ρ)
    (h : notWith (specific X) Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  obtain ⟨a, ha, -, hd⟩ := notWith_denote h cY
  rw [orSrc_eval, hd, specific_denote ha]
  exact refines_ok (Lemmas.or_not_self_refines _ _)

/-- `IS.simplifyOrLogic.L2265`: `X | ~(X & ?)` to -1. -/
theorem simplifyOrLogic.L2265 (ρ : Env) (X Y : Term w) (d : Bool) (cY : Y.Consistent ρ)
    (h : notWith (chas .and (specific X) (fun _ => true)) Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  obtain ⟨a, ha, ca, hd⟩ := notWith_denote h cY
  obtain ⟨p, q, hp, -, -, -, hda⟩ := chas_and ha ca
  rw [orSrc_eval, hd, hda, specific_denote hp]
  exact refines_ok (Lemmas.or_not_and_refines _ _ _)

/-- `IS.simplifyOrLogic.L2269`: `X | (X & ?)` to `X`. -/
theorem simplifyOrLogic.L2269 (ρ : Env) (X Y : Term w) (d : Bool) (cY : Y.Consistent ρ)
    (h : chas .and (specific X) (fun _ => true) Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.old X).eval ρ) := by
  obtain ⟨p, q, hp, -, -, -, hd⟩ := chas_and h cY
  rw [orSrc_eval, hd, specific_denote hp]
  exact refines_ok (Lemmas.or_and_absorb_refines _ _ _)

/-- `IS.simplifyOrLogic.L2277`: `(A ^ B) | (A | B)` to `A | B`, either way round. -/
theorem simplifyOrLogic.L2277 (ρ : Env) (X Y A B : Term w) (d : Bool) (cX : X.Consistent ρ) (cY : Y.Consistent ρ)
    (h0 : ops? .xor X = some (A, B)) (h1 : isOf .or A B Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.old Y).eval ρ) := by
  obtain ⟨f, hb⟩ := ops?_eq h0
  obtain ⟨-, -, hx⟩ := xor_denote' hb cX
  obtain ⟨d', hy⟩ := isOf_or h1 cY
  rw [orSrc_eval, Repl.eval_old, hx, hy]
  exact refines_ok (Lemmas.or_xor_or_refines _ _ _ _)

/-- `IS.simplifyOrLogic.L2283`: `~(A ^ B) | (A | B)` to -1. -/
theorem simplifyOrLogic.L2283 (ρ : Env) (X Y A B : Term w) (d : Bool) (cX : X.Consistent ρ) (cY : Y.Consistent ρ)
    (h0 : notBind (ops? .xor) X = some (A, B)) (h1 : isOf .or A B Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  obtain ⟨u, hu, cu, hx⟩ := notBind_denote h0 cX
  obtain ⟨f, hb⟩ := ops?_eq hu
  obtain ⟨-, -, hxu⟩ := xor_denote' hb cu
  obtain ⟨d', hy⟩ := isOf_or h1 cY
  rw [orSrc_eval, hx, hxu, hy]
  exact refines_ok (Lemmas.or_not_xor_or_refines _ _ _ _)

/-- `IS.simplifyOrLogic.L2291`: `(A & ~B) | (A ^ B)` to `A ^ B`, in every order. -/
theorem simplifyOrLogic.L2291 (ρ : Env) (X Y A B : Term w) (d : Bool) (cX : X.Consistent ρ) (cY : Y.Consistent ρ)
    (h0 : cbind .and some not? X = some (A, B)) (h1 : isOf .xor A B Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.old Y).eval ρ) := by
  obtain ⟨a, b, ha, hb, -, cb, hx⟩ := cbind_and h0 cX
  cases ha
  obtain ⟨-, hbd⟩ := not?_denote hb cb
  rw [orSrc_eval, Repl.eval_old, hx, hbd, isOf_xor h1 cY]
  exact refines_ok (Lemmas.or_and_not_xor_refines _ _ _)

/-- `IS.simplifyOrLogic.L2299`: `(~A ^ B) | (A & B)` to `~A ^ B`, in every order. -/
theorem simplifyOrLogic.L2299 (ρ : Env) (X Y A B : Term w) (d : Bool) (cX : X.Consistent ρ) (cY : Y.Consistent ρ)
    (h0 : cbind .xor not? some X = some (A, B)) (h1 : isOf .and A B Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.old X).eval ρ) := by
  obtain ⟨a, b, ha, hb, ca, -, hx⟩ := cbind_xor h0 cX
  cases hb
  obtain ⟨-, had⟩ := not?_denote ha ca
  rw [orSrc_eval, Repl.eval_old, hx, had, isOf_and h1 cY]
  exact refines_ok (Lemmas.or_xor_not_and_refines _ _ _)

/-- `IS.simplifyOrLogic.L2307`: `(~A | B) | (A ^ B)` to -1, in every order. -/
theorem simplifyOrLogic.L2307 (ρ : Env) (X Y A B : Term w) (d : Bool) (cX : X.Consistent ρ) (cY : Y.Consistent ρ)
    (h0 : cbind .or not? some X = some (A, B)) (h1 : isOf .xor A B Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  obtain ⟨a, b, d', ha, hb, ca, -, hx⟩ := cbind_or h0 cX
  cases hb
  obtain ⟨-, had⟩ := not?_denote ha ca
  rw [orSrc_eval, hx, had, isOf_xor h1 cY]
  exact refines_ok (Lemmas.or_or_not_xor_refines _ _ _ _)

/-- `IS.simplifyOrLogic.L2317`: `(~A & B) | ~(A | B)` to `~A`, in every order. -/
theorem simplifyOrLogic.L2317 (ρ : Env) (X Y NotA A B : Term w) (d : Bool) (cX : X.Consistent ρ)
    (cY : Y.Consistent ρ) (h0 : cbind .and (fun u => (not? u).map fun a => (u, a)) some X = some ((NotA, A), B))
    (h1 : notWith (isOf .or A B) Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.old NotA).eval ρ) := by
  obtain ⟨u, b, hu, hb, cu, -, hx⟩ := cbind_and h0 cX
  cases hb
  cases hn : not? u with
  | none => simp [hn] at hu
  | some a =>
    simp only [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    obtain ⟨-, hnd⟩ := not?_denote hn cu
    obtain ⟨y, hy, cy, hyd⟩ := notWith_denote h1 cY
    obtain ⟨d', hyo⟩ := isOf_or hy cy
    rw [orSrc_eval, Repl.eval_old, hx, hyd, hyo, hnd]
    exact refines_ok (Lemmas.or_and_not_not_or_refines _ _ _ _)

/-- `IS.simplifyOrLogic.L2324`: `(~A && B) | ~(A || B)` to `~A`, with logical `and` and `or` in every form and order,
on `i1`. -/
theorem simplifyOrLogic.L2324 (ρ : Env) (X Y NotA A B : Term 1) (d : Bool) (cX : X.Consistent ρ)
    (cY : Y.Consistent ρ) (h0 : logicalAnd? (fun u => (not? u).map fun a => (u, a)) some X = some ((NotA, A), B))
    (h1 : notWith (isLogicalOrOf A B) Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.old NotA).eval ρ) := by
  obtain ⟨u, b, hu, hb, cu, -, hx⟩ := logicalAnd?_spec h0 cX
  cases hb
  cases hn : not? u with
  | none => simp [hn] at hu
  | some a =>
    simp only [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    obtain ⟨-, hnd⟩ := not?_denote hn cu
    obtain ⟨y, hy, cy, hyd⟩ := notWith_denote h1 cY
    have hyo := isLogicalOrOf_spec hy cy
    rw [hnd, allOnes_one] at hx
    rw [orSrc_eval, Repl.eval_old, hyd, hnd, allOnes_one]
    exact refines_ok (Lemmas.or_logicalAnd_not_logicalOr_refines _ _ _ _ _ hx hyo)

/-- `IS.simplifyOrLogic.L2332`: `~(A ^ B) | (A & B)` to `~(A ^ B)`. -/
theorem simplifyOrLogic.L2332 (ρ : Env) (X Y A B : Term w) (d : Bool) (cX : X.Consistent ρ) (cY : Y.Consistent ρ)
    (h0 : notBind (ops? .xor) X = some (A, B)) (h1 : isOf .and A B Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.old X).eval ρ) := by
  obtain ⟨u, hu, cu, hx⟩ := notBind_denote h0 cX
  obtain ⟨f, hb⟩ := ops?_eq hu
  obtain ⟨-, -, hxu⟩ := xor_denote' hb cu
  rw [orSrc_eval, Repl.eval_old, hx, hxu, isOf_and h1 cY]
  exact refines_ok (Lemmas.or_not_xor_and_refines _ _ _)

/-- `IS.simplifyOrLogic.L2339`: `~(A & B) | (A ^ B)` to `~(A & B)`. -/
theorem simplifyOrLogic.L2339 (ρ : Env) (X Y A B : Term w) (d : Bool) (cX : X.Consistent ρ) (cY : Y.Consistent ρ)
    (h0 : notBind (ops? .and) X = some (A, B)) (h1 : isOf .xor A B Y = true) :
    Refines ((orSrc X Y d).eval ρ) ((Repl.old X).eval ρ) := by
  obtain ⟨u, hu, cu, hx⟩ := notBind_denote h0 cX
  obtain ⟨f, hb⟩ := ops?_eq hu
  obtain ⟨-, -, hxu⟩ := and_denote hb cu
  rw [orSrc_eval, Repl.eval_old, hx, hxu, isOf_xor h1 cY]
  exact refines_ok (Lemmas.or_not_and_xor_refines _ _ _)

/-- The logical step fires only where `IS.simplifyOrLogic.L2324` does. -/
theorem simplifyOrLogic.logicalStep_sound (ρ : Env) (X Y : Term 1) (d : Bool) (cX : X.Consistent ρ)
    (cY : Y.Consistent ρ) {s : String} {r : Repl 1} (h : Step.fire s r = simplifyOrLogic.logicalStep X Y) :
    Refines ((orSrc X Y d).eval ρ) (r.eval ρ) := by
  unfold simplifyOrLogic.logicalStep at h
  cases h0 : logicalAnd? (fun u => (not? u).map fun a => (u, a)) some X with
  | none => simp [h0] at h
  | some p =>
    obtain ⟨⟨NotA, A⟩, B⟩ := p
    cases h1 : notWith (isLogicalOrOf A B) Y
    · simp [h0, h1] at h
    · simp only [h0, h1, ite_true, Step.fire.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyOrLogic.L2324 ρ X Y NotA A B d cX cY h0 h1

/-- Theorem 1 for `simplifyOrLogic`: what it returns refines the `or`, with or without `disjoint`. -/
theorem simplifyOrLogic.sound (ρ : Env) (X Y : Term w) (d : Bool) (cX : X.Consistent ρ) (cY : Y.Consistent ρ)
    {r : Repl w} (h : run (simplifyOrLogic.steps X Y) = .value r) : Refines ((orSrc X Y d).eval ρ) (r.eval ρ) := by
  refine run_sound (P := fun r => Refines ((orSrc X Y d).eval ρ) (r.eval ρ)) (fun s r hmem => ?_) h
  simp only [simplifyOrLogic.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyOrLogic.L2261 ρ X Y d cY (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyOrLogic.L2265 ρ X Y d cY (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyOrLogic.L2269 ρ X Y d cY (by assumption)
  all_goals first
    | (split at h
       · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
         obtain ⟨-, rfl⟩ := h
         first
           | exact simplifyOrLogic.L2277 ρ X Y _ _ d cX cY (by assumption) (by assumption)
           | exact simplifyOrLogic.L2283 ρ X Y _ _ d cX cY (by assumption) (by assumption)
           | exact simplifyOrLogic.L2291 ρ X Y _ _ d cX cY (by assumption) (by assumption)
           | exact simplifyOrLogic.L2299 ρ X Y _ _ d cX cY (by assumption) (by assumption)
           | exact simplifyOrLogic.L2307 ρ X Y _ _ d cX cY (by assumption) (by assumption)
           | exact simplifyOrLogic.L2317 ρ X Y _ _ _ d cX cY (by assumption) (by assumption)
           | exact simplifyOrLogic.L2332 ρ X Y _ _ d cX cY (by assumption) (by assumption)
           | exact simplifyOrLogic.L2339 ρ X Y _ _ d cX cY (by assumption) (by assumption)
       · simp only [reduceCtorEq] at h)
    | (split at h
       · next hw =>
         subst hw
         simp only [castStep, asI1] at h
         exact simplifyOrLogic.logicalStep_sound ρ X Y d cX cY h
       · simp only [reduceCtorEq] at h)

/-! ### `simplifyOrInst`'s rewrites, one theorem each -/

/-- `IS.simplifyOrInst.L2353`: `X | poison` to poison. -/
theorem simplifyOrInst.L2353 (ρ : Env) (op0 op1 : Term w) (d : Bool) (h : isPoison op1 = true) :
    Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [orSrc_eval, isPoison_denote h, Lemmas.Logic.or_none_right]
  exact refines_ok (Refine.val_none _)

/-- `IS.simplifyOrInst.L2359`: `X | undef` and `X | -1` to -1. Without `undef`, the first is `X | poison`. -/
theorem simplifyOrInst.L2359 (ρ : Env) (op0 op1 : Term w) (d : Bool) (u1 : op1.hasUndef = false)
    (h : (isUndefValue op1 || allOnes op1) = true) :
    Refines ((orSrc op0 op1 d).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [orSrc_eval, isUndefValue_denote h u1, Lemmas.Logic.or_none_right]
    exact refines_ok (Refine.val_none _)
  · rw [orSrc_eval, cst_eq h]
    exact refines_ok (Generic.or_allOnes_refines _ _)

/-- `IS.simplifyOrInst.L2364`: `X | X` and `X | 0` to `X`. -/
theorem simplifyOrInst.L2364 (ρ : Env) (op0 op1 : Term w) (d : Bool) (h : (specific op0 op1 || zero op1) = true) :
    Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old op0).eval ρ) := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [orSrc_eval, specific_denote h]
    exact refines_ok (Generic.or_self_disjoint_refines _ _)
  · rw [orSrc_eval, cst_eq h, Generic.or_zero]
    exact refines_ok (Refine.refl_val _)

/-- `IS.simplifyOrInst.L2387`: `(-1 << X) | (-1 >> Y)` to -1, either way round, where `X = C - Y` or `Y = C - X`
and `C` is at most the width. -/
theorem simplifyOrInst.L2387 (ρ : Env) (op0 op1 X Y : Term w) (c : BitVec w) (d : Bool) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (hr : rotatedAllOnes? op0 op1 = some (X, Y)) (hc : rotateC? X Y = some c)
    (hw : decide (c.toNat ≤ w) = true) :
    Refines ((orSrc op0 op1 d).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  simp only [decide_eq_true_eq] at hw
  obtain ⟨cX, cY, f1, f2, e, hd⟩ := rotatedAllOnes?_spec hr c0 c1
  rw [orSrc_eval, hd]
  refine refines_ok ?_
  unfold rotateC? at hc
  split at hc
  · next c' hs =>
    cases hc
    obtain ⟨f3, f4, hx⟩ := subFrom?_spec hs cX
    rw [hx]
    exact Lemmas.or_shl_lshr_allOnes_sub_left_refines _ _ _ _ _ _ _ _ hw
  · obtain ⟨f3, f4, hy⟩ := subFrom?_spec hc cY
    rw [hy]
    exact Lemmas.or_shl_lshr_allOnes_sub_right_refines _ _ _ _ _ _ _ _ hw

/-- `IS.simplifyOrInst.L2399`: `(fshl X, ?, Y) | (shl X, Y)` to the `fshl`. -/
theorem simplifyOrInst.L2399 (ρ : Env) (op0 op1 : Term w) (d : Bool) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (h : fshlShl op0 op1 = true) : Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old op0).eval ρ) := by
  obtain ⟨x, z, y, f1, f2, h0, h1⟩ := fshlShl_spec h c0 c1
  rw [orSrc_eval, Repl.eval_old, h0, h1]
  exact refines_ok (Lemmas.or_fshl_shl_refines _ _ _ _ _ _)

/-- `IS.simplifyOrInst.L2403`: `(shl X, Y) | (fshl X, ?, Y)` to the `fshl`. -/
theorem simplifyOrInst.L2403 (ρ : Env) (op0 op1 : Term w) (d : Bool) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (h : fshlShl op1 op0 = true) : Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [orSrc_comm]
  exact simplifyOrInst.L2399 ρ op1 op0 d c1 c0 h

/-- `IS.simplifyOrInst.L2410`: `(fshr ?, X, Y) | (lshr X, Y)` to the `fshr`. -/
theorem simplifyOrInst.L2410 (ρ : Env) (op0 op1 : Term w) (d : Bool) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (h : fshrLshr op0 op1 = true) : Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old op0).eval ρ) := by
  obtain ⟨z, x, y, e, h0, h1⟩ := fshrLshr_spec h c0 c1
  rw [orSrc_eval, Repl.eval_old, h0, h1]
  exact refines_ok (Lemmas.or_fshr_lshr_refines _ _ _ _ _)

/-- `IS.simplifyOrInst.L2414`: `(lshr X, Y) | (fshr ?, X, Y)` to the `fshr`. -/
theorem simplifyOrInst.L2414 (ρ : Env) (op0 op1 : Term w) (d : Bool) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (h : fshrLshr op1 op0 = true) : Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [orSrc_comm]
  exact simplifyOrInst.L2410 ρ op1 op0 d c1 c0 h

/-- `IS.simplifyOrInst.L2448`: `A | (A || B)` to `A || B`, on `i1`. -/
theorem simplifyOrInst.L2448 (ρ : Env) (op0 op1 : Term 1) (d : Bool) (c1 : op1.Consistent ρ)
    (h : selectOf false op0 op1 = true) : Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old op1).eval ρ) := by
  obtain ⟨fv, hd⟩ := selectOf_or h c1
  rw [orSrc_eval, Repl.eval_old, hd]
  exact refines_ok (Lemmas.or_select_refines _ _ _)

/-- `IS.simplifyOrInst.L2450`: `(A || B) | A` to `A || B`, on `i1`. -/
theorem simplifyOrInst.L2450 (ρ : Env) (op0 op1 : Term 1) (d : Bool) (c0 : op0.Consistent ρ)
    (h : selectOf false op1 op0 = true) : Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [orSrc_comm]
  exact simplifyOrInst.L2448 ρ op1 op0 d c0 h

/-- `IS.simplifyOrInst.L2475`: `((B + N) & C1) | (B & C2)` to `B + N`, where `C1 = ~C2`, `C2` is a mask of low bits,
and `N` has none of them, from known bits. -/
theorem simplifyOrInst.L2475 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 A B N : Term w) (c1 c2 : BitVec w)
    (d : Bool) (cs0 : op0.Consistent ρ) (cs1 : op1.Consistent ρ)
    (h0 : andConst? op0 = some (A, c1)) (h1 : andConst? op1 = some (B, c2))
    (hc : (c1 == ~~~c2 && isMask c2) = true) (hn : addOf? B A = some N) (hz : maskedValueIsZero o N c2 = true) :
    Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old A).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨rfl, hm⟩ := hc
  obtain ⟨f1, f2, hA⟩ := addOf?_spec hn (andConst?_denote h0 cs0).1
  rw [orSrc_eval, Repl.eval_old, (andConst?_denote h0 cs0).2, (andConst?_denote h1 cs1).2, hA]
  exact refines_ok (Lemmas.or_and_add_and_lowMask_refines _ _ _ _ _ _ (isMask_spec hm)
    (maskedValueIsZero_spec ho hz))

/-- `IS.simplifyOrInst.L2481`: `(A & C1) | ((A + N) & C2)` to `A + N`, where `C1 = ~C2`, `C1` is a mask of low bits,
and `N` has none of them, from known bits. -/
theorem simplifyOrInst.L2481 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 A B N : Term w) (c1 c2 : BitVec w)
    (d : Bool) (cs0 : op0.Consistent ρ) (cs1 : op1.Consistent ρ)
    (h0 : andConst? op0 = some (A, c1)) (h1 : andConst? op1 = some (B, c2))
    (hc : (c1 == ~~~c2 && isMask c1) = true) (hn : addOf? A B = some N) (hz : maskedValueIsZero o N c1 = true) :
    Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old B).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨rfl, hm⟩ := hc
  obtain ⟨f1, f2, hB⟩ := addOf?_spec hn (andConst?_denote h1 cs1).1
  rw [orSrc_eval, Repl.eval_old, (andConst?_denote h0 cs0).2, (andConst?_denote h1 cs1).2, hB, Lemmas.Logic.or_comm]
  have := Lemmas.or_and_add_and_lowMask_refines (A.denote ρ) (N.denote ρ) (~~~c2) f1 f2 d (isMask_spec hm)
    (maskedValueIsZero_spec ho hz)
  rw [BitVec.not_not] at this
  exact refines_ok this

/-- `IS.simplifyOrInst.L2495`: `(A ^ C) | (A ^ ~C)` to -1. -/
theorem simplifyOrInst.L2495 (ρ : Env) (op0 op1 A A' : Term w) (c1 c2 : BitVec w) (d : Bool)
    (cs0 : op0.Consistent ρ) (cs1 : op1.Consistent ρ) (h0 : xorConst? op0 = some (A, c1))
    (h1 : xorConst? op1 = some (A', c2)) (h : (specific A A' && c2 == ~~~c1) = true) :
    Refines ((orSrc op0 op1 d).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hA, rfl⟩ := h
  rw [orSrc_eval, xorConst?_denote h0 cs0, xorConst?_denote h1 cs1, specific_denote hA]
  exact refines_ok (Lemmas.or_xor_xor_not_refines _ _ _)

/-- `IS.simplifyOrInst.L2502`: `A | B` to `A` on `i1`, where `A` false implies `B` false. It rests on
`isImpliedCondition`'s soundness with `LHSIsTrue` false, `Logic.Ext.Sound.impliesFalse`. -/
theorem simplifyOrInst.L2502 (ρ : Env) (e : Ext) (he : e.Sound ρ) (op0 op1 : Term 1) (d : Bool)
    (h : e.impliesFalse op0 op1 = some false) : Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [orSrc_eval, Repl.eval_old]
  exact refines_ok (Lemmas.or_refines_left_of_implies _ _ _ fun ha => by
    simpa using he.impliesFalse op0 op1 false h ha)

/-- `IS.simplifyOrInst.L2505`: `A | B` to true on `i1`, where `A` false implies `B` true. It rests on
`Logic.Ext.Sound.impliesFalse`. -/
theorem simplifyOrInst.L2505 (ρ : Env) (e : Ext) (he : e.Sound ρ) (op0 op1 : Term 1) (d : Bool)
    (h : e.impliesFalse op0 op1 = some true) : Refines ((orSrc op0 op1 d).eval ρ) ((Repl.const 1#1).eval ρ) := by
  rw [orSrc_eval, Repl.eval_const]
  exact refines_ok (Lemmas.or_refines_true_of_implies _ _ _ fun ha => by
    simpa using he.impliesFalse op0 op1 true h ha)

/-- `IS.simplifyOrInst.L2511`: `A | B` to `B` on `i1`, where `B` false implies `A` false. It rests on
`Logic.Ext.Sound.impliesFalse`. -/
theorem simplifyOrInst.L2511 (ρ : Env) (e : Ext) (he : e.Sound ρ) (op0 op1 : Term 1) (d : Bool)
    (h : e.impliesFalse op1 op0 = some false) : Refines ((orSrc op0 op1 d).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [orSrc_comm]
  exact simplifyOrInst.L2502 ρ e he op1 op0 d h

/-- `IS.simplifyOrInst.L2514`: `A | B` to true on `i1`, where `B` false implies `A` true. It rests on
`Logic.Ext.Sound.impliesFalse`. -/
theorem simplifyOrInst.L2514 (ρ : Env) (e : Ext) (he : e.Sound ρ) (op0 op1 : Term 1) (d : Bool)
    (h : e.impliesFalse op1 op0 = some true) : Refines ((orSrc op0 op1 d).eval ρ) ((Repl.const 1#1).eval ρ) := by
  rw [orSrc_comm]
  exact simplifyOrInst.L2505 ρ e he op1 op0 d h

/-! ### The fold -/

/-- The implied conditions' steps fire only where `isImpliedCondition` says so. -/
theorem simplifyOrInst.impliedStep_sound (ρ : Env) (x : Option Ext) (hx : ∀ e, x = some e → e.Sound ρ)
    (isFalse swap : Bool) (op0 op1 : Term 1) (d : Bool) {s : String} {r : Repl 1}
    (h : Step.fire s r = simplifyOrInst.impliedStep x isFalse swap op0 op1) :
    Refines ((orSrc op0 op1 d).eval ρ) (r.eval ρ) := by
  unfold simplifyOrInst.impliedStep at h
  split at h
  · simp only [reduceCtorEq] at h
  · next e =>
    have he := hx e rfl
    cases swap <;> cases isFalse <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;> obtain ⟨-, rfl⟩ := h <;>
      rename_i hi <;> simp only [beq_iff_eq] at hi
    · exact simplifyOrInst.L2505 ρ e he op0 op1 d hi
    · exact simplifyOrInst.L2502 ρ e he op0 op1 d hi
    · exact simplifyOrInst.L2514 ρ e he op0 op1 d hi
    · exact simplifyOrInst.L2511 ρ e he op0 op1 d hi

/-- Every step of `simplifyOrInst` that fires is right, the folds it forwards to included. -/
theorem simplifyOrInst.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (x : Option Ext)
    (hx : ∀ e, x = some e → e.Sound ρ) (op0 op1 : Term w) (n : Nat) (d : Bool) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) :
    ∀ s r, Step.fire s r ∈ simplifyOrInst.steps o x op0 op1 n → Refines ((orSrc op0 op1 d).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyOrInst.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h
  -- X | poison, X | undef, X | -1, X | X, X | 0
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyOrInst.L2353 ρ op0 op1 d (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyOrInst.L2359 ρ op0 op1 d u1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyOrInst.L2364 ρ op0 op1 d (by assumption)
  -- simplifyOrLogic both ways, and simplifyLogicOfAddSub
  · exact simplifyOrLogic.sound ρ op0 op1 d c0 c1 (run_of_forward h.symm)
  · rw [orSrc_comm]
    exact simplifyOrLogic.sound ρ op1 op0 d c1 c0 (run_of_forward h.symm)
  · exact simplifyLogicOfAddSub.sound ρ .or d op0 op1 c0 c1 u0 u1 (.inr (.inl rfl)) (run_of_forward h.symm)
  -- rotated -1
  · split at h
    · next X Y hr =>
      split at h
      · next c hc =>
        split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
        obtain ⟨-, rfl⟩ := h
        exact simplifyOrInst.L2387 ρ op0 op1 X Y c d c0 c1 hr hc (by simpa using (by assumption))
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  -- funnel shifts
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyOrInst.L2399 ρ op0 op1 d c0 c1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyOrInst.L2403 ρ op0 op1 d c0 c1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyOrInst.L2410 ρ op0 op1 d c0 c1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyOrInst.L2414 ρ op0 op1 d c0 c1 (by assumption)
  -- simplifyAndOrWithICmpEq both ways
  · have := simplifyAndOrWithICmpEq.sound ρ x hx false d op0 op1 n c0 (run_of_forward h.symm)
    simpa [andOrSrc] using this
  · rw [orSrc_comm]
    have := simplifyAndOrWithICmpEq.sound ρ x hx false d op1 op0 n c1 (run_of_forward h.symm)
    simpa [andOrSrc] using this
  -- simplifyAndOrOfCmps, isCheckForZeroAndMulWithOverflow, simplifyAssociativeBinOp, expandCommutativeBinOp
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  -- A | (A || B), (A || B) | A
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨-, rfl⟩, hs⟩ := hc
    exact simplifyOrInst.L2448 ρ op0 op1 d c1 hs
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨-, rfl⟩, hs⟩ := hc
    exact simplifyOrInst.L2450 ρ op0 op1 d c0 hs
  -- threadBinOpOverSelect
  · split at h <;> simp only [reduceCtorEq] at h
  -- (A & C1) | (B & C2)
  · split at h
    · next A c1' B c2 h0 h1 =>
      split at h
      · next hc =>
        split at h
        · next N hn =>
          split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
          obtain ⟨-, rfl⟩ := h
          exact simplifyOrInst.L2475 ρ o ho op0 op1 A B N c1' c2 d c0 c1 h0 h1 hc hn (by assumption)
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  · split at h
    · next A c1' B c2 h0 h1 =>
      split at h
      · next hc =>
        split at h
        · next N hn =>
          split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
          obtain ⟨-, rfl⟩ := h
          exact simplifyOrInst.L2481 ρ o ho op0 op1 A B N c1' c2 d c0 c1 h0 h1 hc hn (by assumption)
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  -- threadBinOpOverPHI
  · split at h <;> simp only [reduceCtorEq] at h
  -- (A ^ C) | (A ^ ~C)
  · split at h
    · next A c1' A' c2 h0 h1 =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyOrInst.L2495 ρ op0 op1 A A' c1' c2 d c0 c1 h0 h1 (by assumption)
    · simp only [reduceCtorEq] at h
  -- implied conditions, on i1
  all_goals first
    | (split at h
       · next hw =>
         subst hw
         simp only [castStep, asI1] at h
         exact simplifyOrInst.impliedStep_sound ρ x hx _ _ op0 op1 d h
       · simp only [reduceCtorEq] at h)
    | (unfold domEqStep at h
       repeat' (split at h <;> try simp only [reduceCtorEq] at h))

/-- Theorem 1 for `simplifyOrInst`: every value the model returns refines the `or` it replaces, with or without
`disjoint`, at every width and recursion budget, in every run its operands are consistent with, poison included, where
the `Oracle`'s answers are sound (PASS-01's) and, if a `Logic.Ext` is given, its answers are too: `isImpliedCondition`'s
with `LHSIsTrue` false, and `simplifyWithOpReplaced`'s, the recursive simplifier's. It says nothing about operands that
reach an `undef`. -/
theorem simplifyOrInst.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (x : Option Ext)
    (hx : ∀ e, x = some e → e.Sound ρ) (op0 op1 : Term w) (n : Nat) (d : Bool) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) {r : Repl w}
    (h : simplifyOrInst o x op0 op1 n = .value r) : Refines ((orSrc op0 op1 d).eval ρ) (r.eval ρ) := by
  unfold simplifyOrInst at h
  split at h
  · split at h
    · cases h
    · rw [orSrc_comm]
      exact run_sound (simplifyOrInst.steps_sound ρ o ho x hx op1 op0 n d c1 c0 u1 u0) h
  · exact run_sound (simplifyOrInst.steps_sound ρ o ho x hx op0 op1 n d c0 c1 u0 u1) h

/-- What `onInst` answers for an `or` refines it, whatever its `disjoint` flag. -/
theorem simplifyOrInst.onInst_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (t : Term w) (ht : t.Consistent ρ)
    (hu : t.hasUndef = false) {r : Repl w} (h : simplifyOrInst.onInst o t = .value r) :
    Refines (t.top.eval ρ) (r.eval ρ) := by
  cases t with
  | bin id op f a b =>
    cases op <;> simp only [simplifyOrInst.onInst, reduceCtorEq] at h
    obtain ⟨ca, cb, -⟩ := ht
    simp only [Term.hasUndef, Bool.or_eq_false_iff] at hu
    exact simplifyOrInst.sound ρ o ho none (fun _ h => by cases h) a b 3 f.disjoint ca cb hu.1 hu.2 h
  | _ => simp [simplifyOrInst.onInst] at h

end Peephole.IS
