import Peephole.IC.Base
import Peephole.IS.Add
import Peephole.Lemmas.ICAdd

/-! # InstCombine's `foldAddWithConstant`, and its rewrites for every input

`foldAddWithConstant` is at `llvm/lib/Transforms/InstCombine/InstCombineAddSub.cpp:856-1025` at `llvmorg-23.1.3`.
`visitAdd` calls it on an `add` its earlier steps left alone, and goes on to its next step when it answers `nullptr`.
This is its model, step by step in the C++'s order, with each rewrite under its ID from
`tests/llvm_scope/rewrites/instcombine.json`, and a theorem of that name for each:

| ID | Rewrite |
| --- | --- |
| `IC.AddSub.foldAddWithConstant.L874` | `add (sub C1, X), C2` to `sub (C1 + C2), X` |
| `IC.AddSub.foldAddWithConstant.L881` | `add (sub X, Y), -1` to `add (not Y), X`, for a `sub` with one use |
| `IC.AddSub.foldAddWithConstant.L886` | `zext(bool) + C` to `select bool, C + 1, C` |
| `IC.AddSub.foldAddWithConstant.L891` | `sext(bool) + C` to `select bool, C - 1, C` |
| `IC.AddSub.foldAddWithConstant.L902` | `~X + C` to `(C - 1) - X`, `nsw` if the `add` has it and `C - 1` doesn't overflow |
| `IC.AddSub.foldAddWithConstant.L911` | `(X s>> (N - 1)) + 1` to `zext (X > -1)`, for an `ashr` with one use |
| `IC.AddSub.foldAddWithConstant.L924` | `(X | C1) + C` to `X + (C1 + C)` for a disjoint `or` |
| `IC.AddSub.foldAddWithConstant.L930` | `(X | C2) + C` to `(X | C2) ^ C2` where `C2 == -C` |
| `IC.AddSub.foldAddWithConstant.L936` | `X + signmask` to `X | signmask`, disjoint, with `nsw` or `nuw` |
| `IC.AddSub.foldAddWithConstant.L940` | `X + signmask` to `X ^ signmask` |
| `IC.AddSub.foldAddWithConstant.L947` | `add (zext (xor X, signmask)), sext(signmask)` to `sext X` |
| `IC.AddSub.foldAddWithConstant.L952` | `(X ^ signmask) + C` to `X + (signmask ^ C)` |
| `IC.AddSub.foldAddWithConstant.L959` | `(X ^ C2) + C` to `(C2 + C) - X` where `X` has no bit outside `C2` |
| `IC.AddSub.foldAddWithConstant.L976` | `(X ^ C2) + -C2` to `ashr (shl X, S), S`, a sign extension in a register |
| `IC.AddSub.foldAddWithConstant.L989` | `sext(bool) + 1` to `zext (not bool)`, for a `sext` with one use |
| `IC.AddSub.foldAddWithConstant.L997` | `ashr (shl X, N - 1), N - 1` plus 1 to `~X & 1`, for an `ashr` with one use |
| `IC.AddSub.foldAddWithConstant.L1003` | `umax(X, -C) + C` to `usub.sat(X, -C)`, for a `umax` with one use |
| `IC.AddSub.foldAddWithConstant.L1020` | `zext (X + -C) + C` to `zext X` where `X u>= C` |

`L989` and `L997` can't fire: `L891` takes every `sext` of an `i1` plus a constant first, and `L911` every `ashr` by
`N - 1` with one use plus 1. They're modelled, and proved, as the C++ has them.

`L902` is wrong at `i1` on its own: `add nsw (xor %p, true), true` is `true` for `%p = true`, and `sub nsw false, %p`
is poison, since `1` is `-1` there and `C - 1` doesn't overflow. Its theorem holds where the `add` has no `nsw` or isn't
an `i1`, which `visitAdd` makes sure of: `simplifyAddInst`, which it calls first, answers for every `i1` `add`. -/

namespace Peephole.IC

open IRLean

variable {w : Nat}

/-! ### Matchers -/

/-- `m_ZExt(m_Value(X))` where `X` is an `i1`, binding `X`. -/
def zextBool? : Term w → Option (Term 1)
  | @Term.zext v _ _ _ x => if h : v = 1 then some (cast (congrArg Term h) x) else none
  | _ => none

/-- `m_SExt(m_Value(X))` where `X` is an `i1`, binding `X`. -/
def sextBool? : Term w → Option (Term 1)
  | @Term.sext v _ _ x => if h : v = 1 then some (cast (congrArg Term h) x) else none
  | _ => none

/-- `m_ZExt(m_BinOp<op>(m_Value(X), m_APInt(C)))`, binding `X` and `C` at the narrow width. -/
def zextBinConst? (op : BinOp) : Term w → Option ((v : Nat) × Term v × BitVec v)
  | @Term.zext v _ _ _ a =>
    match binop? op a with
    | some (_, x, ct) =>
      match apint ct with
      | some k => some ⟨v, x, k⟩
      | none => none
    | none => none
  | _ => none

/-- `m_Xor(m_Value(X), m_APInt(C2))`, binding `X` and `C2`. Not commutative. -/
def xorConst? (t : Term w) : Option (Term w × BitVec w) :=
  match binop? .xor t with
  | some (_, x, ct) =>
    match apint ct with
    | some k => some (x, k)
    | none => none
  | none => none

/-- `m_AShr(m_Shl(m_Value(X), m_APInt(C2)), m_APInt(C3))`, binding `X`, `C2` and `C3`. -/
def ashrShl? (t : Term w) : Option (Term w × BitVec w × BitVec w) :=
  match binop? .ashr t with
  | some (_, sh, c3t) =>
    match binop? .shl sh, apint c3t with
    | some (_, x, c2t), some c3 =>
      match apint c2t with
      | some c2 => some (x, c2, c3)
      | none => none
    | _, _ => none
  | none => none

/-- The shift of `add (xor X, C2), C`'s sign extension in a register, at `InstCombineAddSub.cpp:966-971`:
`BitWidth - logBase2 - 1` of `C` if it's a power of two, else of `C2` if it is, else 0. -/
def sextShAmt (k c2 : BitVec w) : Nat :=
  if k.toNat.isPowerOfTwo then w - Nat.log2 k.toNat - 1
  else if c2.toNat.isPowerOfTwo then w - Nat.log2 c2.toNat - 1
  else 0

/-- `APInt::getHighBitsSet(BitWidth, n)`: the top `n` bits set. -/
def highBits (w n : Nat) : BitVec w := BitVec.allOnes w <<< (w - n)

/-! ### The model -/

/-- `foldAddWithConstant`'s steps once `C` is `m_APInt(C)`: those after `if (!match(Op1, m_APInt(C))) return
nullptr;`. -/
def foldAddWithConstant.apSteps (c : Ctx) (o : Oracle) (op0 op1 : Term w) (k : BitVec w) (nsw nuw : Bool) :
    List (Step w) :=
  [ -- (X | Op01C) + Op1C --> X + (Op01C + Op1C) iff the `or` is actually an `add`
    match binop? .or op0 with
    | some (f, x, c01) =>
      if f.disjoint && c01.isConstant then
        .fire "IC.AddSub.foldAddWithConstant.L924"
          (.bin .add { nsw := nsw && willNotOverflowSignedAdd c01 k, nuw := nuw } (.old x) (constAdd c01 op1))
      else .next
    | none => .next,
    -- (X | C2) + C --> (X | C2) ^ C2 iff (C2 == -C)
    match binop? .or op0 with
    | some (_, _, c2t) =>
      match apint c2t with
      | some c2 => if c2 = -k then .fire "IC.AddSub.foldAddWithConstant.L930" (.bin .xor {} (.old op0) (.const c2))
        else .next
      | none => .next
    | none => .next,
    -- If wrapping is not allowed, then the addition must set the sign bit:
    -- X + (signmask) --> X | signmask
    if k = BitVec.intMin w && (nsw || nuw) then
      .fire "IC.AddSub.foldAddWithConstant.L936" (.bin .or { disjoint := true } (.old op0) (.old op1))
    else .next,
    -- If wrapping is allowed, then the addition flips the sign bit of LHS:
    -- X + (signmask) --> X ^ signmask
    if k = BitVec.intMin w then .fire "IC.AddSub.foldAddWithConstant.L940" (.bin .xor {} (.old op0) (.old op1))
    else .next,
    -- Is this add the last step in a convoluted sext?
    -- add(zext(xor i16 X, -32768), -32768) --> sext X
    match zextBinConst? .xor op0 with
    | some ⟨v, x, c2⟩ =>
      if c2 = BitVec.intMin v && c2.signExtend w = k then .fire "IC.AddSub.foldAddWithConstant.L947" (.sext (.old x))
      else .next
    | none => .next,
    -- (X ^ signmask) + C --> (X + (signmask ^ C))
    match xorConst? op0 with
    | some (x, c2) =>
      if c2 = BitVec.intMin w then .fire "IC.AddSub.foldAddWithConstant.L952" (.bin .add {} (.old x) (.const (c2 ^^^ k)))
      else .next
    | none => .next,
    -- If X has no bits set other than an xor mask,
    -- xor is equivalent to sub with no borrow between bits:
    -- add (xor X, C2), C --> sub (C2 + C), X
    match xorConst? op0 with
    | some (x, c2) =>
      if (c2 ||| o.knownZero x) = BitVec.allOnes w then
        .fire "IC.AddSub.foldAddWithConstant.L959" (.bin .sub {} (.const (c2 + k)) (.old x))
      else .next
    | none => .next,
    -- Look for a math+logic pattern that corresponds to sext-in-register of a
    -- value with cleared high bits. Convert that into a pair of shifts:
    -- add (xor X, 0x80), 0xF..F80 --> (X << ShAmtC) >>s ShAmtC
    -- add (xor X, 0xF..F80), 0x80 --> (X << ShAmtC) >>s ShAmtC
    match xorConst? op0 with
    | some (x, c2) =>
      if c.oneUse op0 && c2 = -k && sextShAmt k c2 != 0 &&
          (o.knownZero x &&& highBits w (sextShAmt k c2)) = highBits w (sextShAmt k c2) then
        .fire "IC.AddSub.foldAddWithConstant.L976"
          (.bin .ashr {} (shlOf x (BitVec.ofNat w (sextShAmt k c2))) (.const (BitVec.ofNat w (sextShAmt k c2))))
      else .next
    | none => .next,
    -- add (sext i1 X), 1 --> zext (not X)
    if k = 1#w && c.oneUse op0 then
      match sextBool? op0 with
      | some x => .fire "IC.AddSub.foldAddWithConstant.L989" (.zext false (notOf x))
      | none => .next
    else .next,
    -- Shifts and add used to flip and mask off the low bit:
    -- add (ashr (shl i32 X, 31), 31), 1 --> and (not X), 1
    if k = 1#w && c.oneUse op0 then
      match ashrShl? op0 with
      | some (x, c2, c3) =>
        if c2 = c3 && c2.toNat = w - 1 then
          .fire "IC.AddSub.foldAddWithConstant.L997" (.bin .and {} (notOf x) (.const 1#w))
        else .next
      | none => .next
    else .next,
    -- umax(X, C) + -C --> usub.sat(X, C)
    match op0 with
    | .bi _ .umax x d =>
      if c.oneUse op0 && cst (· == -k) d then .fire "IC.AddSub.foldAddWithConstant.L1003" (usubSatOf x (-k))
      else .next
    | _ => .next,
    -- Fold (add (zext (add X, -C)), C) -> (zext X) if X u>= C.
    -- Truncate C to the narrow type to avoid mismatched width comparisons.
    match zextBinConst? .add op0 with
    | some ⟨v, x, ic⟩ =>
      if k.toNat < 2 ^ v && ic = -k.setWidth v &&
          (if k.setWidth v = 1#v then o.nonZero x else BitVec.ule (k.setWidth v) (o.knownOne x)) then
        .fire "IC.AddSub.foldAddWithConstant.L1020" (.zext false (.old x))
      else .next
    | none => .next ]

/-- `foldAddWithConstant(Add)`, step by step, for `add op0, op1` with its flags. Its `return nullptr`s go on to the
rest of `visitAdd`, so they end the list rather than the fold. -/
def foldAddWithConstant.steps (c : Ctx) (o : Oracle) (op0 op1 : Term w) (nsw nuw : Bool) : List (Step w) :=
  -- if (!match(Op1, m_ImmConstant(Op1C))) return nullptr;
  if op1.isConstant then
    [ -- if (Instruction *NV = foldBinOpIntoSelectOrPhi(Add)) return NV;
      if isSelect op0 || c.phi op0 then .delegate "foldBinOpIntoSelectOrPhi" else .next,
      -- if (Instruction *FoldedLogic = foldBinOpSelectBinOp(Add)) return FoldedLogic;
      if isSelect op0 then .delegate "foldBinOpSelectBinOp" else .next,
      -- add (sub C1, X), C2 --> sub (add C1, C2), X
      match binop? .sub op0 with
      | some (_, c1, x) =>
        if c1.isConstant then .fire "IC.AddSub.foldAddWithConstant.L874" (.bin .sub {} (constAdd c1 op1) (.old x))
        else .next
      | none => .next,
      -- add (sub X, Y), -1 --> add (not Y), X
      match binop1? c .sub op0 with
      | some (_, x, y) =>
        if allOnes op1 then .fire "IC.AddSub.foldAddWithConstant.L881" (.bin .add {} (notOf y) (.old x)) else .next
      | none => .next,
      -- zext(bool) + C -> bool ? C + 1 : C
      match zextBool? op0 with
      | some x =>
        .fire "IC.AddSub.foldAddWithConstant.L886" (.select (.old x) (constAdd op1 (.const 1#w)) (.old op1))
      | none => .next,
      -- sext(bool) + C -> bool ? C - 1 : C
      match sextBool? op0 with
      | some x =>
        .fire "IC.AddSub.foldAddWithConstant.L891" (.select (.old x) (constSub op1 (.const 1#w)) (.old op1))
      | none => .next,
      -- ~X + C --> (C-1) - X
      -- ~X + C has NSW and (C-1) won't oveflow => (C-1)-X can have NSW
      match not? op0 with
      | some x =>
        .fire "IC.AddSub.foldAddWithConstant.L902"
          (.bin .sub { nsw := nsw && willNotOverflowSignedSubOne op1 } (constSub op1 (.const 1#w)) (.old x))
      | none => .next,
      -- (iN X s>> (N - 1)) + 1 --> zext (X > -1)
      match binop1? c .ashr op0 with
      | some (_, x, s) =>
        if cst (· == BitVec.ofNat w (w - 1)) s && one op1 then
          .fire "IC.AddSub.foldAddWithConstant.L911" (.zext false (isNotNegOf x))
        else .next
      | none => .next ] ++
    match apint op1 with
    | some k => foldAddWithConstant.apSteps c o op0 op1 k nsw nuw
    | none => []
  else []

end Peephole.IC
