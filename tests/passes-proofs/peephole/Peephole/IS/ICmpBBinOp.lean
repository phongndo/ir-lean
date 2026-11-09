import Peephole.IS.ICmpBOnLHS

/-! # InstSimplify's `simplifyICmpWithBinOp`, and its rewrites for every input

`simplifyICmpWithBinOp` is at `llvm/lib/Analysis/InstructionSimplify.cpp:3372-3602` at `llvmorg-23.1.3`, with its
helper `trySimplifyICmpWithAdds` at 3347-3367. `simplifyICmpInst` forwards to it. Each step that rewrites carries its ID
from `tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyICmpWithBinOp.L3461` | `0 - zext X <s C` and `!= C` to true, for `C > 0` |
| `IS.simplifyICmpWithBinOp.L3463` | `0 - zext X >=s C` and `== C` to false, for `C > 0` |
| `IS.simplifyICmpWithBinOp.L3467` | `0 - zext X <=s C` to true, for `C >= 0` |
| `IS.simplifyICmpWithBinOp.L3469` | `0 - zext X >s C` to false, for `C >= 0` |
| `IS.simplifyICmpWithBinOp.L3492` | `(C2 << X) == C` to false, for a power of two `C2` and a `C` that isn't one |
| `IS.simplifyICmpWithBinOp.L3494` | `(C2 << X) != C` to true, the same |
| `IS.simplifyICmpWithBinOp.L3503` | `(C << X) >u signmask` to false, for a power of two `C` |
| `IS.simplifyICmpWithBinOp.L3505` | `(C << X) <=u signmask` to true, the same |
| `IS.simplifyICmpWithBinOp.L3543` | `(X op C1) <=u (X op C2)` to true, `op` `and` or `or`, `C1` a subset of `C2` |
| `IS.simplifyICmpWithBinOp.L3545` | `(X op C1) >u (X op C2)` to false, the same |
| `IS.simplifyICmpWithBinOp.L3548` | `(X op C1) <=s (X op C2)` to true, where `C1` and `C2` have one sign |
| `IS.simplifyICmpWithBinOp.L3550` | `(X op C1) >s (X op C2)` to false, the same |

It also forwards to `simplifyICmpWithBinOpOnLHS`, twice, which `ICmpBOnLHS` models and proves, and recurses into
`simplifyICmpInst` with `MaxRecurse - 1` on other operands: `icmp (X + Y), X` on `icmp Y, 0` and the like. Those calls
pass `Pred` on with its `samesign` flag, which says something about the original operands and not about the new ones,
so a sound recursive call doesn't make their answer right: the model delegates them, claiming nothing, and falls
through where they decline.

`simplifyICmpWithBinOp.sound` puts the rest together: every value the model returns refines the compare, at every
width, predicate and `samesign` flag, poison included. Besides the oracle, it assumes the `zext` in `0 - zext X` widens,
as LLVM's verifier makes it (`WellTyped`): `Term` doesn't say so. -/

namespace Peephole.IS.ICmpB

open IRLean

variable {w : Nat}

/-! ### Helpers it calls -/

/-- `dyn_cast<BinaryOperator>(V)` isn't null. -/
def isBin : Term w → Bool
  | .bin .. => true
  | _ => false

/-- A binary operator's opcode. -/
def binOpc : Term w → Option BinOp
  | .bin _ op .. => some op
  | _ => none

/-- A binary operator's flags, read through `Q.IIQ` with `UseInstrInfo` true, as InstSimplify's queries have it. -/
def binFlags : Term w → Flags
  | .bin _ _ f .. => f
  | _ => {}

/-- `NoLHSWrapProblem` for an `add` with flags `f`. -/
def noWrap (p : Pred) (f : Flags) : Bool :=
  isEquality p || (isUnsigned p && f.nuw) || (isSigned p && f.nsw)

/-- `m_NSWAdd(m_Value(), m_Value())`. -/
def nswAdd (t : Term w) : Bool :=
  match binop? .add t with
  | some (f, _, _) => f.nsw
  | none => false

/-- `trySimplifyICmpWithAdds(Pred, LHS, RHS, IIQ)`, with `IIQ.UseInstrInfo` true. -/
def trySimplifyICmpWithAdds (p : Pred) (lhs rhs : Term w) : Bool :=
  isSigned p &&
    (let lr := if nswAdd rhs then (lhs, rhs) else (rhs, lhs)
     nswAdd lr.2 &&
       match binop? .add lr.1, binop? .add lr.2 with
       | some (_, x, c1t), some (_, x', c2t) =>
         match apint c1t, apint c2t with
         | some c1, some c2 => specific x x' && ((c1.sle c2 && !c1.msb) || (c2.sle c1 && c1.sle 0#w))
         | _, _ => false
       | _, _ => false)

/-- `m_Neg(m_ZExt(m_Value()))`: `sub 0, (zext X)`. -/
def negZext : Term w → Bool
  | .bin _ .sub _ c (.zext ..) => zero c
  | _ => false

/-- `m_Shl(m_Power2(), m_Value())`. -/
def shlPow2 (t : Term w) : Bool :=
  match binop? .shl t with
  | some (_, c, _) => power2 c
  | none => false

/-- `m_Shl(m_One(), m_Value())`. -/
def shlOne (t : Term w) : Bool :=
  match binop? .shl t with
  | some (_, c, _) => one c
  | none => false

/-- `APInt::isSubsetOf`: `(A & ~B) == 0`. -/
def subsetOf (a b : BitVec w) : Bool := a &&& ~~~b == 0#w

/-- Both operands `and`, or both `or`, of one operand 0, with `m_APInt` operand 1s `C1` and `C2`: the constants. -/
def andOrPair (lhs rhs : Term w) : Option (BitVec w × BitVec w) :=
  match lhs, rhs with
  | .bin _ lop _ x1 c1t, .bin _ rop _ x2 c2t =>
    if lop = rop ∧ (lop = .and ∨ lop = .or) ∧ specific x1 x2 = true then
      match apint c1t, apint c2t with
      | some c1, some c2 => some (c1, c2)
      | _, _ => none
    else none
  | _, _ => none

/-- The `and`/`or` case under a relational predicate. If `C1` isn't a subset of `C2`, the C++ swaps them and the
predicate, and then goes on if `C1` is a subset of `C2`: the constants and predicate it goes on with. -/
def andOrConsts (p : Pred) (lhs rhs : Term w) : Option (BitVec w × BitVec w × Pred) :=
  if isRelational p then
    match andOrPair lhs rhs with
    | some (c1, c2) =>
      if subsetOf c1 c2 then some (c1, c2, p)
      else if subsetOf c2 c1 then some (c2, c1, swapP p)
      else none
    | none => none
  else none

/-! ### The recursive calls

Each recursive `simplifyICmpInst(Pred, Y, Z, Q, MaxRecurse - 1)` the C++ makes, as the operands it asks about, or
`none` where it doesn't make it. `recStep` makes the call and delegates its answer. -/

/-- `MaxRecurse && (LBO || RBO)`. -/
def addsGuard (lhs rhs : Term w) (n : Nat) : Bool := n != 0 && (isBin lhs || isBin rhs)

/-- `NoLHSWrapProblem` and `NoRHSWrapProblem`: false where the operand isn't an `add`. -/
def addNoWrap (p : Pred) (t : Term w) : Bool :=
  match binop? .add t with
  | some (f, _, _) => noWrap p f
  | none => false

/-- icmp (X+Y), X -> icmp Y, 0 for equalities or if there is no overflow. -/
def addLeftCall (p : Pred) (lhs rhs : Term w) (n : Nat) : Option (Term w × Term w) :=
  match binop? .add lhs with
  | some (_, a, b) =>
    if addsGuard lhs rhs n && (specific rhs a || specific rhs b) && addNoWrap p lhs then
      some (if specific rhs a then b else a, .const 0#w)
    else none
  | none => none

/-- icmp X, (X+Y) -> icmp 0, Y for equalities or if there is no overflow. -/
def addRightCall (p : Pred) (lhs rhs : Term w) (n : Nat) : Option (Term w × Term w) :=
  match binop? .add rhs with
  | some (_, c, d) =>
    if addsGuard lhs rhs n && (specific lhs c || specific lhs d) && addNoWrap p rhs then
      some (.const 0#w, if specific lhs c then d else c)
    else none
  | none => none

/-- icmp (X+Y), (X+Z) -> icmp Y,Z for equalities or if there is no overflow. -/
def addBothCall (p : Pred) (lhs rhs : Term w) (n : Nat) : Option (Term w × Term w) :=
  match binop? .add lhs, binop? .add rhs with
  | some (_, a, b), some (_, c, d) =>
    if addsGuard lhs rhs n && (specific c a || specific d a || specific c b || specific d b) &&
        ((addNoWrap p lhs && addNoWrap p rhs) || trySimplifyICmpWithAdds p lhs rhs) then
      -- A == C: Y = B, Z = D; A == D: Y = B, Z = C; B == C: Y = A, Z = D; else B == D: Y = A, Z = C.
      some (if specific c a then (b, d) else if specific d a then (b, c) else if specific c b then (a, d) else (a, c))
    else none
  | _, _ => none

/-- `LBO->getOperand(0) == RBO->getOperand(0)`, `Shl`: both `nuw`, both `nsw` for a signed predicate, and operand 0
known non-zero. -/
def shlOp0Call (o : Oracle) (p : Pred) (lhs rhs : Term w) : Option (Term w × Term w) :=
  match lhs, rhs with
  | .bin _ .shl fl x1 y1, .bin _ .shl fr x2 y2 =>
    if specific x1 x2 && fl.nuw && fr.nuw && !(isSigned p && !(fl.nsw && fr.nsw)) && o.nonZero x1 then some (y1, y2)
    else none
  | _, _ => none

/-- `LBO->getOperand(1) == RBO->getOperand(1)`: `udiv` and `lshr` both exact under an unsigned or equality predicate,
`sdiv` both exact under an equality, `ashr` both exact, `shl` both `nuw` or both `nsw`, and both `nsw` for a signed
predicate. The step before has made the opcodes equal. -/
def op1Call (p : Pred) (lhs rhs : Term w) : Option (Term w × Term w) :=
  match lhs, rhs with
  | .bin _ lop fl x1 y1, .bin _ _ fr x2 y2 =>
    if specific y1 y2 then
      match lop with
      | .udiv | .lshr => if !isSigned p && fl.exact && fr.exact then some (x1, x2) else none
      | .sdiv => if isEquality p && fl.exact && fr.exact then some (x1, x2) else none
      | .ashr => if fl.exact && fr.exact then some (x1, x2) else none
      | .shl =>
        if (fl.nuw && fr.nuw || fl.nsw && fr.nsw) && !(!(fl.nsw && fr.nsw) && isSigned p) then some (x1, x2)
        else none
      | _ => none
    else none
  | _, _ => none

/-- `if (Value *V = simplifyICmpInst(Pred, Y, Z, Q, MaxRecurse - 1)) return V;`, where the C++ makes the call. -/
def recStep (simp : ICmpSimp) (p : Pred) (s : Bool) (n : Nat) : Option (Term w × Term w) → Step 1
  | some (y, z) => delegUnlessNull "simplifyICmpInst" (simp p s y z (n - 1))
  | none => .next

theorem recStep_ne_fire {simp : ICmpSimp} {p : Pred} {s : Bool} {n : Nat} {c : Option (Term w × Term w)}
    {site : String} {r : Repl 1} : recStep simp p s n c ≠ .fire site r := by
  cases c with
  | none => simp [recStep]
  | some yz => exact delegUnlessNull_ne_fire

/-! ### The model -/

/-- `simplifyICmpWithBinOp(Pred, LHS, RHS, Q, MaxRecurse)`, step by step. `simp` is the recursive `simplifyICmpInst`,
whose answers are delegated. -/
def _root_.Peephole.IS.simplifyICmpWithBinOp.steps (o : Oracle) (simp : ICmpSimp) (p : Pred) (s : Bool) (lhs rhs : Term w)
    (n : Nat) : List (Step 1) :=
  [ -- icmp (X+Y), X -> icmp Y, 0 for equalities or if there is no overflow.
    recStep simp p s n (addLeftCall p lhs rhs n),
    -- icmp X, (X+Y) -> icmp 0, Y for equalities or if there is no overflow.
    recStep simp p s n (addRightCall p lhs rhs n),
    -- icmp (X+Y), (X+Z) -> icmp Y,Z for equalities or if there is no overflow.
    recStep simp p s n (addBothCall p lhs rhs n),
    if isBin lhs then fwd "IS.simplifyICmpWithBinOpOnLHS" (simplifyICmpWithBinOpOnLHS o p lhs rhs n) else .next,
    if isBin rhs then fwd "IS.simplifyICmpWithBinOpOnLHS" (simplifyICmpWithBinOpOnLHS o (swapP p) rhs lhs n)
    else .next,
    -- 0 - (zext X) pred C
    match apint rhs with
    | some c =>
      if !isUnsigned p && negZext lhs && !c.msb && c != 0#w && (p == .slt || p == .ne) then
        .fire "IS.simplifyICmpWithBinOp.L3461" (boolR true)
      else .next
    | none => .next,
    match apint rhs with
    | some c =>
      if !isUnsigned p && negZext lhs && !c.msb && c != 0#w && (p == .sge || p == .eq) then
        .fire "IS.simplifyICmpWithBinOp.L3463" (boolR false)
      else .next
    | none => .next,
    match apint rhs with
    | some c =>
      if !isUnsigned p && negZext lhs && !c.msb && p == .sle then .fire "IS.simplifyICmpWithBinOp.L3467" (boolR true)
      else .next
    | none => .next,
    match apint rhs with
    | some c =>
      if !isUnsigned p && negZext lhs && !c.msb && p == .sgt then .fire "IS.simplifyICmpWithBinOp.L3469" (boolR false)
      else .next
    | none => .next,
    --   If C2 is a power-of-2 and C is not:
    --   (C2 << X) == C --> false
    --   (C2 << X) != C --> true
    match apint rhs with
    | some c =>
      if shlPow2 lhs && !decide c.toNat.isPowerOfTwo &&
          ((binFlags lhs).nsw || (binFlags lhs).nuw || shlOne lhs || c != 0#w) && p == .eq then
        .fire "IS.simplifyICmpWithBinOp.L3492" (boolR false)
      else .next
    | none => .next,
    match apint rhs with
    | some c =>
      if shlPow2 lhs && !decide c.toNat.isPowerOfTwo &&
          ((binFlags lhs).nsw || (binFlags lhs).nuw || shlOne lhs || c != 0#w) && p == .ne then
        .fire "IS.simplifyICmpWithBinOp.L3494" (boolR true)
      else .next
    | none => .next,
    -- If C is a power-of-2:
    -- (C << X)  >u 0x8000 --> false
    -- (C << X) <=u 0x8000 --> true
    if shlPow2 lhs && signMask rhs && p == .ugt then .fire "IS.simplifyICmpWithBinOp.L3503" (boolR false) else .next,
    if shlPow2 lhs && signMask rhs && p == .ule then .fire "IS.simplifyICmpWithBinOp.L3505" (boolR true) else .next,
    if n == 0 || !isBin lhs || !isBin rhs || binOpc lhs != binOpc rhs then .decline else .next,
    -- LBO->getOperand(0) == RBO->getOperand(0), Shl: the recursive call.
    recStep simp p s n (shlOp0Call o p lhs rhs),
    -- If C1 & C2 == C1, A = X and/or C1, B = X and/or C2:
    -- icmp ule A, B -> true
    -- icmp ugt A, B -> false
    -- icmp sle A, B -> true (C1 and C2 are the same sign)
    -- icmp sgt A, B -> false (C1 and C2 are the same sign)
    match andOrConsts p lhs rhs with
    | some (_, _, p') => if p' == .ule then .fire "IS.simplifyICmpWithBinOp.L3543" (boolR true) else .next
    | none => .next,
    match andOrConsts p lhs rhs with
    | some (_, _, p') => if p' == .ugt then .fire "IS.simplifyICmpWithBinOp.L3545" (boolR false) else .next
    | none => .next,
    match andOrConsts p lhs rhs with
    | some (c1, c2, p') =>
      if c1.msb == c2.msb && p' == .sle then .fire "IS.simplifyICmpWithBinOp.L3548" (boolR true) else .next
    | none => .next,
    match andOrConsts p lhs rhs with
    | some (c1, c2, p') =>
      if c1.msb == c2.msb && p' == .sgt then .fire "IS.simplifyICmpWithBinOp.L3550" (boolR false) else .next
    | none => .next,
    -- LBO->getOperand(1) == RBO->getOperand(1): the recursive calls.
    recStep simp p s n (op1Call p lhs rhs) ]

/-- `simplifyICmpWithBinOp(Pred, LHS, RHS, Q, MaxRecurse)`. -/
def _root_.Peephole.IS.simplifyICmpWithBinOp (o : Oracle) (simp : ICmpSimp) (p : Pred) (s : Bool) (lhs rhs : Term w) (n : Nat) :
    Result 1 :=
  run (simplifyICmpWithBinOp.steps o simp p s lhs rhs n)

/-! ### The rewrites, one theorem each -/

theorem zext_some {v : Nat} {a : Val v} {nneg : Bool} {q : BitVec w} (h : Val.zext w a nneg = some q) :
    ∃ y, a = some y ∧ q = y.setWidth w := by
  cases a with
  | none => cases h
  | some y =>
    simp only [Val.zext] at h
    split at h
    · cases h
    · exact ⟨y, rfl, (Option.some.inj h).symm⟩

theorem negZext_val {ρ : Env} {t : Term w} (h : negZext t = true) (hc : t.Consistent ρ) (wt : WellTyped t)
    {x : BitVec w} (hx : t.denote ρ = some x) : ∃ (v : Nat) (y : BitVec v), v < w ∧ x = 0#w - y.setWidth w := by
  unfold negZext at h
  split at h
  · next id f c v zid nneg a =>
    simp only [Term.Consistent] at hc
    obtain ⟨-, ⟨-, hz⟩, he⟩ := hc
    simp only [WellTyped] at wt
    have he' : Val.sub (c.denote ρ) (ρ w zid) f.nuw f.nsw = ρ w id := ok_inj he
    have hx' : ρ w id = some x := hx
    rw [hx', cst_eq h] at he'
    obtain ⟨pc, q, hpc, hq, rfl⟩ := sub_some he'
    cases hpc
    rw [hq] at hz
    obtain ⟨y, -, rfl⟩ := zext_some hz
    exact ⟨v, y, wt.2.1, rfl⟩
  · cases h

/-- `IS.simplifyICmpWithBinOp.L3461`: `0 - zext X <s C` and `!= C` to true, for `C > 0`. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3461 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c : BitVec w)
    (cl : lhs.Consistent ρ) (wt : WellTyped lhs) (hrc : apint rhs = some c)
    (h : (!isUnsigned p && negZext lhs && !c.msb && c != 0#w && (p == .slt || p == .ne)) = true) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR true).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, hz⟩, hm⟩, hc0⟩, hp⟩ := h
  refine refines_bool fun x y hx hy => ?_
  rw [apint_denote hrc] at hy
  cases hy
  obtain ⟨v, z, hv, rfl⟩ := negZext_val hz cl wt hx
  have hlt := Lemmas.zero_sub_setWidth_slt z hv hm (fun h0 => hc0 (BitVec.eq_of_toNat_eq (by simpa using h0)))
  rcases hp with rfl | rfl
  · exact hlt
  · simp only [test, bne_iff_ne, ne_eq]
    intro he
    rw [he] at hlt
    simp [BitVec.slt] at hlt

/-- `IS.simplifyICmpWithBinOp.L3463`: `0 - zext X >=s C` and `== C` to false, for `C > 0`. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3463 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c : BitVec w)
    (cl : lhs.Consistent ρ) (wt : WellTyped lhs) (hrc : apint rhs = some c)
    (h : (!isUnsigned p && negZext lhs && !c.msb && c != 0#w && (p == .sge || p == .eq)) = true) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR false).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, hz⟩, hm⟩, hc0⟩, hp⟩ := h
  refine refines_bool fun x y hx hy => ?_
  rw [apint_denote hrc] at hy
  cases hy
  obtain ⟨v, z, hv, rfl⟩ := negZext_val hz cl wt hx
  have hlt := Lemmas.zero_sub_setWidth_slt z hv hm (fun h0 => hc0 (BitVec.eq_of_toNat_eq (by simpa using h0)))
  rcases hp with rfl | rfl
  · simp only [test, Lemmas.sle_eq_not_slt, hlt]; rfl
  · simp only [test, beq_eq_false_iff_ne, ne_eq]
    intro he
    rw [he] at hlt
    simp [BitVec.slt] at hlt

/-- `IS.simplifyICmpWithBinOp.L3467`: `0 - zext X <=s C` to true, for `C >= 0`. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3467 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c : BitVec w)
    (cl : lhs.Consistent ρ) (wt : WellTyped lhs) (hrc : apint rhs = some c)
    (h : (!isUnsigned p && negZext lhs && !c.msb && p == .sle) = true) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR true).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨-, hz⟩, hm⟩, rfl⟩ := h
  refine refines_bool fun x y hx hy => ?_
  rw [apint_denote hrc] at hy
  cases hy
  obtain ⟨v, z, hv, rfl⟩ := negZext_val hz cl wt hx
  exact Lemmas.zero_sub_setWidth_sle z hv hm

/-- `IS.simplifyICmpWithBinOp.L3469`: `0 - zext X >s C` to false, for `C >= 0`. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3469 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c : BitVec w)
    (cl : lhs.Consistent ρ) (wt : WellTyped lhs) (hrc : apint rhs = some c)
    (h : (!isUnsigned p && negZext lhs && !c.msb && p == .sgt) = true) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR false).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨-, hz⟩, hm⟩, rfl⟩ := h
  refine refines_bool fun x y hx hy => ?_
  rw [apint_denote hrc] at hy
  cases hy
  obtain ⟨v, z, hv, rfl⟩ := negZext_val hz cl wt hx
  have := Lemmas.zero_sub_setWidth_sle z hv hm
  simp only [test, BitVec.slt, BitVec.sle, decide_eq_true_eq, decide_eq_false_iff_not] at this ⊢
  omega

theorem shlPow2_val {ρ : Env} {t : Term w} (h : shlPow2 t = true) (hc : t.Consistent ρ) {x : BitVec w}
    (hx : t.denote ρ = some x) : ∃ c2 q : BitVec w, c2.toNat.isPowerOfTwo ∧ q.toNat < w ∧ x = c2 <<< q.toNat ∧
      ((binFlags t).nuw = true → (c2 <<< q.toNat) >>> q.toNat = c2) ∧
      ((binFlags t).nsw = true → (c2 <<< q.toNat).sshiftRight q.toNat = c2) ∧
      (shlOne t = true → c2 = 1#w) := by
  unfold shlPow2 at h
  split at h
  · next f c sa hb =>
    obtain ⟨id, rfl⟩ := binop?_eq hb
    obtain ⟨c2, hp, hcd⟩ := cst_denote (ρ := ρ) h
    have he := ok_inj (bin_val hb hc)
    rw [hx, hcd] at he
    obtain ⟨pc, q, hpc, -, hq, rfl, hu, hs⟩ := shl_some he
    cases hpc
    refine ⟨c2, q, by simpa using hp, hq, by rw [BitVec.shiftLeft_eq'], ?_, ?_, ?_⟩
    · intro hn
      have := hu hn
      rwa [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'] at this
    · intro hn
      have := hs hn
      rwa [BitVec.shiftLeft_eq', BitVec.sshiftRight'] at this
    · intro h1
      simp only [shlOne, hb] at h1
      have := cst_eq (ρ := ρ) h1
      rw [hcd] at this
      exact Option.some.inj this
  · cases h

theorem shiftLeft_ne_zero {c2 : BitVec w} {k : Nat} (h2 : c2.toNat.isPowerOfTwo) (hk : k < w)
    (hc : ((c2 <<< k) >>> k = c2) ∨ ((c2 <<< k).sshiftRight k = c2) ∨ c2 = 1#w) : c2 <<< k ≠ 0#w := by
  intro h0
  have hne : c2 ≠ 0#w := by
    intro hz
    rw [hz] at h2
    obtain ⟨j, hj⟩ := h2
    have := Nat.two_pow_pos j
    simp at hj
    omega
  rcases hc with hc | hc | hc
  · rw [h0] at hc
    exact hne (by rw [← hc]; simp)
  · rw [h0] at hc
    exact hne (by rw [← hc]; exact BitVec.eq_of_toNat_eq (by simp))
  · subst hc
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this
    have hw : 0 < w := by omega
    simp only [BitVec.toNat_ofNat, Nat.one_mod_two_pow hw, Nat.one_mul, Nat.zero_mod] at this
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)] at this
    have := Nat.two_pow_pos k
    omega

theorem shl_eq_false {ρ : Env} {lhs rhs : Term w} {c : BitVec w} (cl : lhs.Consistent ρ)
    (hrc : apint rhs = some c)
    (h : (shlPow2 lhs && !decide c.toNat.isPowerOfTwo &&
      ((binFlags lhs).nsw || (binFlags lhs).nuw || shlOne lhs || c != 0#w)) = true) :
    ∀ x y, lhs.denote ρ = some x → rhs.denote ρ = some y → (x == y) = false := by
  intro x y hx hy
  rw [apint_denote hrc] at hy
  cases hy
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨hs, hpc⟩, hz⟩ := h
  obtain ⟨c2, q, h2, hq, rfl, hu, hn, h1⟩ := shlPow2_val hs cl hx
  apply Lemmas.shiftLeft_pow2_ne _ h2 hpc
  rcases hz with ((hz | hz) | hz) | hz
  · exact Or.inl (shiftLeft_ne_zero h2 hq (Or.inr (Or.inl (hn hz))))
  · exact Or.inl (shiftLeft_ne_zero h2 hq (Or.inl (hu hz)))
  · exact Or.inl (shiftLeft_ne_zero h2 hq (Or.inr (Or.inr (h1 hz))))
  · exact Or.inr hz

/-- `IS.simplifyICmpWithBinOp.L3492`: `(C2 << X) == C` to false, for a power of two `C2` and a `C` that isn't one,
where the shift is `nsw` or `nuw`, `C2` is 1, or `C` isn't 0. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3492 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c : BitVec w)
    (cl : lhs.Consistent ρ) (hrc : apint rhs = some c)
    (h : (shlPow2 lhs && !decide c.toNat.isPowerOfTwo &&
      ((binFlags lhs).nsw || (binFlags lhs).nuw || shlOne lhs || c != 0#w) && p == .eq) = true) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR false).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h, rfl⟩ := h
  exact refines_bool (shl_eq_false cl hrc h)

/-- `IS.simplifyICmpWithBinOp.L3494`: `(C2 << X) != C` to true, the same. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3494 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c : BitVec w)
    (cl : lhs.Consistent ρ) (hrc : apint rhs = some c)
    (h : (shlPow2 lhs && !decide c.toNat.isPowerOfTwo &&
      ((binFlags lhs).nsw || (binFlags lhs).nuw || shlOne lhs || c != 0#w) && p == .ne) = true) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR true).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h, rfl⟩ := h
  refine refines_bool fun x y hx hy => ?_
  simp only [test, bne, shl_eq_false cl hrc h x y hx hy]; rfl

theorem shl_ule_signMask {ρ : Env} {lhs rhs : Term w} (cl : lhs.Consistent ρ)
    (h : (shlPow2 lhs && signMask rhs) = true) :
    ∀ x y, lhs.denote ρ = some x → rhs.denote ρ = some y → BitVec.ule x y = true := by
  intro x y hx hy
  rw [Bool.and_eq_true] at h
  rw [cst_eq h.2] at hy
  cases hy
  obtain ⟨c2, q, h2, -, rfl, -⟩ := shlPow2_val h.1 cl hx
  exact Lemmas.shiftLeft_pow2_ule_intMin _ h2

/-- `IS.simplifyICmpWithBinOp.L3503`: `(C << X) >u signmask` to false, for a power of two `C`. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3503 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (cl : lhs.Consistent ρ)
    (h : (shlPow2 lhs && signMask rhs && p == .ugt) = true) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR false).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h, rfl⟩ := h
  refine refines_bool fun x y hx hy => ?_
  have := shl_ule_signMask cl h x y hx hy
  simp only [test, BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at this ⊢
  omega

/-- `IS.simplifyICmpWithBinOp.L3505`: `(C << X) <=u signmask` to true, for a power of two `C`. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3505 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (cl : lhs.Consistent ρ)
    (h : (shlPow2 lhs && signMask rhs && p == .ule) = true) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR true).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h, rfl⟩ := h
  exact refines_bool (shl_ule_signMask cl h)

theorem andOr_val {ρ : Env} {t x1 c1t : Term w} {c1 : BitVec w} {op : BinOp} {f : Flags}
    (hop : op = .and ∨ op = .or) (hl : binop? op t = some (f, x1, c1t)) (cl : t.Consistent ρ)
    (hc1 : apint c1t = some c1) {x : BitVec w} (hx : t.denote ρ = some x) :
    ∃ xv, x1.denote ρ = some xv ∧ x = (if op = .and then xv &&& c1 else xv ||| c1) := by
  have he := bin_val hl cl
  rw [hx, apint_denote hc1] at he
  rcases hop with rfl | rfl
  · have he' : Val.and (x1.denote ρ) (some c1) = some x := ok_inj he
    cases hxd : x1.denote ρ with
    | none => rw [hxd] at he'; cases he'
    | some xv =>
      rw [hxd] at he'
      exact ⟨xv, rfl, by simpa [Val.and, Val.map₂] using he'.symm⟩
  · have he' : Val.or (x1.denote ρ) (some c1) f.disjoint = some x := ok_inj he
    obtain ⟨xv, c, hxd, hc, rfl⟩ := or_some he'
    cases hc
    exact ⟨xv, hxd, by simp⟩

theorem andOrPair_val {ρ : Env} {lhs rhs : Term w} {c1 c2 : BitVec w} (h : andOrPair lhs rhs = some (c1, c2))
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) :
    ∀ x y, lhs.denote ρ = some x → rhs.denote ρ = some y →
      ∃ xv, (x = xv &&& c1 ∧ y = xv &&& c2) ∨ (x = xv ||| c1 ∧ y = xv ||| c2) := by
  intro x y hx hy
  unfold andOrPair at h
  split at h
  · next id1 lop f1 x1 c1t id2 rop f2 x2 c2t =>
    split at h
    · next hg =>
      obtain ⟨rfl, hop, hsp⟩ := hg
      split at h
      · next k1 k2 hk1 hk2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hl : binop? lop (.bin id1 lop f1 x1 c1t) = some (f1, x1, c1t) := by simp [binop?]
        have hr : binop? lop (.bin id2 lop f2 x2 c2t) = some (f2, x2, c2t) := by simp [binop?]
        obtain ⟨xv, hxv, rfl⟩ := andOr_val hop hl cl hk1 hx
        obtain ⟨xv', hxv', rfl⟩ := andOr_val hop hr cr hk2 hy
        rw [specific_denote hsp, hxv] at hxv'
        cases hxv'
        refine ⟨xv, ?_⟩
        rcases hop with rfl | rfl
        · exact Or.inl ⟨by simp, by simp⟩
        · exact Or.inr ⟨by simp, by simp⟩
      · cases h
    · cases h
  · cases h

theorem andOr_ule {xv k1 k2 a b : BitVec w} (hs : k1 &&& ~~~k2 = 0#w)
    (hab : (a = xv &&& k1 ∧ b = xv &&& k2) ∨ (a = xv ||| k1 ∧ b = xv ||| k2)) :
    BitVec.ule a b = true ∧ (k1.msb = k2.msb → BitVec.sle a b = true) := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨Lemmas.ule_of_subset (Lemmas.and_subset hs), fun hm => ?_⟩
    rw [Lemmas.sle_eq_ule_of_msb_eq (by simp [BitVec.msb_and, hm])]
    exact Lemmas.ule_of_subset (Lemmas.and_subset hs)
  · refine ⟨Lemmas.ule_of_subset (Lemmas.or_subset hs), fun hm => ?_⟩
    rw [Lemmas.sle_eq_ule_of_msb_eq (by simp [BitVec.msb_or, hm])]
    exact Lemmas.ule_of_subset (Lemmas.or_subset hs)

theorem andOrConsts_val {ρ : Env} {p : Pred} {lhs rhs : Term w} {c1 c2 : BitVec w} {p' : Pred}
    (h : andOrConsts p lhs rhs = some (c1, c2, p')) (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) :
    ∀ x y, lhs.denote ρ = some x → rhs.denote ρ = some y →
      ∃ a b : BitVec w, BitVec.ule a b = true ∧ (c1.msb = c2.msb → BitVec.sle a b = true) ∧
        test p x y = test p' a b := by
  intro x y hx hy
  unfold andOrConsts at h
  split at h
  · split at h
    · next k1 k2 hk =>
      obtain ⟨xv, hab⟩ := andOrPair_val hk cl cr x y hx hy
      split at h
      · next hs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨e1, e2, e3⟩ := h
        subst e1 e2 e3
        obtain ⟨h1, h2⟩ := andOr_ule (by simpa [subsetOf] using hs) hab
        exact ⟨x, y, h1, h2, rfl⟩
      · split at h
        · next hs =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨e1, e2, e3⟩ := h
          subst e1 e2 e3
          have hab' : (y = xv &&& k2 ∧ x = xv &&& k1) ∨ (y = xv ||| k2 ∧ x = xv ||| k1) := by
            rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨h2, h1⟩
            · exact Or.inr ⟨h2, h1⟩
          obtain ⟨h1, h2⟩ := andOr_ule (by simpa [subsetOf] using hs) hab'
          exact ⟨y, x, h1, h2, (test_swap p x y).symm⟩
        · cases h
    · cases h
  · cases h

/-- `IS.simplifyICmpWithBinOp.L3543`: `(X op C1) <=u (X op C2)` to true, for `op` `and` or `or` and `C1` a subset of
`C2`, after the C++'s swap. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3543 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c1 c2 : BitVec w)
    (p' : Pred) (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (hk : andOrConsts p lhs rhs = some (c1, c2, p'))
    (h : (p' == .ule) = true) : Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR true).eval ρ) := by
  rw [beq_iff_eq] at h
  subst h
  refine refines_bool fun x y hx hy => ?_
  obtain ⟨a, b, hab, -, he⟩ := andOrConsts_val hk cl cr x y hx hy
  rw [he]
  exact hab

/-- `IS.simplifyICmpWithBinOp.L3545`: `(X op C1) >u (X op C2)` to false, the same. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3545 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c1 c2 : BitVec w)
    (p' : Pred) (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (hk : andOrConsts p lhs rhs = some (c1, c2, p'))
    (h : (p' == .ugt) = true) : Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR false).eval ρ) := by
  rw [beq_iff_eq] at h
  subst h
  refine refines_bool fun x y hx hy => ?_
  obtain ⟨a, b, hab, -, he⟩ := andOrConsts_val hk cl cr x y hx hy
  rw [he]
  simp only [test, BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at hab ⊢
  omega

/-- `IS.simplifyICmpWithBinOp.L3548`: `(X op C1) <=s (X op C2)` to true, where `C1` and `C2` have one sign. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3548 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c1 c2 : BitVec w)
    (p' : Pred) (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (hk : andOrConsts p lhs rhs = some (c1, c2, p'))
    (h : (c1.msb == c2.msb && p' == .sle) = true) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR true).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  obtain ⟨hm, rfl⟩ := h
  refine refines_bool fun x y hx hy => ?_
  obtain ⟨a, b, -, hab, he⟩ := andOrConsts_val hk cl cr x y hx hy
  rw [he]
  exact hab hm

/-- `IS.simplifyICmpWithBinOp.L3550`: `(X op C1) >s (X op C2)` to false, where `C1` and `C2` have one sign. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.L3550 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c1 c2 : BitVec w)
    (p' : Pred) (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (hk : andOrConsts p lhs rhs = some (c1, c2, p'))
    (h : (c1.msb == c2.msb && p' == .sgt) = true) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR false).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  obtain ⟨hm, rfl⟩ := h
  refine refines_bool fun x y hx hy => ?_
  obtain ⟨a, b, -, hab, he⟩ := andOrConsts_val hk cl cr x y hx hy
  rw [he]
  have := hab hm
  simp only [test, BitVec.slt, BitVec.sle, decide_eq_true_eq, decide_eq_false_iff_not] at this ⊢
  omega

/-! ### The fold -/

/-- Every step of `simplifyICmpWithBinOp` that fires is right. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (simp : ICmpSimp) (p : Pred)
    (s : Bool) (lhs rhs : Term w) (n : Nat) (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ)
    (wt : WellTyped lhs) :
    ∀ site r, Step.fire site r ∈ simplifyICmpWithBinOp.steps o simp p s lhs rhs n →
      Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) := by
  intro site r hmem
  simp only [simplifyICmpWithBinOp.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  -- the three recursive calls
  · exact absurd h.symm recStep_ne_fire
  · exact absurd h.symm recStep_ne_fire
  · exact absurd h.symm recStep_ne_fire
  -- the forwards to simplifyICmpWithBinOpOnLHS
  · split at h
    · exact simplifyICmpWithBinOpOnLHS.sound ρ o ho p s lhs rhs n cl (fwd_fire h.symm)
    · cases h
  · split at h
    · rw [← icmpSrc_swap]
      exact refines_of_plain
        (simplifyICmpWithBinOpOnLHS.sound ρ o ho (swapP p) false rhs lhs n cr (fwd_fire h.symm))
    · cases h
  -- 0 - (zext X) pred C
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOp.L3461 ρ p s lhs rhs _ cl wt (by assumption) (by assumption)
    · cases h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOp.L3463 ρ p s lhs rhs _ cl wt (by assumption) (by assumption)
    · cases h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOp.L3467 ρ p s lhs rhs _ cl wt (by assumption) (by assumption)
    · cases h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOp.L3469 ρ p s lhs rhs _ cl wt (by assumption) (by assumption)
    · cases h
  -- (C2 << X) == C
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOp.L3492 ρ p s lhs rhs _ cl (by assumption) (by assumption)
    · cases h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOp.L3494 ρ p s lhs rhs _ cl (by assumption) (by assumption)
    · cases h
  -- (C << X) against the sign mask
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyICmpWithBinOp.L3503 ρ p s lhs rhs cl (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyICmpWithBinOp.L3505 ρ p s lhs rhs cl (by assumption)
  -- the decline
  · split at h <;> cases h
  -- the recursive call on shl's operand 1
  · exact absurd h.symm recStep_ne_fire
  -- and/or with constants
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOp.L3543 ρ p s lhs rhs _ _ _ cl cr (by assumption) (by assumption)
    · cases h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOp.L3545 ρ p s lhs rhs _ _ _ cl cr (by assumption) (by assumption)
    · cases h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOp.L3548 ρ p s lhs rhs _ _ _ cl cr (by assumption) (by assumption)
    · cases h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOp.L3550 ρ p s lhs rhs _ _ _ cl cr (by assumption) (by assumption)
    · cases h
  -- the recursive calls on operand 0
  · exact absurd h.symm recStep_ne_fire

/-- Theorem 1 for `simplifyICmpWithBinOp`: every value the model returns refines `icmp [samesign] Pred LHS, RHS`, at
every width, predicate, `samesign` flag and recursion budget, in every run the operands are consistent with and the
oracle is sound in, poison included, for whatever the recursive `simplifyICmpInst` answers. It assumes `LHS`'s casts
are well typed. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOp.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (simp : ICmpSimp) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (n : Nat) (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (wt : WellTyped lhs) {r : Repl 1}
    (h : simplifyICmpWithBinOp o simp p s lhs rhs n = .value r) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) :=
  run_sound (simplifyICmpWithBinOp.steps_sound ρ o ho simp p s lhs rhs n cl cr wt) h

end Peephole.IS.ICmpB
