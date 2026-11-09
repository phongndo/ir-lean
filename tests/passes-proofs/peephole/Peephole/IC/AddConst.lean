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

/-- `NarrowC.isOne() ? isKnownNonZero(X, Q) : computeKnownBits(X, &Add).getMinValue().uge(NarrowC)`: what the analyses
know of `X u>= NarrowC`. The least value the known bits allow is the bits known to be one. -/
def knownAtLeast (o : Oracle) {v : Nat} (x : Term v) (n : BitVec v) : Bool :=
  if n = 1#v then o.nonZero x else BitVec.ule n (o.knownOne x)

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
      if k.toNat < 2 ^ v && ic = -k.setWidth v && knownAtLeast o x (k.setWidth v) then
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

/-! ### What a match says about values -/

theorem zextBool?_spec {t : Term w} {x : Term 1} (h : zextBool? t = some x) : ∃ id nneg, t = .zext id nneg x := by
  cases t <;> simp only [zextBool?, reduceCtorEq] at h
  next v id nneg a =>
    split at h
    · next hv => subst hv; simp only [cast_eq, Option.some.injEq] at h; subst h; exact ⟨id, nneg, rfl⟩
    · cases h

theorem sextBool?_spec {t : Term w} {x : Term 1} (h : sextBool? t = some x) : ∃ id, t = .sext id x := by
  cases t <;> simp only [sextBool?, reduceCtorEq] at h
  next v id a =>
    split at h
    · next hv => subst hv; simp only [cast_eq, Option.some.injEq] at h; subst h; exact ⟨id, rfl⟩
    · cases h

theorem zextBinConst?_spec {op : BinOp} {t : Term w} {v : Nat} {x : Term v} {k : BitVec v}
    (h : zextBinConst? op t = some ⟨v, x, k⟩) :
    ∃ id nneg a f ct, t = .zext id nneg a ∧ binop? op a = some (f, x, ct) ∧ apint ct = some k := by
  cases t <;> simp only [zextBinConst?, reduceCtorEq] at h
  next v' id nneg a =>
    split at h
    · next f x' ct hb =>
      split at h
      · next k' hk =>
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        simp only [heq_eq_eq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨id, nneg, a, f, ct, rfl, hb, hk⟩
      · cases h
    · cases h

theorem xorConst?_spec {t x : Term w} {k : BitVec w} (h : xorConst? t = some (x, k)) :
    ∃ f ct, binop? .xor t = some (f, x, ct) ∧ apint ct = some k := by
  unfold xorConst? at h
  split at h
  · next f x' ct hb =>
    split at h
    · next k' hk =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨f, ct, hb, hk⟩
    · cases h
  · cases h

theorem ashrShl?_spec {t x : Term w} {c2 c3 : BitVec w} (h : ashrShl? t = some (x, c2, c3)) :
    ∃ f g sh c2t c3t, binop? .ashr t = some (f, sh, c3t) ∧ binop? .shl sh = some (g, x, c2t) ∧
      apint c2t = some c2 ∧ apint c3t = some c3 := by
  unfold ashrShl? at h
  split at h
  · next f sh c3t ha =>
    split at h
    · next g x' c2t c3' hs h3 =>
      split at h
      · next c2' h2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨f, g, sh, c2t, c3t, ha, hs, h2, h3⟩
      · cases h
    · cases h
  · cases h

/-- What a matched binary operator's value is, and that its operands are consistent and have no `undef`. -/
theorem bin_facts {ρ : Env} {op : BinOp} {t a b : Term w} {f : Flags} (h : binop? op t = some (f, a, b))
    (hc : t.Consistent ρ) (hu : t.hasUndef = false) :
    op.eval f (a.denote ρ) (b.denote ρ) = Outcome.ok (t.denote ρ) ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      a.hasUndef = false ∧ b.hasUndef = false := by
  obtain ⟨ca, cb, he⟩ := binop?_consistent h hc
  obtain ⟨ua, ub⟩ := binop?_noUndef h hu
  exact ⟨he, ca, cb, ua, ub⟩

theorem bin_denote {ρ : Env} {op : BinOp} {t a b : Term w} {f : Flags} (h : binop? op t = some (f, a, b))
    (hc : t.Consistent ρ) {r : Val w} (he : op.eval f (a.denote ρ) (b.denote ρ) = Outcome.ok r) : t.denote ρ = r :=
  (ok_inj ((binop?_consistent h hc).2.2.symm.trans he))

theorem const_of_apint {t : Term w} {k : BitVec w} (h : apint t = some k) : t = .const k := by
  cases t <;> simp_all [apint]

/-- A constant with no `undef` is a `ConstantInt` or poison. -/
theorem isConstant_cases {t : Term w} (h : t.isConstant = true) (hu : t.hasUndef = false) :
    (∃ k, t = .const k) ∨ t = .poison := by
  cases t <;> simp_all [Term.isConstant, Term.hasUndef]

/-! ### The rewrites, one theorem each -/

/-- `IC.AddSub.foldAddWithConstant.L874`: `add (sub C1, X), C2` to `sub (C1 + C2), X`. -/
theorem foldAddWithConstant.L874 (ρ : Env) (op0 op1 c1 x : Term w) (f : Flags) (nsw nuw : Bool)
    (c0 : op0.Consistent ρ) (h : binop? .sub op0 = some (f, c1, x)) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) ((Repl.bin .sub {} (constAdd c1 op1) (.old x)).eval ρ) := by
  refine refines_of_eval (IS.addSrc_eval ρ op0 op1 nsw nuw) (by rw [eval_bin, constAdd_eval]; rfl) ?_
  rw [IS.sub_denote h c0]
  exact Lemmas.add_sub_left_refines _ _ _ _ _ _ _

/-- `IC.AddSub.foldAddWithConstant.L881`: `add (sub X, Y), -1` to `add (not Y), X`. -/
theorem foldAddWithConstant.L881 (ρ : Env) (op0 op1 x y : Term w) (f : Flags) (nsw nuw : Bool)
    (c0 : op0.Consistent ρ) (h : binop? .sub op0 = some (f, x, y)) (hk : allOnes op1 = true) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) ((Repl.bin .add {} (notOf y) (.old x)).eval ρ) := by
  refine refines_of_eval (IS.addSrc_eval ρ op0 op1 nsw nuw) (by rw [eval_bin, notOf_eval]; rfl) ?_
  rw [IS.sub_denote h c0, IS.cst_eq hk]
  exact Lemmas.add_sub_allOnes_refines _ _ _ _ _ _

/-- `IC.AddSub.foldAddWithConstant.L886`: `zext(bool) + C` to `select bool, C + 1, C`. -/
theorem foldAddWithConstant.L886 (ρ : Env) (op0 op1 : Term w) (x : Term 1) (nsw nuw : Bool)
    (c0 : op0.Consistent ρ) (h : zextBool? op0 = some x) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ)
      ((Repl.select (.old x) (constAdd op1 (.const 1#w)) (.old op1)).eval ρ) := by
  obtain ⟨id, nneg, rfl⟩ := zextBool?_spec h
  refine refines_of_eval (IS.addSrc_eval ρ _ op1 nsw nuw) (by rw [eval_select, constAdd_eval]; rfl) ?_
  have hd : (Term.zext (w := w) id nneg x).denote ρ = Val.zext w (x.denote ρ) nneg := c0.2.symm
  rw [hd]
  exact Lemmas.add_zext_bool_refines _ _ _ _ _

/-- `IC.AddSub.foldAddWithConstant.L891`: `sext(bool) + C` to `select bool, C - 1, C`. -/
theorem foldAddWithConstant.L891 (ρ : Env) (op0 op1 : Term w) (x : Term 1) (nsw nuw : Bool)
    (c0 : op0.Consistent ρ) (h : sextBool? op0 = some x) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ)
      ((Repl.select (.old x) (constSub op1 (.const 1#w)) (.old op1)).eval ρ) := by
  obtain ⟨id, rfl⟩ := sextBool?_spec h
  refine refines_of_eval (IS.addSrc_eval ρ _ op1 nsw nuw) (by rw [eval_select, constSub_eval]; rfl) ?_
  have hd : (Term.sext (w := w) id x).denote ρ = Val.sext w (x.denote ρ) := c0.2.symm
  rw [hd]
  exact Lemmas.add_sext_bool_refines _ _ _ _

/-- `m_Not(m_Value(X))` on a consistent operand: its value is `X`'s with every bit flipped. -/
theorem not?_denote {ρ : Env} {t x : Term w} (h : not? t = some x) (hc : t.Consistent ρ) :
    t.denote ρ = Val.xor (x.denote ρ) (some (BitVec.allOnes w)) := by
  unfold not? at h
  split at h
  · next f a b hb =>
    rw [IS.xor_denote hb hc]
    split at h
    · next ha => cases h; rw [IS.cst_eq ha, Lemmas.xor_comm]
    · split at h
      · next hb' => cases h; rw [IS.cst_eq hb']
      · cases h
  · cases h

/-- `IC.AddSub.foldAddWithConstant.L902`: `~X + C` to `(C - 1) - X`, `nsw` if the `add` has it and `C - 1` doesn't
overflow. At `i1` this is wrong with `nsw`, so the theorem assumes the `add` isn't an `i1` or has no `nsw`, which
`visitAdd.sound` shows: `simplifyAddInst` answers for every `i1` `add` first. -/
theorem foldAddWithConstant.L902 (ρ : Env) (op0 op1 x : Term w) (nsw nuw : Bool) (c0 : op0.Consistent ρ)
    (u1 : op1.hasUndef = false) (hc : op1.isConstant = true) (hw : w ≠ 1 ∨ nsw = false) (h : not? op0 = some x) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ)
      ((Repl.bin .sub { nsw := nsw && willNotOverflowSignedSubOne op1 } (constSub op1 (.const 1#w)) (.old x)).eval ρ) := by
  rcases isConstant_cases hc u1 with ⟨k, rfl⟩ | rfl
  · refine refines_of_eval (IS.addSrc_eval ρ op0 _ nsw nuw) (by rw [eval_bin, constSub_eval]; rfl) ?_
    rw [not?_denote h c0]
    exact Lemmas.add_not_refines _ k nuw nsw hw
  · refine refines_of_eval (IS.addSrc_eval ρ op0 _ nsw nuw) (by rw [eval_bin, constSub_eval]; rfl) ?_
    rw [show (Term.poison : Term w).denote ρ = none from rfl, Lemmas.add_none_right]
    exact Refine.val_none _

/-- `IC.AddSub.foldAddWithConstant.L911`: `(X s>> (N - 1)) + 1` to `zext (X > -1)`. -/
theorem foldAddWithConstant.L911 (ρ : Env) (op0 op1 x s : Term w) (f : Flags) (nsw nuw : Bool)
    (c0 : op0.Consistent ρ) (u0 : op0.hasUndef = false) (h : binop? .ashr op0 = some (f, x, s))
    (hs : cst (· == BitVec.ofNat w (w - 1)) s = true) (h1 : one op1 = true) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) ((Repl.zext false (isNotNegOf x)).eval ρ) := by
  obtain ⟨he, -, -, ux, -⟩ := bin_facts h c0 u0
  refine refines_of_eval (IS.addSrc_eval ρ op0 op1 nsw nuw) (by rw [eval_zext, isNotNegOf_eval ρ x ux]; rfl) ?_
  rw [IS.cst_eq hs] at he
  rw [← ok_inj he, IS.cst_eq h1]
  exact Lemmas.add_ashr_sign_one_refines _ _ _ _

/-- `IC.AddSub.foldAddWithConstant.L924`: `(X | C1) + C` to `X + (C1 + C)` for a disjoint `or`. -/
theorem foldAddWithConstant.L924 (ρ : Env) (op0 op1 x c01 : Term w) (f : Flags) (k : BitVec w) (nsw nuw : Bool)
    (c0 : op0.Consistent ρ) (u0 : op0.hasUndef = false) (h : binop? .or op0 = some (f, x, c01))
    (hd : f.disjoint = true) (hc : c01.isConstant = true) (hk : apint op1 = some k) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ)
      ((Repl.bin .add { nsw := nsw && willNotOverflowSignedAdd c01 k, nuw := nuw } (.old x) (constAdd c01 op1)).eval ρ) := by
  obtain ⟨he, -, -, -, uc⟩ := bin_facts h c0 u0
  obtain rfl := const_of_apint hk
  rcases isConstant_cases hc uc with ⟨c1, rfl⟩ | rfl
  · refine refines_of_eval (IS.addSrc_eval ρ op0 _ nsw nuw) (by rw [eval_bin, constAdd_eval]; rfl) ?_
    rw [← ok_inj he]
    simp only [Term.denote, BinOp.eval, hd]
    exact Lemmas.add_or_disjoint_refines _ c1 k nuw nsw
  · refine refines_of_eval (IS.addSrc_eval ρ op0 _ nsw nuw) (by rw [eval_bin, constAdd_eval]; rfl) ?_
    rw [← ok_inj he]
    have : Val.or (x.denote ρ) none f.disjoint = none := by cases x.denote ρ <;> rfl
    change Refines (Val.add (Val.or (x.denote ρ) none f.disjoint) (some k) nuw nsw) _
    rw [this]
    exact Refine.val_none _

/-- `IC.AddSub.foldAddWithConstant.L930`: `(X | C2) + C` to `(X | C2) ^ C2` where `C2 == -C`. -/
theorem foldAddWithConstant.L930 (ρ : Env) (op0 op1 x c2t : Term w) (f : Flags) (k c2 : BitVec w) (nsw nuw : Bool)
    (c0 : op0.Consistent ρ) (h : binop? .or op0 = some (f, x, c2t)) (h2 : apint c2t = some c2) (he : c2 = -k)
    (hk : apint op1 = some k) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) ((Repl.bin .xor {} (.old op0) (.const c2)).eval ρ) := by
  obtain rfl := const_of_apint hk
  obtain rfl := const_of_apint h2
  subst he
  refine refines_of_eval (IS.addSrc_eval ρ op0 _ nsw nuw) (by rw [eval_bin]; rfl) ?_
  have hd : op0.denote ρ = Val.or (x.denote ρ) (some (-k)) f.disjoint :=
    (ok_inj ((binop?_consistent h c0).2.2)).symm
  rw [hd]
  exact Lemmas.add_or_neg_refines _ k _ _ _

/-- `IC.AddSub.foldAddWithConstant.L936`: `X + signmask` to `X | signmask`, disjoint, with `nsw` or `nuw`. -/
theorem foldAddWithConstant.L936 (ρ : Env) (op0 op1 : Term w) (nsw nuw : Bool)
    (hk : apint op1 = some (BitVec.intMin w)) (hf : (nsw || nuw) = true) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ)
      ((Repl.bin .or { disjoint := true } (.old op0) (.old op1)).eval ρ) := by
  obtain rfl := const_of_apint hk
  refine refines_of_eval (IS.addSrc_eval ρ op0 _ nsw nuw) (by rw [eval_bin]; rfl) ?_
  exact Lemmas.add_signMask_disjoint_refines _ _ _ (by rw [Bool.or_comm]; exact hf)

/-- `IC.AddSub.foldAddWithConstant.L940`: `X + signmask` to `X ^ signmask`. -/
theorem foldAddWithConstant.L940 (ρ : Env) (op0 op1 : Term w) (nsw nuw : Bool)
    (hk : apint op1 = some (BitVec.intMin w)) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) ((Repl.bin .xor {} (.old op0) (.old op1)).eval ρ) := by
  obtain rfl := const_of_apint hk
  refine refines_of_eval (IS.addSrc_eval ρ op0 _ nsw nuw) (by rw [eval_bin]; rfl) ?_
  exact Lemmas.add_signMask_xor_refines _ _ _

/-- `IC.AddSub.foldAddWithConstant.L952`: `(X ^ signmask) + C` to `X + (signmask ^ C)`. -/
theorem foldAddWithConstant.L952 (ρ : Env) (op0 op1 x : Term w) (k : BitVec w) (nsw nuw : Bool)
    (c0 : op0.Consistent ρ) (h : xorConst? op0 = some (x, BitVec.intMin w)) (hk : apint op1 = some k) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ)
      ((Repl.bin .add {} (.old x) (.const (BitVec.intMin w ^^^ k))).eval ρ) := by
  obtain rfl := const_of_apint hk
  obtain ⟨f, ct, hb, hc⟩ := xorConst?_spec h
  obtain rfl := const_of_apint hc
  refine refines_of_eval (IS.addSrc_eval ρ op0 _ nsw nuw) (by rw [eval_bin]; rfl) ?_
  rw [IS.xor_denote hb c0]
  exact Lemmas.add_xor_signMask_const_refines _ _ _ _

/-- `IC.AddSub.foldAddWithConstant.L959`: `(X ^ C2) + C` to `(C2 + C) - X`, where `computeKnownBits` knows every
bit of `X` outside `C2` is zero. -/
theorem foldAddWithConstant.L959 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 x : Term w) (k c2 : BitVec w)
    (nsw nuw : Bool) (c0 : op0.Consistent ρ) (h : xorConst? op0 = some (x, c2))
    (hz : (c2 ||| o.knownZero x) = BitVec.allOnes w) (hk : apint op1 = some k) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) ((Repl.bin .sub {} (.const (c2 + k)) (.old x)).eval ρ) := by
  obtain rfl := const_of_apint hk
  obtain ⟨f, ct, hb, hc⟩ := xorConst?_spec h
  obtain rfl := const_of_apint hc
  refine refines_of_eval (IS.addSrc_eval ρ op0 _ nsw nuw) (by rw [eval_bin]; rfl) ?_
  rw [IS.xor_denote hb c0]
  cases hx : x.denote ρ with
  | none => simp [Val.xor, Val.map₂, Val.add, Refines, Refine.le]
  | some xv =>
    have hkz := ho.knownZero x xv hx
    have hm : xv &&& ~~~c2 = 0#w := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have h1 := congrArg (·.getLsbD i) hkz
      have h2 := congrArg (·.getLsbD i) hz
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, BitVec.getLsbD_or, BitVec.getLsbD_allOnes, hi,
        decide_true] at h1 h2
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and, BitVec.getLsbD_zero]
      cases hxi : xv.getLsbD i <;> cases hci : c2.getLsbD i <;> simp_all
    simp only [Val.xor, Val.map₂]
    exact Lemmas.add_xor_mask_refines hm k nuw nsw

/-- `IC.AddSub.foldAddWithConstant.L989`: `sext(bool) + 1` to `zext (not bool)`. -/
theorem foldAddWithConstant.L989 (ρ : Env) (op0 op1 : Term w) (x : Term 1) (nsw nuw : Bool)
    (c0 : op0.Consistent ρ) (h : sextBool? op0 = some x) (hk : apint op1 = some 1#w) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) ((Repl.zext false (notOf x)).eval ρ) := by
  obtain rfl := const_of_apint hk
  obtain ⟨id, rfl⟩ := sextBool?_spec h
  refine refines_of_eval (IS.addSrc_eval ρ _ _ nsw nuw) (by rw [eval_zext, notOf_eval]; rfl) ?_
  have hd : (Term.sext (w := w) id x).denote ρ = Val.sext w (x.denote ρ) := c0.2.symm
  rw [hd]
  exact Lemmas.add_sext_bool_one_refines _ _ _

/-- `IC.AddSub.foldAddWithConstant.L997`: `ashr (shl X, N - 1), N - 1` plus 1 to `~X & 1`. -/
theorem foldAddWithConstant.L997 (ρ : Env) (op0 op1 x : Term w) (c2 c3 : BitVec w) (nsw nuw : Bool)
    (c0 : op0.Consistent ρ) (h : ashrShl? op0 = some (x, c2, c3)) (he : c2 = c3) (hn : c2.toNat = w - 1)
    (hk : apint op1 = some 1#w) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) ((Repl.bin .and {} (notOf x) (.const 1#w)).eval ρ) := by
  obtain rfl := const_of_apint hk
  obtain ⟨f, g, sh, c2t, c3t, ha, hs, h2, h3⟩ := ashrShl?_spec h
  obtain rfl := const_of_apint h2
  obtain rfl := const_of_apint h3
  subst he
  have hc2 : c2 = BitVec.ofNat w (w - 1) := by
    apply BitVec.eq_of_toNat_eq; rw [hn, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := @Nat.lt_two_pow_self w; omega)).symm
  subst hc2
  refine refines_of_eval (IS.addSrc_eval ρ op0 _ nsw nuw) (by rw [eval_bin, notOf_eval]; rfl) ?_
  have csh := (binop?_consistent ha c0).1
  have hsh : sh.denote ρ = Val.shl (x.denote ρ) (some (BitVec.ofNat w (w - 1))) g.nuw g.nsw :=
    (ok_inj ((binop?_consistent hs csh).2.2)).symm
  have hd : op0.denote ρ = Val.ashr (sh.denote ρ) (some (BitVec.ofNat w (w - 1))) f.exact :=
    (ok_inj ((binop?_consistent ha c0).2.2)).symm
  rw [hd, hsh]
  exact Lemmas.add_ashr_shl_sign_one_refines _ _ _ _ _ _

/-- `IC.AddSub.foldAddWithConstant.L1003`: `umax(X, -C) + C` to `usub.sat(X, -C)`. -/
theorem foldAddWithConstant.L1003 (ρ : Env) (op0 op1 x d : Term w) (id : Nat) (k : BitVec w) (nsw nuw : Bool)
    (c0 : op0.Consistent ρ) (u0 : op0.hasUndef = false) (h0 : op0 = .bi id .umax x d)
    (hd : cst (· == -k) d = true) (hk : apint op1 = some k) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) ((usubSatOf x (-k)).eval ρ) := by
  obtain rfl := const_of_apint hk
  subst h0
  have ux : x.hasUndef = false := by simp_all [Term.hasUndef]
  refine refines_of_eval (IS.addSrc_eval ρ _ _ nsw nuw) (usubSatOf_eval ρ x (-k) ux) ?_
  have hb : (Term.bi id BinIntr.umax x d).denote ρ = Val.umax (x.denote ρ) (d.denote ρ) := c0.2.2.symm
  rw [hb, IS.cst_eq hd]
  exact Lemmas.add_umax_refines _ _ _ _

/-- `IC.AddSub.foldAddWithConstant.L1020`: `zext (X + -C) + C` to `zext X`, where `X u>= C` by `isKnownNonZero` for
`C = 1` and by the least value `computeKnownBits` allows otherwise. -/
theorem foldAddWithConstant.L1020 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 : Term w) {v : Nat}
    (x : Term v) (ic k : BitVec v) (k' : BitVec w) (nsw nuw : Bool) (c0 : op0.Consistent ρ)
    (h : zextBinConst? .add op0 = some ⟨v, x, ic⟩) (hk : apint op1 = some k')
    (hfit : k'.toNat < 2 ^ v) (hkv : k = k'.setWidth v) (hic : ic = -k)
    (hx : knownAtLeast o x k = true) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) ((Repl.zext false (.old x)).eval ρ) := by
  obtain rfl := const_of_apint hk
  obtain ⟨id, nneg, a, f, ct, rfl, hb, hc⟩ := zextBinConst?_spec h
  obtain rfl := const_of_apint hc
  subst hic
  refine refines_of_eval (IS.addSrc_eval ρ _ _ nsw nuw) (by rw [eval_zext]; rfl) ?_
  have hz : (Term.zext (w := w) id nneg a).denote ρ = Val.zext w (a.denote ρ) nneg := c0.2.symm
  have ha : a.denote ρ = Val.add (x.denote ρ) (some (-k)) f.nuw f.nsw :=
    (ok_inj ((binop?_consistent hb c0.1).2.2)).symm
  have hk' : k' = k.setWidth w := by
    subst hkv
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt hfit, Nat.mod_eq_of_lt k'.isLt]
  rw [hz, ha, hk']
  cases hxd : x.denote ρ with
  | none => simp [Val.add, Val.zext, Refines, Refine.le]
  | some xv =>
    have hle : k.toNat ≤ xv.toNat := by
      unfold knownAtLeast at hx
      split at hx
      · next h1 =>
        subst h1
        have := ho.nonZero x xv hx hxd
        rcases Nat.eq_zero_or_pos v with rfl | hv
        · simp
        · have : xv.toNat ≠ 0 := fun h0 => this (BitVec.eq_of_toNat_eq (by simpa using h0))
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
          omega
      · have h1 := ho.knownOne x xv hxd
        have h2 := Lemmas.le_of_and_eq h1
        simp only [BitVec.ule, decide_eq_true_eq] at hx
        omega
    exact Lemmas.add_zext_add_neg_refines hle _ _ _ _ _

/-- `IC.AddSub.foldAddWithConstant.L947`: `add (zext (xor X, signmask)), sext(signmask)` to `sext X`. -/
theorem foldAddWithConstant.L947 (ρ : Env) (op0 op1 : Term w) {v : Nat} (x : Term v) (c2 : BitVec v) (k : BitVec w)
    (nsw nuw : Bool) (c0 : op0.Consistent ρ) (h : zextBinConst? .xor op0 = some ⟨v, x, c2⟩)
    (hm : c2 = BitVec.intMin v) (hs : c2.signExtend w = k) (hk : apint op1 = some k) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) ((Repl.sext (w := w) (.old x)).eval ρ) := by
  obtain rfl := const_of_apint hk
  obtain ⟨id, nneg, a, f, ct, rfl, hb, hc⟩ := zextBinConst?_spec h
  obtain rfl := const_of_apint hc
  subst hm hs
  refine refines_of_eval (IS.addSrc_eval ρ _ _ nsw nuw) (by rw [eval_sext]; rfl) ?_
  have hz : (Term.zext (w := w) id nneg a).denote ρ = Val.zext w (a.denote ρ) nneg := c0.2.symm
  rw [hz, IS.xor_denote hb c0.1]
  exact Lemmas.add_zext_xor_intMin_refines _ _ _ _

/-- `C` and `C2` once `sextShAmt` isn't 0: one is `2^j` and the other its negation, with `j + 1` inside the width,
and the shift is `w - 1 - j`. -/
theorem sextShAmt_spec {k c2 : BitVec w} (he : c2 = -k) (hs : sextShAmt k c2 ≠ 0) :
    ∃ j, j + 1 < w ∧ sextShAmt k c2 = w - 1 - j ∧
      ((k = BitVec.twoPow w j ∧ c2 = -k) ∨ (c2 = BitVec.twoPow w j ∧ k = -c2)) := by
  have pow {c : BitVec w} (hp : c.toNat.isPowerOfTwo) :
      Nat.log2 c.toNat < w ∧ c = BitVec.twoPow w (Nat.log2 c.toNat) := by
    obtain ⟨j, hj⟩ := hp
    have hlt : 2 ^ j < 2 ^ w := hj ▸ c.isLt
    have hjw : j < w := (Nat.pow_lt_pow_iff_right (by omega)).1 hlt
    rw [hj, Nat.log2_two_pow]
    exact ⟨hjw, BitVec.eq_of_toNat_eq (by rw [hj, BitVec.toNat_twoPow_of_lt hjw])⟩
  unfold sextShAmt at hs ⊢
  by_cases hp : k.toNat.isPowerOfTwo
  · simp only [hp, ite_true] at hs ⊢
    obtain ⟨hlt, hk⟩ := pow hp
    exact ⟨_, by omega, by omega, Or.inl ⟨hk, he⟩⟩
  · by_cases hp2 : c2.toNat.isPowerOfTwo
    · simp only [hp, hp2, ite_true, ite_false] at hs ⊢
      obtain ⟨hlt, hc⟩ := pow hp2
      refine ⟨_, by omega, by omega, Or.inr ⟨hc, ?_⟩⟩
      rw [he, BitVec.neg_neg]
    · simp [hp, hp2] at hs

/-- `IC.AddSub.foldAddWithConstant.L976`: `(X ^ C2) + -C2` to `ashr (shl X, S), S`, where one of `C` and `C2` is
`2^j`, `S = w - 1 - j`, and `computeKnownBits` knows every bit of `X` above `j` is zero. -/
theorem foldAddWithConstant.L976 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 x : Term w) (k c2 : BitVec w)
    (nsw nuw : Bool) (c0 : op0.Consistent ρ) (u0 : op0.hasUndef = false) (h : xorConst? op0 = some (x, c2))
    (he : c2 = -k) (hs : sextShAmt k c2 ≠ 0)
    (hz : (o.knownZero x &&& highBits w (sextShAmt k c2)) = highBits w (sextShAmt k c2)) (hk : apint op1 = some k) :
    Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ)
      ((Repl.bin .ashr {} (shlOf x (BitVec.ofNat w (sextShAmt k c2))) (.const (BitVec.ofNat w (sextShAmt k c2)))).eval
        ρ) := by
  obtain rfl := const_of_apint hk
  obtain ⟨f, ct, hb, hc⟩ := xorConst?_spec h
  obtain rfl := const_of_apint hc
  obtain ⟨-, -, -, ux, -⟩ := bin_facts hb c0 u0
  obtain ⟨j, hj, hS, hcs⟩ := sextShAmt_spec he hs
  refine refines_of_eval (IS.addSrc_eval ρ op0 _ nsw nuw) (by rw [eval_bin, shlOf_eval ρ x _ ux]; rfl) ?_
  rw [IS.xor_denote hb c0]
  rw [hS] at hz ⊢
  cases hx : x.denote ρ with
  | none => simp [Val.xor, Val.map₂, Val.add, Refines, Refine.le]
  | some xv =>
    have hkz := ho.knownZero x xv hx
    have hbits : ∀ i, j < i → xv.getLsbD i = false := by
      intro i hi
      by_cases hiw : i < w
      · have h1 := congrArg (·.getLsbD i) hkz
        have h2 := congrArg (·.getLsbD i) hz
        have hh : (highBits w (w - 1 - j)).getLsbD i = true := by
          simp only [highBits, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, hiw, decide_true,
            Bool.true_and, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
          omega
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, hh, Bool.and_true] at h1 h2
        rw [h2, Bool.and_true] at h1
        exact h1
      · exact BitVec.getLsbD_of_ge xv i (by omega)
    simp only [Val.xor, Val.map₂]
    exact Lemmas.add_xor_sext_refines hj hbits hcs nuw nsw

/-! ### The fold -/

/-- Every step of `foldAddWithConstant` after `m_APInt(C)` that fires is right. -/
theorem foldAddWithConstant.apSteps_sound (ρ : Env) (c : Ctx) (o : Oracle) (ho : o.Sound ρ) (op0 op1 : Term w)
    (k : BitVec w) (nsw nuw : Bool) (c0 : op0.Consistent ρ) (u0 : op0.hasUndef = false) (hk : apint op1 = some k) :
    ∀ s r, Step.fire s r ∈ foldAddWithConstant.apSteps c o op0 op1 k nsw nuw →
      Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [foldAddWithConstant.apSteps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
  · -- L924
    split at h
    · next f x c01 hb =>
      split at h
      · next hc =>
        simp only [Step.fire.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [Bool.and_eq_true] at hc
        exact foldAddWithConstant.L924 ρ op0 op1 x c01 f k nsw nuw c0 u0 hb hc.1 hc.2 hk
      · cases h
    · cases h
  · -- L930
    split at h
    · next f x c2t hb =>
      split at h
      · next c2 h2 =>
        split at h
        · next he =>
          simp only [Step.fire.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact foldAddWithConstant.L930 ρ op0 op1 x c2t f k c2 nsw nuw c0 hb h2 he hk
        · cases h
      · cases h
    · cases h
  · -- L936
    split at h
    · next hc =>
      simp only [Step.fire.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨rfl, hf⟩ := hc
      exact foldAddWithConstant.L936 ρ op0 op1 nsw nuw hk hf
    · cases h
  · -- L940
    split at h
    · next hc =>
      simp only [Step.fire.injEq] at h
      obtain ⟨-, rfl⟩ := h
      subst hc
      exact foldAddWithConstant.L940 ρ op0 op1 nsw nuw hk
    · cases h
  · -- L947
    split at h
    · next v x c2 hz =>
      split at h
      · next hc =>
        simp only [Step.fire.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact foldAddWithConstant.L947 ρ op0 op1 x c2 k nsw nuw c0 hz hc.1 hc.2 hk
      · cases h
    · cases h
  · -- L952
    split at h
    · next x c2 hx =>
      split at h
      · next hc =>
        simp only [Step.fire.injEq] at h
        obtain ⟨-, rfl⟩ := h
        subst hc
        exact foldAddWithConstant.L952 ρ op0 op1 x k nsw nuw c0 hx hk
      · cases h
    · cases h
  · -- L959
    split at h
    · next x c2 hx =>
      split at h
      · next hc =>
        simp only [Step.fire.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact foldAddWithConstant.L959 ρ o ho op0 op1 x k c2 nsw nuw c0 hx hc hk
      · cases h
    · cases h
  · -- L976
    split at h
    · next x c2 hx =>
      split at h
      · next hc =>
        simp only [Step.fire.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
        obtain ⟨⟨⟨-, he⟩, hs⟩, hz⟩ := hc
        exact foldAddWithConstant.L976 ρ o ho op0 op1 x k c2 nsw nuw c0 u0 hx he hs hz hk
      · cases h
    · cases h
  · -- L989
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨rfl, -⟩ := hc
      split at h
      · next x hx =>
        simp only [Step.fire.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact foldAddWithConstant.L989 ρ op0 op1 x nsw nuw c0 hx hk
      · cases h
    · cases h
  · -- L997
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨rfl, -⟩ := hc
      split at h
      · next x c2 c3 hx =>
        split at h
        · next he =>
          simp only [Step.fire.injEq] at h
          obtain ⟨-, rfl⟩ := h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at he
          exact foldAddWithConstant.L997 ρ op0 op1 x c2 c3 nsw nuw c0 hx he.1 he.2 hk
        · cases h
      · cases h
    · cases h
  · -- L1003
    split at h
    · next id x d =>
      split at h
      · next hc =>
        simp only [Step.fire.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [Bool.and_eq_true] at hc
        exact foldAddWithConstant.L1003 ρ _ op1 x d id k nsw nuw c0 u0 rfl hc.2 hk
      · cases h
    · cases h
  · -- L1020
    split at h
    · next v x ic hz =>
      split at h
      · next hc =>
        simp only [Step.fire.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨hfit, hic⟩, hx⟩ := hc
        exact foldAddWithConstant.L1020 ρ o ho op0 op1 x ic (k.setWidth v) k nsw nuw c0 hz hk hfit rfl hic hx
      · cases h
    · cases h

/-- Theorem 1 for `foldAddWithConstant`: every rewrite it makes refines the `add`, at every width, for every flag,
`Ctx` and sound `Oracle`, in every run its operands are consistent with, poison included, with no `undef`. With `nsw`
at `i1` its `L902` is wrong, so it assumes the `add` isn't an `i1` or has no `nsw`, which `visitAdd` makes sure of. -/
theorem foldAddWithConstant.sound (ρ : Env) (c : Ctx) (o : Oracle) (ho : o.Sound ρ) (op0 op1 : Term w)
    (nsw nuw : Bool) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) (hw : w ≠ 1 ∨ nsw = false) :
    ∀ s r, Step.fire s r ∈ foldAddWithConstant.steps c o op0 op1 nsw nuw →
      Refines ((IS.addSrc op0 op1 nsw nuw).eval ρ) (r.eval ρ) := by
  intro s r hmem
  unfold foldAddWithConstant.steps at hmem
  split at hmem
  · next hc =>
    rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h | h | h | h
      · split at h <;> simp only [reduceCtorEq] at h
      · split at h <;> simp only [reduceCtorEq] at h
      · -- L874
        split at h
        · next f c1' x hb =>
          split at h
          · simp only [Step.fire.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact foldAddWithConstant.L874 ρ op0 op1 c1' x f nsw nuw c0 hb
          · cases h
        · cases h
      · -- L881
        split at h
        · next f x y hb =>
          split at h
          · next ha =>
            simp only [Step.fire.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact foldAddWithConstant.L881 ρ op0 op1 x y f nsw nuw c0 (binop1?_eq hb) ha
          · cases h
        · cases h
      · -- L886
        split at h
        · next x hx =>
          simp only [Step.fire.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact foldAddWithConstant.L886 ρ op0 op1 x nsw nuw c0 hx
        · cases h
      · -- L891
        split at h
        · next x hx =>
          simp only [Step.fire.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact foldAddWithConstant.L891 ρ op0 op1 x nsw nuw c0 hx
        · cases h
      · -- L902
        split at h
        · next x hx =>
          simp only [Step.fire.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact foldAddWithConstant.L902 ρ op0 op1 x nsw nuw c0 u1 hc hw hx
        · cases h
      · -- L911
        split at h
        · next f x sh hb =>
          split at h
          · next hs =>
            simp only [Step.fire.injEq] at h
            obtain ⟨-, rfl⟩ := h
            simp only [Bool.and_eq_true] at hs
            exact foldAddWithConstant.L911 ρ op0 op1 x sh f nsw nuw c0 u0 (binop1?_eq hb) hs.1 hs.2
          · cases h
        · cases h
    · split at hmem
      · next k hk => exact foldAddWithConstant.apSteps_sound ρ c o ho op0 op1 k nsw nuw c0 u0 hk s r hmem
      · cases hmem
  · cases hmem

end Peephole.IC
