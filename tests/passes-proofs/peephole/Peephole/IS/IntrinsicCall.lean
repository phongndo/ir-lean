import Peephole.IS.IntrinsicUnary
import Peephole.IS.IntrinsicBinary

/-! # InstSimplify's `simplifyCall` and `simplifyIntrinsic`, and the funnel shifts' rewrites, for every input

`simplifyInstruction` hands a call to `simplifyCall`, at `llvm/lib/Analysis/InstructionSimplify.cpp:7591-7615` at
`llvmorg-23.1.3`. For a call to an intrinsic whose operands aren't all constants, it asks the `simplifyIntrinsic` that
takes the call, whose only case of its own is `experimental_gc_relocate`, and which otherwise returns what
`llvm::simplifyIntrinsic`, at `7321-7524`, answers. This is the model of both on `Peephole.Term`, step by step in the
C++'s order, for the calls to integer intrinsics `Term` holds:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyIntrinsic.L7329` | A call to an intrinsic that propagates poison, with a poison operand, to poison |
| `IS.simplifyIntrinsic.L7375` | `fshl(undef, undef, z)` to `undef`: without `undef`, of poison |
| `IS.simplifyIntrinsic.L7379` | `fshl(x, y, undef)` to `x`, `fshr` to `y`, about poison only too |
| `IS.simplifyIntrinsic.L7387` | `fshl(x, y, C)` to `x`, `fshr` to `y`, where `C` is a multiple of the width |
| `IS.simplifyIntrinsic.L7396` | `fshl(x >> C1, x << C2, C1)` and `fshr(..., C2)` to `x`, where `C1 + C2` is the width |
| `IS.simplifyIntrinsic.L7401` | `fshl(0, 0, z)` and `fshr(0, 0, z)` to 0 |
| `IS.simplifyIntrinsic.L7405` | `fshl(-1, -1, z)` and `fshr(-1, -1, z)` to -1 |

`intrinsicPropagatesPoison` holds of every intrinsic `Term` holds, and `simplifyIdentityInterleave` declines each, since
none is an interleave. The rest of `simplifyIntrinsic`'s `switch` is for intrinsics `Term` doesn't hold. A call whose
operands are all constants goes to the constant folder first, which the model doesn't follow. -/

namespace Peephole.IS

open IRLean Intrinsic

variable {w : Nat}

/-! ### Helpers -/

/-- `any_of(Args, IsaPred<PoisonValue>)`. An `abs`, `ctlz` or `cttz` call's flag is an `i1` constant, never poison. -/
def Intrinsic.anyPoison : Term w → Bool
  | .un _ _ a => isPoison a
  | .bi _ _ a b => isPoison a || isPoison b
  | .fsh _ _ a b c => isPoison a || isPoison b || isPoison c
  | _ => false

/-- Whether every operand of the call is a `Constant`, as `tryConstantFoldCall` asks. A flag is a constant. -/
def Intrinsic.allConstant : Term w → Bool
  | .un _ _ a => a.isConstant
  | .bi _ _ a b => a.isConstant && b.isConstant
  | .fsh _ _ a b c => a.isConstant && b.isConstant && c.isConstant
  | _ => false

/-- How many operands the call has, as `Args.size()` counts them: an `abs`, `ctlz` or `cttz` call has its flag too. -/
def Intrinsic.numOperands : UnIntr → Nat
  | .ctpop | .bitreverse | .bswap => 1
  | .ctlz _ | .cttz _ | .abs _ => 2

/-- `IID == Intrinsic::fshl ? A : B`. -/
def Intrinsic.byIID {α : Type} (left : Bool) (a b : α) : α := if left then a else b

/-- `match(Op0, m_LShr(m_Value(X), m_APInt(C1))) && match(Op1, m_Shl(m_Specific(X), m_APInt(C2)))`, binding `X`,
`C1` and `C2`. -/
def Intrinsic.rotate? (op0 op1 : Term w) : Option (Term w × BitVec w × BitVec w) :=
  match binop? .lshr op0, binop? .shl op1 with
  | some (_, x, c1t), some (_, x', c2t) =>
    match apint c1t, apint c2t with
    | some c1, some c2 => if specific x x' then some (x, c1, c2) else none
    | _, _ => none
  | _, _ => none

/-! ### The models -/

/-- `llvm::simplifyIntrinsic(IID, ReturnType, Args, FMF, Q, CxtF, ExBehavior, Rounding)`, step by step, for the
calls `Term` holds. `IID` and `Args` are the call's. -/
def simplifyIntrinsic.steps (o : Oracle) (r : Recur) (call : Term w) : List (Step w) :=
  [ -- if (IID != Intrinsic::not_intrinsic && intrinsicPropagatesPoison(IID) && any_of(Args, IsaPred<PoisonValue>))
    --   return PoisonValue::get(ReturnType);
    if anyPoison call then .fire "IS.simplifyIntrinsic.L7329" .poison else .next,
    -- Most of the intrinsics with no operands have some kind of side effect. Don't simplify. Every intrinsic
    -- `Term` holds has operands. if (Value *V = simplifyIdentityInterleave(IID, Args)) return V;: none is an
    -- interleave, so `getInterleaveIntrinsicFactor` is 0 and it declines.
    .next,
    -- if (NumOperands == 1) return simplifyUnaryIntrinsic(IID, Args[0], FMF, Q);
    match call with
    | .un _ f op0 => if numOperands f == 1 then tail (simplifyUnaryIntrinsic.steps o f op0) else .next
    | _ => .next,
    -- if (NumOperands == 2) return simplifyBinaryIntrinsic(IID, ReturnType, Args[0], Args[1], FMF, Q);
    match call with
    | .un _ f _ => if numOperands f == 2 then tail (simplifyBinaryIntrinsic.steps r call) else .next
    | .bi .. => tail (simplifyBinaryIntrinsic.steps r call)
    | _ => .next,
    -- case Intrinsic::fshl: case Intrinsic::fshr: If both operands are undef, the result is undef.
    match call with
    | .fsh _ _ op0 op1 _ =>
      if isUndefValue op0 && isUndefValue op1 then .fire "IS.simplifyIntrinsic.L7375" (.old op0) else .next
    | _ => .next,
    -- If shift amount is undef, assume it is zero.
    match call with
    | .fsh _ l op0 op1 sh =>
      if isUndefValue sh then .fire "IS.simplifyIntrinsic.L7379" (.old (byIID l op0 op1)) else .next
    | _ => .next,
    -- If there's effectively no shift, return the 1st arg or 2nd arg.
    match call with
    | .fsh _ l op0 op1 sh =>
      match apint sh with
      | some c =>
        if c % BitVec.ofNat w w == 0#w then .fire "IS.simplifyIntrinsic.L7387" (.old (byIID l op0 op1))
        else .next
      | none => .next
    | _ => .next,
    -- fshl (lshr X, C1), (shl X, C2), C1 -> X when C1 + C2 == BW
    -- fshr (lshr X, C1), (shl X, C2), C2 -> X when C1 + C2 == BW
    match call with
    | .fsh _ l op0 op1 sh =>
      match apint sh, rotate? op0 op1 with
      | some c, some (x, c1, c2) =>
        if c1 + c2 == BitVec.ofNat w w && c % BitVec.ofNat w w == (byIID l c1 c2) then
          .fire "IS.simplifyIntrinsic.L7396" (.old x)
        else .next
      | _, _ => .next
    | _ => .next,
    -- Rotating zero by anything is zero.
    match call with
    | .fsh _ _ op0 op1 _ => if zero op0 && zero op1 then .fire "IS.simplifyIntrinsic.L7401" (.const 0#w) else .next
    | _ => .next,
    -- Rotating -1 by anything is -1.
    match call with
    | .fsh _ _ op0 op1 _ =>
      if allOnes op0 && allOnes op1 then .fire "IS.simplifyIntrinsic.L7405" (.const (BitVec.allOnes w)) else .next
    | _ => .next ]

/-- `llvm::simplifyCall(Call, Callee, Args, Q)`, step by step, for the calls `Term` holds. -/
def simplifyCall.steps (o : Oracle) (r : Recur) (call : Term w) : List (Step w) :=
  [ -- musttail calls can only be simplified if they are also DCEd. No call `Term` holds is `musttail`.
    .next,
    -- call undef -> poison, call null -> poison: the callee here is the intrinsic's declaration.
    .next,
    -- if (Value *V = tryConstantFoldCall(Call, Args, Q)) return V;
    if allConstant call then .delegate "ConstantFoldCall" else .next,
    -- if (F && F->isIntrinsic()) if (Value *Ret = ::simplifyIntrinsic(Call, Args, Q)) return Ret;
    -- Its `switch` has one case, `experimental_gc_relocate`; the default returns `llvm::simplifyIntrinsic`'s answer.
    forward (simplifyIntrinsic.steps o r call) ]

/-- What InstSimplify does with a call to an integer intrinsic it reaches: `simplifyInstructionWithOperands` calls
`simplifyCall` on it, and `isICmpTrue`'s recursive call isn't modelled, `Recur.unknown`. -/
def simplifyCall.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, t@(.un ..) | _, t@(.bi ..) | _, t@(.fsh ..) => run (simplifyCall.steps o Recur.unknown t)
  | _, _ => .null

/-! ### The rewrites, one theorem each -/

/-- A call LLVM's verifier accepts, as far as these folds need: a `bswap` of whole bytes, an even number of them. -/
def Intrinsic.Valid : Term w → Prop
  | .un _ .bswap _ => w % 8 = 0
  | _ => True

/-- `IS.simplifyIntrinsic.L7329`: a call with a poison operand to poison, every intrinsic `Term` holds propagating it,
as `IRLean.Contract`'s strictness lemmas say. -/
theorem simplifyIntrinsic.L7329 (ρ : Env) (call : Term w) (h : anyPoison call = true) :
    Refines (call.top.eval ρ) ((Repl.poison : Repl w).eval ρ) := by
  cases call <;> simp only [anyPoison, Bool.or_eq_true, reduceCtorEq] at h
  · next id f a =>
    simp only [Term.top, un_eval, isPoison_denote h, UnIntr.eval_none, Repl.eval_poison]
    exact refines_ok (Refine.val_none _)
  · next id f a b =>
    simp only [Term.top, bi_eval, Repl.eval_poison]
    refine refines_ok ?_
    rcases h with h | h
    · rw [isPoison_denote h, BinIntr.eval_none_left]; exact Refine.val_none _
    · rw [isPoison_denote h, BinIntr.eval_none_right]; exact Refine.val_none _
  · next id l a b c =>
    simp only [Term.top, fsh_eval, Repl.eval_poison]
    refine refines_ok ?_
    rw [fsh_none]
    · exact Refine.val_none _
    · rcases h with (h | h) | h
      · exact .inl (isPoison_denote h)
      · exact .inr (.inl (isPoison_denote h))
      · exact .inr (.inr (isPoison_denote h))

/-- `IS.simplifyIntrinsic.L7375`: `fshl(undef, undef, z)` to `undef`, which without `undef` is of poison, poison. -/
theorem simplifyIntrinsic.L7375 (ρ : Env) (l : Bool) (op0 op1 sh : Term w) (u0 : op0.hasUndef = false)
    (h : (isUndefValue op0 && isUndefValue op1) = true) :
    Refines ((Repl.fsh l (.old op0) (.old op1) (.old sh)).eval ρ) ((Repl.old op0).eval ρ) := by
  simp only [Bool.and_eq_true] at h
  rw [fsh_eval, Repl.eval_old, fsh_none l _ _ _ (.inl (isUndefValue_denote h.1 u0))]
  exact refines_ok (Refine.val_none _)

/-- `IS.simplifyIntrinsic.L7379`: `fshl(x, y, undef)` to `x` and `fshr` to `y`, which without `undef` is a shift by
poison, poison. -/
theorem simplifyIntrinsic.L7379 (ρ : Env) (l : Bool) (op0 op1 sh : Term w) (us : sh.hasUndef = false)
    (h : isUndefValue sh = true) :
    Refines ((Repl.fsh l (.old op0) (.old op1) (.old sh)).eval ρ) ((Repl.old (byIID l op0 op1)).eval ρ) := by
  rw [fsh_eval, Repl.eval_old, fsh_none l _ _ _ (.inr (.inr (isUndefValue_denote h us)))]
  exact refines_ok (Refine.val_none _)

theorem toNat_umod_width (c : BitVec w) : (c % BitVec.ofNat w w).toNat = c.toNat % w := by
  rw [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := w))]

/-- `IS.simplifyIntrinsic.L7387`: `fshl(x, y, C)` to `x` and `fshr` to `y`, where `C` is a multiple of the width. -/
theorem simplifyIntrinsic.L7387 (ρ : Env) (l : Bool) (op0 op1 sh : Term w) {c : BitVec w}
    (hc : apint sh = some c) (h : (c % BitVec.ofNat w w == 0#w) = true) :
    Refines ((Repl.fsh l (.old op0) (.old op1) (.old sh)).eval ρ) ((Repl.old (byIID l op0 op1)).eval ρ) := by
  have hz : c.toNat % w = 0 := by
    rw [← toNat_umod_width]; simp only [beq_iff_eq] at h; rw [h]; rfl
  rw [fsh_eval, Repl.eval_old, apint_denote hc]
  refine refines_ok ?_
  cases l
  · exact Lemmas.fshr_of_toNat_mod_eq_zero _ _ hz
  · exact Lemmas.fshl_of_toNat_mod_eq_zero _ _ hz

theorem rotate?_denote {ρ : Env} {op0 op1 x : Term w} {c1 c2 : BitVec w} (h : rotate? op0 op1 = some (x, c1, c2))
    (c0 : op0.Consistent ρ) (c1' : op1.Consistent ρ) :
    ∃ e nuw nsw, op0.denote ρ = Val.lshr (x.denote ρ) (some c1) e ∧
      op1.denote ρ = Val.shl (x.denote ρ) (some c2) nuw nsw := by
  unfold rotate? at h
  split at h
  · next f x0 c1t f' x' c2t h0 h1 =>
    split at h
    · next c1v c2v hc1 hc2 =>
      split at h
      · next hs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have d0 := ok_inj (binop?_consistent h0 c0).2.2
        have d1 := ok_inj (binop?_consistent h1 c1').2.2
        refine ⟨f.exact, f'.nuw, f'.nsw, ?_, ?_⟩
        · rw [← d0, apint_denote hc1]
        · rw [← d1, apint_denote hc2, specific_denote hs]
      · cases h
    · cases h
  · cases h

/-- `IS.simplifyIntrinsic.L7396`: `fshl(x >> C1, x << C2, C1)` and `fshr(x >> C1, x << C2, C2)` to `x`, where `C1 + C2`
is the width, whatever the shifts' flags. -/
theorem simplifyIntrinsic.L7396 (ρ : Env) (l : Bool) (op0 op1 sh x : Term w) (c0 : op0.Consistent ρ)
    (c1' : op1.Consistent ρ) {c c1 c2 : BitVec w} (hc : apint sh = some c) (hr : rotate? op0 op1 = some (x, c1, c2))
    (h : (c1 + c2 == BitVec.ofNat w w && c % BitVec.ofNat w w == (byIID l c1 c2)) = true) :
    Refines ((Repl.fsh l (.old op0) (.old op1) (.old sh)).eval ρ) ((Repl.old x).eval ρ) := by
  obtain ⟨e, nuw, nsw, d0, d1⟩ := rotate?_denote hr c0 c1'
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [fsh_eval, Repl.eval_old, apint_denote hc, d0, d1]
  refine refines_ok ?_
  cases l
  · exact Lemmas.fshr_lshr_shl_refines _ h.1 h.2 _ _ _
  · exact Lemmas.fshl_lshr_shl_refines _ h.1 h.2 _ _ _

/-- `IS.simplifyIntrinsic.L7401`: `fshl(0, 0, z)` and `fshr(0, 0, z)` to 0. -/
theorem simplifyIntrinsic.L7401 (ρ : Env) (l : Bool) (op0 op1 sh : Term w) (h : (zero op0 && zero op1) = true) :
    Refines ((Repl.fsh l (.old op0) (.old op1) (.old sh)).eval ρ) ((Repl.const 0#w).eval ρ) := by
  simp only [Bool.and_eq_true] at h
  rw [fsh_eval, cst_eq h.1, cst_eq h.2]
  refine refines_ok ?_
  cases l
  · exact Lemmas.fshr_zero_zero_refines _
  · exact Lemmas.fshl_zero_zero_refines _

/-- `IS.simplifyIntrinsic.L7405`: `fshl(-1, -1, z)` and `fshr(-1, -1, z)` to -1. -/
theorem simplifyIntrinsic.L7405 (ρ : Env) (l : Bool) (op0 op1 sh : Term w)
    (h : (allOnes op0 && allOnes op1) = true) :
    Refines ((Repl.fsh l (.old op0) (.old op1) (.old sh)).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  simp only [Bool.and_eq_true] at h
  rw [fsh_eval, cst_eq h.1, cst_eq h.2]
  refine refines_ok ?_
  cases l
  · exact Lemmas.fshr_allOnes_allOnes_refines _
  · exact Lemmas.fshl_allOnes_allOnes_refines _

/-! ### The folds -/

/-- Every step of `simplifyIntrinsic` that fires is right, for a call LLVM's verifier accepts. -/
theorem simplifyIntrinsic.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (r : Recur) (hr : r.Sound ρ)
    (call : Term w) (cc : call.Consistent ρ) (uc : call.hasUndef = false) (hv : Valid call) :
    ∀ s rr, Step.fire s rr ∈ simplifyIntrinsic.steps o r call → Refines (call.top.eval ρ) (rr.eval ρ) := by
  intro s rr hmem
  simp only [simplifyIntrinsic.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyIntrinsic.L7329 ρ call (by assumption)
  · cases h
  · split at h
    · next id f op0 =>
      split at h
      · exact simplifyUnaryIntrinsic.steps_sound ρ o ho f op0 cc.1 (by rintro rfl; exact hv) s rr (tail_fire h.symm)
      · cases h
    · cases h
  · split at h
    · split at h
      · exact simplifyBinaryIntrinsic.steps_sound ρ r hr _ cc uc s rr (tail_fire h.symm)
      · cases h
    · exact simplifyBinaryIntrinsic.steps_sound ρ r hr _ cc uc s rr (tail_fire h.symm)
    · cases h
  · split at h <;> try simp only [reduceCtorEq] at h
    next id l op0 op1 sh =>
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [Term.hasUndef, Bool.or_eq_false_iff] at uc
    exact simplifyIntrinsic.L7375 ρ l op0 op1 sh uc.1.1 (by assumption)
  · split at h <;> try simp only [reduceCtorEq] at h
    next id l op0 op1 sh =>
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [Term.hasUndef, Bool.or_eq_false_iff] at uc
    exact simplifyIntrinsic.L7379 ρ l op0 op1 sh uc.2 (by assumption)
  · split at h <;> try simp only [reduceCtorEq] at h
    next id l op0 op1 sh =>
    split at h <;> try simp only [reduceCtorEq] at h
    next c hc =>
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyIntrinsic.L7387 ρ l op0 op1 sh hc (by assumption)
  · split at h <;> try simp only [reduceCtorEq] at h
    next id l op0 op1 sh =>
    split at h <;> try simp only [reduceCtorEq] at h
    next c x c1 c2 hc hr' =>
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyIntrinsic.L7396 ρ l op0 op1 sh x cc.1 cc.2.1 hc hr' (by assumption)
  · split at h <;> try simp only [reduceCtorEq] at h
    next id l op0 op1 sh =>
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyIntrinsic.L7401 ρ l op0 op1 sh (by assumption)
  · split at h <;> try simp only [reduceCtorEq] at h
    next id l op0 op1 sh =>
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyIntrinsic.L7405 ρ l op0 op1 sh (by assumption)

/-- Theorem 1 for `simplifyIntrinsic` on the calls `Term` holds: every value the model returns refines the call, at
every width, flag and operand, poison included, in every run the call is consistent with, given the analyses and `r`,
the recursive `simplifyICmpInst`, are sound, for a call LLVM's verifier accepts. It says nothing about operands that
reach an `undef`. -/
theorem simplifyIntrinsic.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (r : Recur) (hr : r.Sound ρ)
    (call : Term w) (cc : call.Consistent ρ) (uc : call.hasUndef = false) (hv : Valid call) {rr : Repl w}
    (h : run (simplifyIntrinsic.steps o r call) = .value rr) : Refines (call.top.eval ρ) (rr.eval ρ) :=
  run_sound (simplifyIntrinsic.steps_sound ρ o ho r hr call cc uc hv) h

/-- Every step of `simplifyCall` that fires is right, for a call LLVM's verifier accepts. -/
theorem simplifyCall.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (r : Recur) (hr : r.Sound ρ)
    (call : Term w) (cc : call.Consistent ρ) (uc : call.hasUndef = false) (hv : Valid call) :
    ∀ s rr, Step.fire s rr ∈ simplifyCall.steps o r call → Refines (call.top.eval ρ) (rr.eval ρ) := by
  intro s rr hmem
  simp only [simplifyCall.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · cases h
  · cases h
  · split at h <;> cases h
  · exact simplifyIntrinsic.steps_sound ρ o ho r hr call cc uc hv s rr (forward_fire h.symm)

/-- Theorem 1 for `simplifyCall` on the calls to integer intrinsics `Term` holds: every value the model returns
refines the call, at every width, flag and operand, poison included, in every run the call is consistent with, given
the analyses and `r`, the recursive `simplifyICmpInst`, are sound, for a call LLVM's verifier accepts. It says nothing
about operands that reach an `undef`. -/
theorem simplifyCall.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (r : Recur) (hr : r.Sound ρ)
    (call : Term w) (cc : call.Consistent ρ) (uc : call.hasUndef = false) (hv : Valid call) {rr : Repl w}
    (h : run (simplifyCall.steps o r call) = .value rr) : Refines (call.top.eval ρ) (rr.eval ρ) :=
  run_sound (simplifyCall.steps_sound ρ o ho r hr call cc uc hv) h

/-- What `onInst` answers, the comparison with `opt` runs, is right: `simplifyCall` with `Recur.unknown`. -/
theorem simplifyCall.onInst_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (call : Term w)
    (cc : call.Consistent ρ) (uc : call.hasUndef = false) (hv : Valid call) {rr : Repl w}
    (h : simplifyCall.onInst o call = .value rr) : Refines (call.top.eval ρ) (rr.eval ρ) := by
  cases call <;> simp only [simplifyCall.onInst, reduceCtorEq] at h <;>
    exact simplifyCall.sound ρ o ho _ (Recur.unknown_sound ρ) _ cc uc hv h

end Peephole.IS
