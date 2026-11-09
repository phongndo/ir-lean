import Peephole.IS.Shift

/-! # InstSimplify's integer casts and `freeze`, and their rewrites for every input

`simplifyCastInst` is at `llvm/lib/Analysis/InstructionSimplify.cpp:5638-5683` and `simplifyFreezeInst` at `7625-7632`,
at `llvmorg-23.1.3`. This is their model on `Peephole.Term`, for the casts a `Term` has, `trunc`, `zext` and `sext`,
step by step in the C++'s order:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyCastInst.L5641` | A cast of a constant to the constant the folder gives |
| `IS.simplifyCastInst.L5653` | `trunc (zext X)` and `trunc (sext X)` back to the type of `X`, to `X` |
| `IS.simplifyCastInst.L5678` | `zext (trunc nuw X)` and `sext (trunc nsw X)` back to the type of `X`, to `X` |
| `IS.simplifyFreezeInst.L7631` | `freeze X` to `X`, where `X` is known not to be `undef` or poison |

`simplifyCastInst.sound` and `simplifyFreezeInst.sound` put them together, and `onInst_sound` says each `onInst`'s
answer refines the instruction it's given.

What the model reads:

- `ConstantFoldCastOperand`, for a scalar integer constant, is `ConstantFoldCastInstruction`'s answer, which the model
  has: poison to poison, `undef` to 0 for `zext` and `sext` and to `undef` for `trunc`, and a `ConstantInt` cast.
- `CastInst::isEliminableCastPair` is modelled for the integer casts, from its table. An extension then a `trunc` back
  to the source's type is a `bitcast`: the one answer `simplifyCastInst` takes.
- `isGuaranteedNotToBeUndefOrPoison` is `Shift.Ext.notUndefOrPoison`, since the core `Oracle`'s `notPoison` is
  `isGuaranteedNotToBePoison`, which holds of `undef` too. `onInst` reads it as the oracle answers `notPoison`, which a
  sound oracle can't answer yes of `undef`, which reads as poison here: `Shift.Ext.ofOracle`.
- The `bitcast` and `ptrtoint` steps don't apply to `trunc`, `zext` or `sext`: `Term` has no `bitcast` or pointers. -/

namespace Peephole.IS

open IRLean

variable {w : Nat}

namespace Cast

/-- The casts a `Term` has, as `simplifyCastInst`'s `CastOpc`. -/
inductive CastOp where
  | trunc | zext | sext
  deriving DecidableEq, Repr

/-- What `CastInst::isEliminableCastPair` answers: no pair, a `bitcast`, or one cast. -/
inductive Pair where
  | none | bitcast
  | cast (op : CastOp)
  deriving DecidableEq, Repr

/-- `CastInst::isEliminableCastPair(FirstOp, SecondOp, SrcTy, MidTy, DstTy, DL)` for the integer casts, from the
table in `llvm/lib/IR/Instructions.cpp:2882`: case 1 gives the first cast, case 0 none, case 9 `zext`, and case 8,
an extension then a `trunc`, a `bitcast` if the source and destination types are the same, else whichever cast goes
from the source's width to the destination's. Integer types are the same when their widths are. -/
def isEliminableCastPair (first second : CastOp) (src _mid dst : Nat) : Pair :=
  match first, second with
  | .trunc, .trunc => .cast .trunc
  | .trunc, .zext | .trunc, .sext => .none
  | .zext, .trunc | .sext, .trunc =>
    if src = dst then .bitcast else if src < dst then .cast first else if dst < src then .cast .trunc else .none
  | .zext, .zext => .cast .zext
  | .zext, .sext => .cast .zext
  | .sext, .zext => .none
  | .sext, .sext => .cast .sext

/-- `ConstantFoldCastOperand(CastOpc, C, Ty, DL)` for a scalar integer constant `C`, which is
`ConstantFoldCastInstruction`'s answer: poison to poison; `undef` to 0 for `zext` and `sext`, "because the top bits will
be zero" or "all the same", and to `undef` for `trunc`; and a `ConstantInt` cast with `APInt`'s `trunc`, `zext` or
`sext`. The cast's flags aren't read. -/
def foldConst (op : CastOp) (w : Nat) {v : Nat} : Term v → Option (Repl w)
  | .const c => some (.const (match op with
    | .trunc | .zext => c.setWidth w
    | .sext => c.signExtend w))
  | .poison => some .poison
  | .undef => some (match op with
    | .trunc => .old .undef
    | .zext | .sext => .const 0#w)
  | _ => none

/-- `Src->getType() == Ty`: `a`, if its width is the destination's. -/
def ofWidth (w : Nat) {u : Nat} (a : Term u) : Option (Term w) :=
  if h : u = w then some (h ▸ a) else none

/-- `dyn_cast<CastInst>(Op)`: the cast `Op` is, if it's one, and its operand at the destination's width, if it has
it. -/
def castOf (w : Nat) {v : Nat} : Term v → Option (CastOp × Term w)
  | .trunc _ _ _ a => (ofWidth w a).map (.trunc, ·)
  | .zext _ _ a => (ofWidth w a).map (.zext, ·)
  | .sext _ a => (ofWidth w a).map (.sext, ·)
  | _ => none

/-- The flag a `trunc` needs for the extension `op` of it to give back its operand: `nuw` for `zext`, `nsw` for
`sext`. -/
def noWrap : CastOp → Bool → Bool → Bool
  | .zext, nuw, _ => nuw
  | .sext, _, nsw => nsw
  | .trunc, _, _ => false

/-- `dyn_cast<TruncInst>(Op)` with `NoWrap`, the flag the outer cast needs, `nuw` for `zext` and `nsw` for `sext`, and
`Src->getType() == Ty`: the `trunc`'s operand. -/
def truncNoWrapOf (op : CastOp) (w : Nat) {v : Nat} : Term v → Option (Term w)
  | .trunc _ nuw nsw a => if noWrap op nuw nsw then ofWidth w a else none
  | _ => none

/-- The cast `op` of `src` to width `w`, with its flags, that a fold replaces: `nneg` is read by `zext`, and `nuw` and
`nsw` by `trunc`. -/
def castSrc (op : CastOp) (nneg nuw nsw : Bool) (w : Nat) {v : Nat} (src : Term v) : Repl w :=
  match op with
  | .trunc => .trunc nuw nsw (.old src)
  | .zext => .zext nneg (.old src)
  | .sext => .sext (.old src)

/-- A `zext` or `sext` that's valid IR: its result is no narrower than its operand. `IS.simplifyCastInst.L5653`
rests on it, as `trunc (zext X)` is only `X` when the `zext` didn't drop bits of `X`. -/
def Widens {v : Nat} : Term v → Prop
  | .zext (v := u) _ _ _ => u ≤ v
  | .sext (v := u) _ _ => u ≤ v
  | _ => True

/-- The operand of a cast `Widens`. -/
def OperandWidens : Term w → Prop
  | .trunc _ _ _ a | .zext _ _ a | .sext _ a => Widens a
  | _ => True

end Cast

/-! ### The model -/

/-- `simplifyCastInst(CastOpc, Op, Ty, Q, MaxRecurse)` for `CastOpc` one of `trunc`, `zext` and `sext`, from width `v`
to width `w`, step by step. -/
def simplifyCastInst.steps (op : Cast.CastOp) {v : Nat} (src : Term v) (w : Nat) : List (Step w) :=
  [ -- if (auto *C = dyn_cast<Constant>(Op)) return ConstantFoldCastOperand(CastOpc, C, Ty, Q.DL);
    match Cast.foldConst op w src with
    | some r => .fire "IS.simplifyCastInst.L5641" r
    | none => .next,
    -- A cast of a cast, back to the source's type, that the pair's table says is a bitcast.
    match Cast.castOf w src with
    | some (first, a) =>
      if Cast.isEliminableCastPair first op w v w = .bitcast then .fire "IS.simplifyCastInst.L5653" (.old a) else .next
    | none => .next,
    -- bitcast x -> x: `CastOpc` is no `bitcast`.
    .next,
    -- ptrtoint (ptradd (Ptr, X - ptrtoint(Ptr))) -> X: `CastOpc` is no `ptrtoint` or `ptrtoaddr`.
    .next,
    -- Fold a value-preserving zext/sext of a trunc back to the original value.
    if op = .zext ∨ op = .sext then
      match Cast.truncNoWrapOf op w src with
      | some a => .fire "IS.simplifyCastInst.L5678" (.old a)
      | none => .next
    else .next ]

def simplifyCastInst (op : Cast.CastOp) {v : Nat} (src : Term v) (w : Nat) : Result w :=
  run (simplifyCastInst.steps op src w)

/-- What InstSimplify does with a `trunc`, `zext` or `sext` it reaches: `simplifyInstructionWithOperands` calls
`simplifyCastInst` with the instruction's opcode, operand and type. -/
def simplifyCastInst.onInst (_o : Oracle) : {w : Nat} → Term w → Result w
  | w, .trunc _ _ _ a => simplifyCastInst .trunc a w
  | w, .zext _ _ a => simplifyCastInst .zext a w
  | w, .sext _ a => simplifyCastInst .sext a w
  | _, _ => .null

/-- `simplifyFreezeInst(Op0, Q)`, step by step. -/
def simplifyFreezeInst.steps (e : Shift.Ext) (op0 : Term w) : List (Step w) :=
  [ -- Use a utility function defined in ValueTracking.
    if e.notUndefOrPoison op0 then .fire "IS.simplifyFreezeInst.L7631" (.old op0) else .next ]

def simplifyFreezeInst (e : Shift.Ext) (op0 : Term w) : Result w := run (simplifyFreezeInst.steps e op0)

/-- What InstSimplify does with a `freeze` it reaches: `simplifyInstructionWithOperands` calls `simplifyFreezeInst` on
its operand. -/
def simplifyFreezeInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .freeze _ a => simplifyFreezeInst (Shift.Ext.ofOracle o) a
  | _, _ => .null

/-! ### The rewrites, one theorem each -/

namespace Cast

theorem castSrc_eval (ρ : Env) (nneg nuw nsw : Bool) {v : Nat} (src : Term v) :
    (castSrc .trunc nneg nuw nsw w src).eval ρ = Outcome.ok (Val.trunc w (src.denote ρ) nuw nsw) ∧
    (castSrc .zext nneg nuw nsw w src).eval ρ = Outcome.ok (Val.zext w (src.denote ρ) nneg) ∧
    (castSrc .sext nneg nuw nsw w src).eval ρ = Outcome.ok (Val.sext w (src.denote ρ)) :=
  ⟨rfl, rfl, rfl⟩

theorem ofWidth_eq {u : Nat} {a : Term u} {b : Term w} (h : ofWidth w a = some b) : ∃ hu : u = w, b = hu ▸ a := by
  unfold ofWidth at h
  split at h
  · next hu => exact ⟨hu, (Option.some.inj h).symm⟩
  · cases h

end Cast

open Cast in
/-- `IS.simplifyCastInst.L5641`: a cast of a constant to what the constant folder gives, whatever the cast's flags:
they can only make the cast poison. -/
theorem simplifyCastInst.L5641 (ρ : Env) (op : CastOp) (nneg nuw nsw : Bool) {v : Nat} (src : Term v) (r : Repl w)
    (u : src.hasUndef = false) (h : foldConst op w src = some r) :
    Refines ((castSrc op nneg nuw nsw w src).eval ρ) (r.eval ρ) := by
  cases src with
  | const c =>
    simp only [foldConst, Option.some.injEq] at h
    subst h
    cases op
    · show Refines (Outcome.ok (Val.trunc w (some c) nuw nsw)) (Outcome.ok (some (c.setWidth w)))
      refine refines_ok ?_
      simp only [Val.trunc]
      split
      · exact Refine.val_none _
      · split
        · exact Refine.val_none _
        · exact Refine.refl_val _
    · show Refines (Outcome.ok (Val.zext w (some c) nneg)) (Outcome.ok (some (c.setWidth w)))
      refine refines_ok ?_
      simp only [Val.zext]
      split
      · exact Refine.val_none _
      · exact Refine.refl_val _
    · exact refines_ok (Refine.refl_val _)
  | poison =>
    simp only [foldConst, Option.some.injEq] at h
    subst h
    cases op <;> exact refines_ok (Refine.val_none _)
  | undef => simp [Term.hasUndef] at u
  | _ => simp [foldConst] at h

theorem Cast.castOf_denote {ρ : Env} {v : Nat} {src : Term v} {first : CastOp} {a : Term w}
    (h : castOf w src = some (first, a)) (hc : src.Consistent ρ) (hw : Widens src) :
    (first = .trunc ∧ ∃ nuw nsw, src.denote ρ = Val.trunc v (a.denote ρ) nuw nsw) ∨
    (first = .zext ∧ w ≤ v ∧ ∃ nneg, src.denote ρ = Val.zext v (a.denote ρ) nneg) ∨
    (first = .sext ∧ w ≤ v ∧ src.denote ρ = Val.sext v (a.denote ρ)) := by
  cases src with
  | trunc id nuw nsw b =>
    simp only [castOf] at h
    cases hb : ofWidth w b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := ofWidth_eq hb
      exact Or.inl ⟨rfl, nuw, nsw, hc.2.symm⟩
  | zext id nneg b =>
    simp only [castOf] at h
    cases hb : ofWidth w b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := ofWidth_eq hb
      exact Or.inr (Or.inl ⟨rfl, hw, nneg, hc.2.symm⟩)
  | sext id b =>
    simp only [castOf] at h
    cases hb : ofWidth w b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := ofWidth_eq hb
      exact Or.inr (Or.inr ⟨rfl, hw, hc.2.symm⟩)
  | _ => simp [castOf] at h

open Cast in
/-- `IS.simplifyCastInst.L5653`: `trunc (zext X)` and `trunc (sext X)` back to the type of `X`, to `X`, whatever the
flags. It rests on the extension being valid IR, `Widens`: one that narrowed would have dropped bits of `X`. -/
theorem simplifyCastInst.L5653 (ρ : Env) (op : CastOp) (nneg nuw nsw : Bool) {v : Nat} (src : Term v) (first : CastOp)
    (a : Term w) (c : src.Consistent ρ) (hw : Widens src) (h : castOf w src = some (first, a))
    (he : isEliminableCastPair first op w v w = .bitcast) :
    Refines ((castSrc op nneg nuw nsw w src).eval ρ) ((Repl.old a).eval ρ) := by
  have hop : op = .trunc := by
    cases first <;> cases op <;> simp [isEliminableCastPair] at he ⊢
  subst hop
  rw [(castSrc_eval ρ nneg nuw nsw src).1, Repl.eval_old]
  refine refines_ok ?_
  rcases castOf_denote h c hw with ⟨rfl, -⟩ | ⟨-, hwv, nneg', hd⟩ | ⟨-, hwv, hd⟩
  · simp [isEliminableCastPair] at he
  · rw [hd]; exact Lemmas.trunc_zext_refines _ hwv _ _ _
  · rw [hd]; exact Lemmas.trunc_sext_refines _ hwv _ _

theorem Cast.truncNoWrapOf_denote {ρ : Env} {op : CastOp} {v : Nat} {src : Term v} {a : Term w}
    (h : truncNoWrapOf op w src = some a) (hc : src.Consistent ρ) :
    (op = .zext ∧ ∃ nsw, src.denote ρ = Val.trunc v (a.denote ρ) true nsw) ∨
    (op = .sext ∧ ∃ nuw, src.denote ρ = Val.trunc v (a.denote ρ) nuw true) := by
  cases src with
  | trunc id nuw nsw b =>
    simp only [truncNoWrapOf] at h
    split at h
    · next hf =>
      obtain ⟨rfl, rfl⟩ := ofWidth_eq h
      cases op <;> simp only [noWrap, Bool.false_eq_true] at hf
      · subst hf; exact Or.inl ⟨rfl, nsw, hc.2.symm⟩
      · subst hf; exact Or.inr ⟨rfl, nuw, hc.2.symm⟩
    · cases h
  | _ => simp [truncNoWrapOf] at h

open Cast in
/-- `IS.simplifyCastInst.L5678`: `zext (trunc nuw X)` and `sext (trunc nsw X)` back to the type of `X`, to `X`,
whatever the other flags: the flag says the `trunc` dropped no bits the extension doesn't put back. -/
theorem simplifyCastInst.L5678 (ρ : Env) (op : CastOp) (nneg nuw nsw : Bool) {v : Nat} (src : Term v) (a : Term w)
    (c : src.Consistent ρ) (h : truncNoWrapOf op w src = some a) :
    Refines ((castSrc op nneg nuw nsw w src).eval ρ) ((Repl.old a).eval ρ) := by
  rw [Repl.eval_old]
  rcases truncNoWrapOf_denote h c with ⟨rfl, nsw', hd⟩ | ⟨rfl, nuw', hd⟩
  · rw [(castSrc_eval ρ nneg nuw nsw src).2.1, hd]
    exact refines_ok (Lemmas.zext_trunc_nuw_refines _ _ _ _)
  · rw [(castSrc_eval ρ nneg nuw nsw src).2.2, hd]
    exact refines_ok (Lemmas.sext_trunc_nsw_refines _ _ _)

open Cast in
theorem simplifyCastInst.steps_sound (ρ : Env) (op : CastOp) (nneg nuw nsw : Bool) {v : Nat} (src : Term v)
    (c : src.Consistent ρ) (u : src.hasUndef = false) (hw : Widens src) :
    ∀ s r, Step.fire s r ∈ simplifyCastInst.steps op src w →
      Refines ((castSrc op nneg nuw nsw w src).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyCastInst.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next r' hr =>
    obtain ⟨-, rfl⟩ := h
    exact simplifyCastInst.L5641 ρ op nneg nuw nsw src _ u hr
  · split at h
    · next first a hca =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next he =>
      obtain ⟨-, rfl⟩ := h
      exact simplifyCastInst.L5653 ρ op nneg nuw nsw src first a c hw hca he
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next a ha =>
      obtain ⟨-, rfl⟩ := h
      exact simplifyCastInst.L5678 ρ op nneg nuw nsw src a c ha
    · simp only [reduceCtorEq] at h

/-- Theorem 1 for `simplifyCastInst`: every value the model returns refines the `trunc`, `zext` or `sext` it replaces,
at every pair of widths and with every flag, in every run its operand is consistent with, poison included. It rests on
a `zext` or `sext` operand being valid IR, `Cast.Widens`, and says nothing about an operand that reaches an `undef`. -/
theorem simplifyCastInst.sound (ρ : Env) (op : Cast.CastOp) (nneg nuw nsw : Bool) {v : Nat} (src : Term v)
    (c : src.Consistent ρ) (u : src.hasUndef = false) (hw : Cast.Widens src) {r : Repl w}
    (h : simplifyCastInst op src w = .value r) :
    Refines ((Cast.castSrc op nneg nuw nsw w src).eval ρ) (r.eval ρ) :=
  run_sound (simplifyCastInst.steps_sound ρ op nneg nuw nsw src c u hw) h

/-- What `simplifyCastInst.onInst` returns refines the instruction it's given, if a `zext` or `sext` operand of it is
valid IR. -/
theorem simplifyCastInst.onInst_sound (o : Oracle) (ρ : Env) (t : Term w) (ct : t.Consistent ρ)
    (ut : t.hasUndef = false) (hw : Cast.OperandWidens t) {r : Repl w} (h : simplifyCastInst.onInst o t = .value r) :
    Refines (t.top.eval ρ) (r.eval ρ) := by
  unfold simplifyCastInst.onInst at h
  split at h
  · next id nuw nsw a =>
    exact simplifyCastInst.sound (nneg := false) ρ .trunc nuw nsw a ct.1 ut hw h
  · next id nneg a =>
    exact simplifyCastInst.sound (nuw := false) (nsw := false) ρ .zext nneg a ct.1 ut hw h
  · next id a =>
    exact simplifyCastInst.sound (nneg := false) (nuw := false) (nsw := false) ρ .sext a ct.1 ut hw h
  · cases h

/-- `IS.simplifyFreezeInst.L7631`: `freeze X` to `X`, where `X` is known not to be `undef` or poison: `freeze` of a
value is that value. -/
theorem simplifyFreezeInst.L7631 (e : Shift.Ext) (ρ : Env) (he : e.Sound ρ) (id : Nat) (op0 : Term w)
    (c : (Term.freeze id op0).Consistent ρ) (h : e.notUndefOrPoison op0 = true) :
    Refines ((Term.freeze id op0).top.eval ρ) ((Repl.old op0).eval ρ) := by
  obtain ⟨-, pick, hp⟩ := c
  have hn := he.notUndefOrPoison op0 h
  show Refines (Outcome.ok (ρ w id)) (Outcome.ok (op0.denote ρ))
  refine refines_ok ?_
  cases hd : op0.denote ρ with
  | none => exact absurd hd hn
  | some x =>
    rw [← hp, hd]
    exact Refine.refl_val _

/-- Theorem 1 for `simplifyFreezeInst`: every value the model returns refines the `freeze` it replaces, at every width,
in every run the `freeze` is consistent with, whatever it chose, and where `isGuaranteedNotToBeUndefOrPoison` is sound,
`Shift.Ext.Sound`. -/
theorem simplifyFreezeInst.sound (e : Shift.Ext) (ρ : Env) (he : e.Sound ρ) (id : Nat) (op0 : Term w)
    (c : (Term.freeze id op0).Consistent ρ) {r : Repl w} (h : simplifyFreezeInst e op0 = .value r) :
    Refines ((Term.freeze id op0).top.eval ρ) (r.eval ρ) := by
  refine run_sound (P := fun r => Refines ((Term.freeze id op0).top.eval ρ) (r.eval ρ)) ?_ h
  intro s r hmem
  simp only [simplifyFreezeInst.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  split at hmem <;> simp only [Step.fire.injEq, reduceCtorEq] at hmem
  obtain ⟨-, rfl⟩ := hmem
  exact simplifyFreezeInst.L7631 e ρ he id op0 c (by assumption)

/-- What `simplifyFreezeInst.onInst` returns refines the instruction it's given. -/
theorem simplifyFreezeInst.onInst_sound (o : Oracle) (ρ : Env) (ho : o.Sound ρ) (t : Term w)
    (ct : t.Consistent ρ) {r : Repl w} (h : simplifyFreezeInst.onInst o t = .value r) :
    Refines (t.top.eval ρ) (r.eval ρ) := by
  unfold simplifyFreezeInst.onInst at h
  split at h
  · exact simplifyFreezeInst.sound _ ρ (Shift.Ext.ofOracle_sound ho) _ _ ct h
  · cases h

end Peephole.IS
