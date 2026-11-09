import Peephole.Match
import Peephole.Oracle
import Peephole.Fold
import Peephole.IS.Add
import Peephole.Lemmas.Add
import Peephole.Lemmas.Logic

/-! # InstSimplify's bitwise folds: what they share

`simplifyAndInst`, `simplifyOrInst` and `simplifyXorInst`, at `llvm/lib/Analysis/InstructionSimplify.cpp:2071-2607`
at `llvmorg-23.1.3`, share helpers. This module holds what they need of them, and the two helpers with rewrites of
their own that more than one of them calls:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyLogicOfAddSub.L2011` | `(X + C) op (~C - X)` to 0 for `and`, -1 for `or` and `xor` |
| `IS.simplifyAndOrWithICmpEq.Simplify.L1965` | `and (icmp eq a, b), x` to false where `x` is false when `a == b`, and `or (icmp ne a, b), x` to true where `x` is true when `a == b` |
| `IS.simplifyAndOrWithICmpEq.Simplify.L1967` | the same, to the `icmp`, where `x` is the operation's identity when `a == b` |
| `IS.simplifyAndOrWithICmpEq.Simplify.L1975` | `and (icmp ne a, b), x` to `x` where `x` is false when `a == b`, and `or (icmp eq a, b), x` to `x` where `x` is true when `a == b` |

The matchers of `PatternMatch.h` that the bitwise folds use and `Peephole.Match` doesn't have are here too, in
`Peephole.IS.Logic`: the commutative ones that bind, and what each match says about values.

## What the core `Oracle` doesn't answer

Three calls in these folds ask what the core `Oracle` doesn't have. `Logic.Ext` answers them:

- `isImpliedCondition(A, B, DL, /*LHSIsTrue=*/false)`, which `simplifyOrInst` asks. Its answers are an analysis's,
  true in the run when `Logic.Ext.Sound.impliesFalse` holds, which is PASS-01's to prove, as `Oracle.Sound` is.
- `simplifyWithOpReplaced(V, Op, RepOp, Q.getWithoutUndef(), /*AllowRefinement=*/true, nullptr, MaxRecurse)`, a
  recursive call into InstSimplify, which `simplifyAndOrWithICmpEq` makes. Its answer refines `V` wherever `Op` and
  `RepOp` are the same value: `Logic.Ext.Sound.replaced`, the recursive simplifier's soundness, which the theorems that
  rest on it name.
- `isImpliedByDomCondition(ICMP_EQ, Op0, Op1, ...)`, which `simplifyByDomEq` asks. `simplifyByDomEq` isn't modelled
  here, so the answer only says when the model hands over to it, and claims nothing.

`Logic.Ext` also says what decides whether the helpers that call back into InstSimplify, which the model doesn't
follow, could answer: whether the first `simplifyBinOp` each makes answers, and whether an operand the model doesn't
look into is a `phi`, or the overflow bit of a multiplication. Those only say where the model hands over, and claim
nothing.

A fold takes `Option Logic.Ext`. With `none`, the model hands over (`.delegate`) at each of these calls, and wherever
one of the helpers could answer, so it claims nothing there. `onInst` runs with `some Logic.Ext.ofTerms`, which answers
only what the operands' trees say: no implication and no dominating equality, as `Oracle.none` has it;
`simplifyWithOpReplaced` computed, by `Logic.replacedEval`, where the operand's tree says what it answers, which is
proved sound, and handed over where it doesn't; every recursive `simplifyBinOp` possibly answering; and every operand
the model doesn't look into an argument, as in the functions the comparison with `opt` builds. It's sound in every
run. -/

namespace Peephole.IS

open IRLean

variable {w : Nat}

namespace Logic

/-! ### What the core `Oracle` doesn't answer -/

/-- Answers to what the bitwise folds ask that the core `Oracle` doesn't have. -/
structure Ext where
  /-- `isImpliedCondition(A, B, DL, /*LHSIsTrue=*/false)`: `some true` if `B` is true whenever `A` is false,
  `some false` if `B` is false whenever `A` is false. -/
  impliesFalse : Term 1 → Term 1 → Option Bool
  /-- `isImpliedByDomCondition(ICMP_EQ, A, B, CxtI, DL)`: `some true` if a condition dominating the instruction says
  `A == B`. -/
  domEq : {w : Nat} → Term w → Term w → Option Bool
  /-- `simplifyWithOpReplaced(V, Op, RepOp, Q.getWithoutUndef(), /*AllowRefinement=*/true, nullptr, MaxRecurse)`:
  `some (some r)` where it answers `r`, `V` simplified with `Op` replaced by `RepOp`, `some none` where it answers
  `nullptr`, and `none` where it isn't known, where the model hands over to it. -/
  replaced : Nat → {u v : Nat} → Term u → Term v → Term v → Option (Option (Term u))
  /-- `simplifyBinOp(Opcode, LHS, RHS, Q, MaxRecurse)`, a recursive call into InstSimplify, with `Q.getWithoutUndef()`
  if the flag is set: whether it answers. `simplifyAssociativeBinOp`, `expandBinOp` and `threadBinOpOverSelect` call
  it first, and answer `nullptr` if it doesn't, so this says only where the model hands over to them. -/
  simplifies : Nat → BinOp → Bool → {w : Nat} → Term w → Term w → Bool
  /-- `isa<PHINode>(V)`, for an operand the model doesn't look into. -/
  isPhi : {w : Nat} → Term w → Bool
  /-- Whether an operand the model doesn't look into is the overflow bit of `umul.with.overflow` or
  `smul.with.overflow`, an `extractvalue`. -/
  isMulOverflowBit : {w : Nat} → Term w → Bool

/-- `e`'s answers are true in the run `ρ`: the analysis's, and the recursive simplifier's. -/
structure Ext.Sound (e : Ext) (ρ : Env) : Prop where
  /-- `isImpliedCondition` with `LHSIsTrue` false is sound: PASS-01's. -/
  impliesFalse : ∀ (a b : Term 1) (r : Bool), e.impliesFalse a b = some r → a.denote ρ = some 0#1 →
    b.denote ρ = none ∨ b.denote ρ = some (BitVec.ofBool r)
  /-- `simplifyWithOpReplaced` with `AllowRefinement` is sound: where `Op` and `RepOp` are the same value, what it
  answers refines `V`, an operand the run is consistent with. -/
  replaced : ∀ (n : Nat) {u v : Nat} (V r : Term u) (a b : Term v) (x : BitVec v),
    e.replaced n V a b = some (some r) → V.Consistent ρ → a.denote ρ = some x → b.denote ρ = some x →
      Refines (V.denote ρ) (r.denote ρ)

/-! ### `simplifyWithOpReplaced`, where the operand's tree alone says what it answers

`simplifyWithOpsReplaced` in `InstructionSimplify.cpp`, with `AllowRefinement` and `Q.getWithoutUndef()`, as
`simplifyAndOrWithICmpEq` calls it: `nullptr` if `Op` is a constant; `RepOp` if `V` is `Op`; `nullptr` at
`MaxRecurse == 0` or if `V` isn't an instruction, or is a `freeze`; else each operand recursed into, `nullptr` as soon
as one becomes `undef` or poison, and `nullptr` unless the last operand the recursion answered for changed
(`AnyReplaced = InstOp != NewInstOp`); and then `simplifyInstructionWithOperands` on the new operands. That last step
is all of InstSimplify, which isn't modelled, except where its answer is the constant folder's: an `icmp`, a cast, or
`and`, `or`, `xor`, `add` or `sub` whose new operands are all constants folds them, ignoring flags, and a `select`
whose new condition is a constant answers the arm it picks. Anywhere else `replacedEval` answers `none`: it can't tell.
An operand the model doesn't look into is taken to be an argument, as in the functions `tests/peephole.py compare`
builds. -/

/-- The flag-free result of a binary operator on two constants, as LLVM's constant folder gives it, for the operators
`replacedEval` follows. -/
def foldBin : BinOp → BitVec w → BitVec w → Option (BitVec w)
  | .and, x, y => some (x &&& y)
  | .or, x, y => some (x ||| y)
  | .xor, x, y => some (x ^^^ y)
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | _, _, _ => none

/-- `icmp p x, y` on two constants, as the constant folder gives it: `samesign` doesn't change it. -/
def foldICmp (p : Pred) (x y : BitVec w) : BitVec 1 :=
  match Pred.eval p (some x) (some y) false with
  | some b => b
  | none => 0#1

/-- The checks before the recursion: `Op` a constant, `V` being `Op`, and `MaxRecurse` at 0. `k` is the rest. -/
def replacedPre (n : Nat) {v u : Nat} (op rep : Term v) (t : Term u) (k : Option (Option (Term u))) :
    Option (Option (Term u)) :=
  if op.isConstant then some none
  else if h : u = v then
    if t.ident == op.ident then some (some (h ▸ rep)) else if n = 0 then some none else k
  else if n = 0 then some none else k

/-- One turn of the loop over an instruction's operands: the new operand, and how it sets `AnyReplaced`, or `none` if
the recursion's answer can't be told. -/
def newOp {v : Nat} (orig : Term v) : Option (Option (Term v)) → Option (Term v × Option Bool)
  | none => none
  | some none => some (orig, none)
  | some (some x) => some (x, some (x.ident != orig.ident))

/-- The loop and `simplifyInstructionWithOperands` for a binary operator. -/
def replacedBin {u : Nat} (o : BinOp) (a b : Term u) (ra rb : Option (Option (Term u))) :
    Option (Option (Term u)) :=
  match newOp a ra with
  | none => none
  | some (a', fa) =>
    if isUndefValue a' then some none else
    match newOp b rb with
    | none => none
    | some (b', fb) =>
      if isUndefValue b' then some none
      else if !(fb.getD (fa.getD false)) then some none
      else
        match apint a', apint b' with
        | some x, some y => (foldBin o x y).map fun c => some (.const c)
        | _, _ => none

/-- The loop and `simplifyInstructionWithOperands` for an `icmp`. -/
def replacedICmp {v : Nat} (p : Pred) (a b : Term v) (ra rb : Option (Option (Term v))) : Option (Option (Term 1)) :=
  match newOp a ra with
  | none => none
  | some (a', fa) =>
    if isUndefValue a' then some none else
    match newOp b rb with
    | none => none
    | some (b', fb) =>
      if isUndefValue b' then some none
      else if !(fb.getD (fa.getD false)) then some none
      else
        match apint a', apint b' with
        | some x, some y => some (some (.const (foldICmp p x y)))
        | _, _ => none

/-- The loop and `simplifyInstructionWithOperands` for a cast `f`. -/
def replacedCast {u v : Nat} (a : Term v) (ra : Option (Option (Term v))) (f : BitVec v → BitVec u) :
    Option (Option (Term u)) :=
  match newOp a ra with
  | none => none
  | some (a', fa) =>
    if isUndefValue a' then some none
    else if !(fa.getD false) then some none
    else
      match apint a' with
      | some x => some (some (.const (f x)))
      | none => none

/-- The loop and `simplifyInstructionWithOperands` for a `select` `t`: a constant condition picks an arm, unless
it's `t` itself (`PreventSelfSimplify`). -/
def replacedSelect {u : Nat} (t : Term u) (c : Term 1) (tv ev : Term u) (rc : Option (Option (Term 1)))
    (rt re : Option (Option (Term u))) : Option (Option (Term u)) :=
  match newOp c rc with
  | none => none
  | some (c', fc) =>
    if isUndefValue c' then some none else
    match newOp tv rt with
    | none => none
    | some (t', ft) =>
      if isUndefValue t' then some none else
      match newOp ev re with
      | none => none
      | some (e', fe) =>
        if isUndefValue e' then some none
        else if !(fe.getD (ft.getD (fc.getD false))) then some none
        else
          match apint c' with
          | some cv =>
            if (if cv == 1#1 then t' else e').ident == t.ident then some none
            else some (some (if cv == 1#1 then t' else e'))
          | none => none

/-- What `simplifyWithOpReplaced(V, Op, RepOp, Q.getWithoutUndef(), true, nullptr, n)` answers, where `V`'s tree says:
`some (some r)` for `r`, `some none` for `nullptr`, and `none` where it can't be told. -/
def replacedEval (n : Nat) {v : Nat} (op rep : Term v) : {u : Nat} → Term u → Option (Option (Term u))
  | _, .bin id o f a b =>
    replacedPre n op rep (.bin id o f a b) (replacedBin o a b (replacedEval (n - 1) op rep a) (replacedEval (n - 1) op rep b))
  | _, .icmp id p s a b =>
    replacedPre n op rep (.icmp id p s a b) (replacedICmp p a b (replacedEval (n - 1) op rep a)
      (replacedEval (n - 1) op rep b))
  | _, .select id c tv ev =>
    replacedPre n op rep (.select id c tv ev) (replacedSelect (.select id c tv ev) c tv ev
      (replacedEval (n - 1) op rep c) (replacedEval (n - 1) op rep tv) (replacedEval (n - 1) op rep ev))
  | w', .zext id nneg a =>
    replacedPre n op rep (.zext id nneg a) (replacedCast a (replacedEval (n - 1) op rep a) (·.setWidth w'))
  | w', .sext id a =>
    replacedPre n op rep (.sext id a) (replacedCast a (replacedEval (n - 1) op rep a) (·.signExtend w'))
  | w', .trunc id nuw nsw a =>
    replacedPre n op rep (.trunc id nuw nsw a) (replacedCast a (replacedEval (n - 1) op rep a) (·.setWidth w'))
  | _, .const c => replacedPre n op rep (.const c) (some none)
  | _, .poison => replacedPre n op rep .poison (some none)
  | _, .undef => replacedPre n op rep .undef (some none)
  | _, .var id => replacedPre n op rep (.var id) (some none)
  | _, .freeze id a => replacedPre n op rep (.freeze id a) (some none)
  | _, .un id f a => replacedPre n op rep (.un id f a) none
  | _, .bi id f a b => replacedPre n op rep (.bi id f a b) none
  | _, .fsh id l a b c => replacedPre n op rep (.fsh id l a b c) none

/-! #### `replacedEval` is sound -/

section

variable {ρ : Env}

theorem replacedPre_cases {n : Nat} {v u : Nat} {op rep : Term v} {t : Term u} {k : Option (Option (Term u))}
    {r : Term u} {x : BitVec v} (hop : op.denote ρ = some x) (hrep : rep.denote ρ = some x)
    (h : replacedPre n op rep t k = some (some r)) : Refines (t.denote ρ) (r.denote ρ) ∨ k = some (some r) := by
  unfold replacedPre at h
  split at h
  · cases h
  · split at h
    · next huv =>
      subst huv
      split at h
      · next hid =>
        simp only [Option.some.injEq] at h
        subst h
        left
        rw [Term.denote_of_ident (by simpa using hid), hop, hrep]
        exact Refine.refl_val _
      · split at h
        · cases h
        · exact .inr h
    · split at h
      · cases h
      · exact .inr h

/-- What a turn of the loop gives refines the operand. -/
theorem newOp_refines {v : Nat} {orig a' : Term v} {r : Option (Option (Term v))} {f : Option Bool}
    (h : newOp orig r = some (a', f)) (ih : ∀ y, r = some (some y) → Refines (orig.denote ρ) (y.denote ρ)) :
    Refines (orig.denote ρ) (a'.denote ρ) := by
  unfold newOp at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Refine.refl_val _
  · next y =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ih _ rfl

theorem refines_const {v : Nat} {a : Val v} {t : Term v} {x : BitVec v} (h : Refines a (t.denote ρ))
    (hx : apint t = some x) : a = none ∨ a = some x := by
  rw [apint_denote hx, Lemmas.Logic.refines_iff] at h
  rcases h with h | h
  · exact .inl h
  · exact .inr h.symm

theorem foldBin_refines {w : Nat} {o : BinOp} {f : Flags} {x y c : BitVec w} {A B : Val w} {V : Val w}
    (hc : foldBin o x y = some c) (hA : A = none ∨ A = some x) (hB : B = none ∨ B = some y)
    (hV : o.eval f A B = Outcome.ok V) : Refines V (some c) := by
  rw [Lemmas.Logic.refines_iff]
  cases o <;> simp only [foldBin, reduceCtorEq, Option.some.injEq] at hc <;> subst hc <;>
    simp only [BinOp.eval] at hV <;> have hV := ok_inj hV <;> subst hV <;>
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> (try exact .inl rfl)
  · rcases Lemmas.Logic.add_cases x y f.nuw f.nsw with h | h <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
  · rcases Lemmas.Logic.sub_cases x y f.nuw f.nsw with h | ⟨-, h⟩ <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
  · exact .inr rfl
  · rcases Lemmas.Logic.or_cases x y f.disjoint with h | h <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
  · exact .inr rfl

theorem foldICmp_refines {v : Nat} {p : Pred} {s : Bool} {x y : BitVec v} {A B : Val v}
    (hA : A = none ∨ A = some x) (hB : B = none ∨ B = some y) : Refines (p.eval A B s) (some (foldICmp p x y)) := by
  rw [Lemmas.Logic.refines_iff]
  rcases hA with rfl | rfl
  · left; cases p <;> rfl
  rcases hB with rfl | rfl
  · left; cases p <;> cases x <;> rfl
  cases p <;> simp only [Pred.eval, foldICmp, Val.icmpEq, Val.icmpNe, Val.icmpUgt, Val.icmpUge, Val.icmpUlt,
    Val.icmpUle, Val.icmpSgt, Val.icmpSge, Val.icmpSlt, Val.icmpSle, Val.icmp, Bool.false_and, Bool.false_eq_true,
    ite_false] <;> split <;> simp

theorem replacedEval_sound (n : Nat) {v : Nat} (op rep : Term v) (x : BitVec v) (hop : op.denote ρ = some x)
    (hrep : rep.denote ρ = some x) :
    ∀ {u : Nat} (t : Term u) (r : Term u), replacedEval n op rep t = some (some r) → t.Consistent ρ →
      Refines (t.denote ρ) (r.denote ρ) := by
  intro u t
  induction t generalizing n with
  | bin id o f a b iha ihb =>
    intro r h hc
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    obtain ⟨ca, cb, hd⟩ := hc
    unfold replacedBin at h
    split at h
    · cases h
    · next a' fa ha =>
      split at h
      · cases h
      · split at h
        · cases h
        · next b' fb hb =>
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · next xa xb hxa hxb =>
                cases hcst : foldBin o xa xb with
                | none => simp [hcst] at h
                | some c =>
                  simp only [hcst, Option.map_some, Option.some.injEq] at h
                  subst h
                  have ra := newOp_refines ha fun y hy => iha (n - 1) y hy ca
                  have rb := newOp_refines hb fun y hy => ihb (n - 1) y hy cb
                  exact foldBin_refines hcst (refines_const ra hxa) (refines_const rb hxb) hd
              · cases h
  | icmp id p s a b iha ihb =>
    intro r h hc
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    obtain ⟨ca, cb, hd⟩ := hc
    unfold replacedICmp at h
    split at h
    · cases h
    · next a' fa ha =>
      split at h
      · cases h
      · split at h
        · cases h
        · next b' fb hb =>
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · next xa xb hxa hxb =>
                simp only [Option.some.injEq] at h
                subst h
                have ra := newOp_refines ha fun y hy => iha (n - 1) y hy ca
                have rb := newOp_refines hb fun y hy => ihb (n - 1) y hy cb
                show Refines (ρ 1 id) (some _)
                rw [← hd]
                exact foldICmp_refines (refines_const ra hxa) (refines_const rb hxb)
              · cases h
  | select id c tv ev ihc iht ihe =>
    intro r h hc
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    obtain ⟨cc, ct, ce, hd⟩ := hc
    unfold replacedSelect at h
    split at h
    · cases h
    · next c' fc hcn =>
      split at h
      · cases h
      · split at h
        · cases h
        · next t' ft htn =>
          split at h
          · cases h
          · split at h
            · cases h
            · next e' fe hen =>
              split at h
              · cases h
              · split at h
                · cases h
                · split at h
                  · next cv hcv =>
                    have hr : r = (if cv == 1#1 then t' else e') := by
                      revert h
                      cases ((if cv == 1#1 then t' else e').ident == (Term.select id c tv ev).ident) <;>
                        simp <;> intro h <;> exact h.symm
                    subst hr
                    · have rc := refines_const (newOp_refines hcn fun y hy => ihc (n - 1) y hy cc) hcv
                      have rt := newOp_refines htn fun y hy => iht (n - 1) y hy ct
                      have re := newOp_refines hen fun y hy => ihe (n - 1) y hy ce
                      show Refines (ρ _ id) _
                      rw [← hd]
                      rcases rc with hcd | hcd <;> rw [hcd]
                      · exact Refine.val_none _
                      · by_cases hc1 : cv = 1#1 <;> simp [IRLean.select, hc1] <;> assumption
                  · cases h
  | zext id nneg a iha =>
    intro r h hc
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    obtain ⟨ca, hd⟩ := hc
    unfold replacedCast at h
    split at h
    · cases h
    · next a' fa ha =>
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · next xa hxa =>
            simp only [Option.some.injEq] at h
            subst h
            have ra := refines_const (newOp_refines ha fun y hy => iha (n - 1) y hy ca) hxa
            show Refines (ρ _ id) _
            rw [← hd, Lemmas.Logic.refines_iff]
            rcases ra with hz | hz <;> rw [hz]
            · exact .inl rfl
            · simp only [Val.zext]; split <;> simp [Term.denote]
          · cases h
  | sext id a iha =>
    intro r h hc
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    obtain ⟨ca, hd⟩ := hc
    unfold replacedCast at h
    split at h
    · cases h
    · next a' fa ha =>
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · next xa hxa =>
            simp only [Option.some.injEq] at h
            subst h
            have ra := refines_const (newOp_refines ha fun y hy => iha (n - 1) y hy ca) hxa
            show Refines (ρ _ id) _
            rw [← hd, Lemmas.Logic.refines_iff]
            rcases ra with hz | hz <;> rw [hz]
            · exact .inl rfl
            · simp [Val.sext, Val.map₁, Term.denote]
          · cases h
  | trunc id nuw nsw a iha =>
    intro r h hc
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    obtain ⟨ca, hd⟩ := hc
    unfold replacedCast at h
    split at h
    · cases h
    · next a' fa ha =>
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · next xa hxa =>
            simp only [Option.some.injEq] at h
            subst h
            have ra := refines_const (newOp_refines ha fun y hy => iha (n - 1) y hy ca) hxa
            show Refines (ρ _ id) _
            rw [← hd, Lemmas.Logic.refines_iff]
            rcases ra with hz | hz <;> rw [hz]
            · exact .inl rfl
            · simp only [Val.trunc]; split
              · exact .inl rfl
              · split <;> simp [Term.denote]
          · cases h
  | const c =>
    intro r h _
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    · cases h
  | poison =>
    intro r h _
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    · cases h
  | undef =>
    intro r h _
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    · cases h
  | var id =>
    intro r h _
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    · cases h
  | freeze id a _ =>
    intro r h _
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    · cases h
  | un id f a _ =>
    intro r h _
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    · cases h
  | bi id f a b _ _ =>
    intro r h _
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    · cases h
  | fsh id l a b c _ _ _ =>
    intro r h _
    simp only [replacedEval] at h
    rcases replacedPre_cases hop hrep h with h' | h
    · exact h'
    · cases h

end

/-- The extension `onInst` runs with: what the operands' trees say, and nothing else. No implication and no
dominating equality, as `Oracle.none` answers; `simplifyWithOpReplaced` computed by `replacedEval` where the tree says
what it answers, and handed over where it doesn't; a recursive `simplifyBinOp` that may answer, so the model hands over
to the helpers that make one; and every operand the model doesn't look into an argument, as in the functions the
comparison with `opt` builds. -/
def Ext.ofTerms : Ext where
  impliesFalse _ _ := Option.none
  domEq _ _ := Option.none
  replaced n _ _ V a b := replacedEval n a b V
  simplifies _ _ _ _ _ _ := true
  isPhi _ := false
  isMulOverflowBit _ := false

theorem Ext.ofTerms_sound (ρ : Env) : Ext.ofTerms.Sound ρ where
  impliesFalse _ _ _ h := by simp [Ext.ofTerms] at h
  replaced := by
    intro n u v V r a b x h hV ha hb
    exact replacedEval_sound n a b x ha hb V r h hV

/-- `some Ext.ofTerms`, as `onInst` gives it, is sound in every run. -/
theorem some_ofTerms_sound (ρ : Env) : ∀ e, some Ext.ofTerms = some e → e.Sound ρ := by
  intro e h
  cases h
  exact Ext.ofTerms_sound ρ

/-! ### Calls to other folds -/

/-- `if (Value *V = callee(...)) return V;`, for a callee modelled here as `steps`: what it answers, under the site
that answered, or the next step if it answers `nullptr`. -/
def forward (steps : List (Step w)) : Step w :=
  match run steps with
  | .value r => .fire ((firedSite steps).getD "") r
  | .null => .next
  | .delegated c => .delegate c

/-- `return callee(...);`: as `forward`, but `nullptr` ends the caller too. -/
def tail (steps : List (Step w)) : Step w :=
  match run steps with
  | .value r => .fire ((firedSite steps).getD "") r
  | .null => .decline
  | .delegated c => .delegate c

theorem run_of_forward {steps : List (Step w)} {s : String} {r : Repl w} (h : forward steps = .fire s r) :
    run steps = .value r := by
  unfold forward at h
  split at h <;> simp_all

theorem run_of_tail {steps : List (Step w)} {s : String} {r : Repl w} (h : tail steps = .fire s r) :
    run steps = .value r := by
  unfold tail at h
  split at h <;> simp_all

/-! ### Matchers -/

/-- Whether a binary operator has opcode `op`: `isa<BinaryOperator>` and `getOpcode() == op`. -/
def isBin (op : BinOp) (t : Term w) : Bool := (binop? op t).isSome

/-- `m_c_<Op>(L, R)`, where `L` and `R` test their operand: operand 0 for `L` and operand 1 for `R`, or the other way
round. -/
def chas (op : BinOp) (l r : Term w → Bool) (t : Term w) : Bool :=
  match binop? op t with
  | some (_, a, b) => (l a && r b) || (l b && r a)
  | none => false

/-- `m_c_<Op>(L, R)`, where `L` and `R` bind: operand 0 for `L` and operand 1 for `R`, else the other way round, and
what they bound in the first order that matches. -/
def cbind {α β : Type} (op : BinOp) (l : Term w → Option α) (r : Term w → Option β) (t : Term w) :
    Option (α × β) :=
  match binop? op t with
  | some (_, a, b) =>
    match l a, r b with
    | some x, some y => some (x, y)
    | _, _ =>
      match l b, r a with
      | some x, some y => some (x, y)
      | _, _ => none
  | none => none

/-- `m_Not(L)`, `m_c_Xor(m_AllOnes(), L)`, where `L` binds: operand 1 for `L` if operand 0 is all ones, else operand
0 if operand 1 is. -/
def notBind {α : Type} (l : Term w → Option α) (t : Term w) : Option α :=
  match binop? .xor t with
  | some (_, a, b) =>
    match (if allOnes a then l b else none) with
    | some x => some x
    | none => if allOnes b then l a else none
  | none => none

/-- `m_<Op>(m_Value(A), m_Value(B))`, not commutative. -/
def ops? (op : BinOp) (t : Term w) : Option (Term w × Term w) :=
  (binop? op t).map fun (_, a, b) => (a, b)

/-- `m_c_<Op>(m_Specific(A), m_Specific(B))`. -/
def isOf (op : BinOp) (a b t : Term w) : Bool := chas op (specific a) (specific b) t

/-- `m_c_Xor(m_Not(m_Value(A)), m_Value(B))` and the like: an operand that's a `not`, binding what it negates, and
the other operand. -/
def notAnd (op : BinOp) (t : Term w) : Option (Term w × Term w) := cbind op not? some t

/-- `m_c_<Op>(m_CombineAnd(m_Value(NotA), m_Not(m_Value(A))), m_Value(B))`: as `notAnd`, also binding the `not`. -/
def notAnd' (op : BinOp) (t : Term w) : Option ((Term w × Term w) × Term w) :=
  cbind op (fun u => (not? u).map fun a => (u, a)) some t

/-- `m_ICmpLike(Pred, m_Value(A), m_Value(B))` with `ICmpInst::isEquality(Pred)`: an `icmp eq` or `icmp ne`, or
`trunc nuw X to i1`, which is `icmp ne X, 0`. Whether the predicate is `eq`, and `A` and `B`, at their width. -/
def icmpEq? : {w : Nat} → Term w → Option (Bool × ((v : Nat) × Term v × Term v))
  | _, .icmp _ .eq _ a b => some (true, ⟨_, a, b⟩)
  | _, .icmp _ .ne _ a b => some (false, ⟨_, a, b⟩)
  | w, .trunc (v := v) _ nuw _ a => if nuw && w == 1 then some (false, ⟨v, a, .const 0#v⟩) else none
  | _, _ => none

/-- `APInt::isMask()`: a nonzero mask of low bits, `0+1+`. -/
def isMask (c : BitVec w) : Bool := c != 0#w && c &&& (c + 1#w) == 0#w

/-! ### What a match says about values -/

variable {ρ : Env}

theorem isMask_spec {c : BitVec w} (h : isMask c = true) : c &&& (c + 1#w) = 0#w := by
  simp only [isMask, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  exact h.2

/-- A matched `and`, `or` or `xor`'s value and operands. -/
theorem and_denote {t a b : Term w} {f : Flags} (h : binop? .and t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.and (a.denote ρ) (b.denote ρ) := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem or_denote {t a b : Term w} {f : Flags} (h : binop? .or t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.or (a.denote ρ) (b.denote ρ) f.disjoint := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem xor_denote' {t a b : Term w} {f : Flags} (h : binop? .xor t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.xor (a.denote ρ) (b.denote ρ) := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem add_denote {t a b : Term w} {f : Flags} (h : binop? .add t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.add (a.denote ρ) (b.denote ρ) f.nuw f.nsw := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem sub_denote' {t a b : Term w} {f : Flags} (h : binop? .sub t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.sub (a.denote ρ) (b.denote ρ) f.nuw f.nsw := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem shl_denote {t a b : Term w} {f : Flags} (h : binop? .shl t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.shl (a.denote ρ) (b.denote ρ) f.nuw f.nsw := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem lshr_denote {t a b : Term w} {f : Flags} (h : binop? .lshr t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.lshr (a.denote ρ) (b.denote ρ) f.exact := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

/-- `m_Not(m_Value(A))`'s value, as `xor A, -1`, whichever operand the `-1` was. -/
theorem not?_denote {t a : Term w} (h : not? t = some a) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ t.denote ρ = Val.xor (a.denote ρ) (some (BitVec.allOnes w)) := by
  unfold not? at h
  split at h
  · next f p q hx =>
    obtain ⟨hp, hq, hd⟩ := xor_denote' hx hc
    split at h
    · next h1 => cases h; exact ⟨hq, by rw [hd, cst_eq h1, Lemmas.Logic.xor_comm]⟩
    · split at h
      · next _ h2 => cases h; exact ⟨hp, by rw [hd, cst_eq h2]⟩
      · cases h
  · cases h

/-- `m_Not(P)`'s value, as `xor A, -1`, for the `A` that matches `P`. -/
theorem notWith_denote {p : Term w → Bool} {t : Term w} (h : notWith p t = true) (hc : t.Consistent ρ) :
    ∃ a, p a = true ∧ a.Consistent ρ ∧ t.denote ρ = Val.xor (a.denote ρ) (some (BitVec.allOnes w)) := by
  unfold notWith at h
  split at h
  · next f x y hx =>
    obtain ⟨hp, hq, hd⟩ := xor_denote' hx hc
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨y, h2, hq, by rw [hd, cst_eq h1, Lemmas.Logic.xor_comm]⟩
    · exact ⟨x, h2, hp, by rw [hd, cst_eq h1]⟩
  · cases h

theorem notBind_denote {α : Type} {l : Term w → Option α} {t : Term w} {x : α} (h : notBind l t = some x)
    (hc : t.Consistent ρ) :
    ∃ a, l a = some x ∧ a.Consistent ρ ∧ t.denote ρ = Val.xor (a.denote ρ) (some (BitVec.allOnes w)) := by
  unfold notBind at h
  split at h
  · next f p q hx =>
    obtain ⟨hp, hq, hd⟩ := xor_denote' hx hc
    split at h
    · next y hy =>
      cases h
      split at hy
      · next h1 => exact ⟨q, hy, hq, by rw [hd, cst_eq h1, Lemmas.Logic.xor_comm]⟩
      · cases hy
    · split at h
      · next h2 => exact ⟨p, h, hp, by rw [hd, cst_eq h2]⟩
      · cases h
  · cases h

/-- What a commutative matcher on `and` bound, with the operands in the matcher's order. -/
theorem cbind_and {α β : Type} {l : Term w → Option α} {r : Term w → Option β} {t : Term w} {x : α} {y : β}
    (h : cbind .and l r t = some (x, y)) (hc : t.Consistent ρ) :
    ∃ a b, l a = some x ∧ r b = some y ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.and (a.denote ρ) (b.denote ρ) := by
  unfold cbind at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := and_denote hb hc
    split at h
    · next x' y' h1 h2 => cases h; exact ⟨p, q, h1, h2, hp, hq, hd⟩
    · split at h
      · next x' y' h1 h2 =>
        cases h; exact ⟨q, p, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.and_comm]⟩
      · cases h
  · cases h

theorem cbind_or {α β : Type} {l : Term w → Option α} {r : Term w → Option β} {t : Term w} {x : α} {y : β}
    (h : cbind .or l r t = some (x, y)) (hc : t.Consistent ρ) :
    ∃ a b d, l a = some x ∧ r b = some y ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.or (a.denote ρ) (b.denote ρ) d := by
  unfold cbind at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := or_denote hb hc
    split at h
    · next x' y' h1 h2 => cases h; exact ⟨p, q, _, h1, h2, hp, hq, hd⟩
    · split at h
      · next x' y' h1 h2 =>
        cases h; exact ⟨q, p, _, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.or_comm]⟩
      · cases h
  · cases h

theorem cbind_xor {α β : Type} {l : Term w → Option α} {r : Term w → Option β} {t : Term w} {x : α} {y : β}
    (h : cbind .xor l r t = some (x, y)) (hc : t.Consistent ρ) :
    ∃ a b, l a = some x ∧ r b = some y ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.xor (a.denote ρ) (b.denote ρ) := by
  unfold cbind at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := xor_denote' hb hc
    split at h
    · next x' y' h1 h2 => cases h; exact ⟨p, q, h1, h2, hp, hq, hd⟩
    · split at h
      · next x' y' h1 h2 =>
        cases h; exact ⟨q, p, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.xor_comm]⟩
      · cases h
  · cases h

/-- What a commutative matcher on `and` tested, with the operands in the matcher's order. -/
theorem chas_and {l r : Term w → Bool} {t : Term w} (h : chas .and l r t = true) (hc : t.Consistent ρ) :
    ∃ a b, l a = true ∧ r b = true ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.and (a.denote ρ) (b.denote ρ) := by
  unfold chas at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := and_denote hb hc
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨p, q, h1, h2, hp, hq, hd⟩
    · exact ⟨q, p, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.and_comm]⟩
  · cases h

theorem chas_or {l r : Term w → Bool} {t : Term w} (h : chas .or l r t = true) (hc : t.Consistent ρ) :
    ∃ a b d, l a = true ∧ r b = true ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.or (a.denote ρ) (b.denote ρ) d := by
  unfold chas at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := or_denote hb hc
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨p, q, _, h1, h2, hp, hq, hd⟩
    · exact ⟨q, p, _, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.or_comm]⟩
  · cases h

theorem chas_xor {l r : Term w → Bool} {t : Term w} (h : chas .xor l r t = true) (hc : t.Consistent ρ) :
    ∃ a b, l a = true ∧ r b = true ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.xor (a.denote ρ) (b.denote ρ) := by
  unfold chas at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := xor_denote' hb hc
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨p, q, h1, h2, hp, hq, hd⟩
    · exact ⟨q, p, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.xor_comm]⟩
  · cases h

/-- `m_c_And(m_Specific(A), m_Specific(B))` and the like: the operands' values are `A`'s and `B`'s. -/
theorem isOf_and {a b t : Term w} (h : isOf .and a b t = true) (hc : t.Consistent ρ) :
    t.denote ρ = Val.and (a.denote ρ) (b.denote ρ) := by
  obtain ⟨p, q, h1, h2, -, -, hd⟩ := chas_and h hc
  rw [hd, specific_denote h1, specific_denote h2]

theorem isOf_or {a b t : Term w} (h : isOf .or a b t = true) (hc : t.Consistent ρ) :
    ∃ d, t.denote ρ = Val.or (a.denote ρ) (b.denote ρ) d := by
  obtain ⟨p, q, d, h1, h2, -, -, hd⟩ := chas_or h hc
  exact ⟨d, by rw [hd, specific_denote h1, specific_denote h2]⟩

theorem isOf_xor {a b t : Term w} (h : isOf .xor a b t = true) (hc : t.Consistent ρ) :
    t.denote ρ = Val.xor (a.denote ρ) (b.denote ρ) := by
  obtain ⟨p, q, h1, h2, -, -, hd⟩ := chas_xor h hc
  rw [hd, specific_denote h1, specific_denote h2]

end Logic

open Logic

/-! ### The instructions the folds replace -/

namespace Logic

/-- The `and` a fold replaces. -/
def andSrc (op0 op1 : Term w) : Repl w := .bin .and {} (.old op0) (.old op1)

/-- The `or` a fold replaces, with its `disjoint` flag. -/
def orSrc (op0 op1 : Term w) (disjoint : Bool) : Repl w := .bin .or { disjoint := disjoint } (.old op0) (.old op1)

/-- The `xor` a fold replaces. -/
def xorSrc (op0 op1 : Term w) : Repl w := .bin .xor {} (.old op0) (.old op1)

theorem andSrc_eval (ρ : Env) (op0 op1 : Term w) :
    (andSrc op0 op1).eval ρ = Outcome.ok (Val.and (op0.denote ρ) (op1.denote ρ)) := rfl

theorem orSrc_eval (ρ : Env) (op0 op1 : Term w) (d : Bool) :
    (orSrc op0 op1 d).eval ρ = Outcome.ok (Val.or (op0.denote ρ) (op1.denote ρ) d) := rfl

theorem xorSrc_eval (ρ : Env) (op0 op1 : Term w) :
    (xorSrc op0 op1).eval ρ = Outcome.ok (Val.xor (op0.denote ρ) (op1.denote ρ)) := rfl

theorem andSrc_comm (ρ : Env) (op0 op1 : Term w) : (andSrc op0 op1).eval ρ = (andSrc op1 op0).eval ρ := by
  rw [andSrc_eval, andSrc_eval, Lemmas.Logic.and_comm]

theorem orSrc_comm (ρ : Env) (op0 op1 : Term w) (d : Bool) : (orSrc op0 op1 d).eval ρ = (orSrc op1 op0 d).eval ρ := by
  rw [orSrc_eval, orSrc_eval, Lemmas.Logic.or_comm]

theorem xorSrc_comm (ρ : Env) (op0 op1 : Term w) : (xorSrc op0 op1).eval ρ = (xorSrc op1 op0).eval ρ := by
  rw [xorSrc_eval, xorSrc_eval, Lemmas.Logic.xor_comm]

/-- The bitwise operation a fold replaces: `and`, `or disjoint` or `xor`. -/
def logicSrc (opc : BinOp) (disjoint : Bool) (op0 op1 : Term w) : Repl w :=
  .bin opc { disjoint := disjoint } (.old op0) (.old op1)

end Logic

/-! ## `simplifyLogicOfAddSub` -/

namespace Logic

/-- `m_Add(m_Value(X), m_Constant(C1))` on `A` and `m_Sub(m_Constant(C2), m_Specific(X))` on `S`: `X`, `C1` and
`C2`. -/
def addSubPair (a s : Term w) : Option (Term w × Term w × Term w) :=
  match binop? .add a with
  | some (_, x, c1) =>
    if c1.isConstant then
      match binop? .sub s with
      | some (_, c2, x') => if c2.isConstant && specific x x' then some (x, c1, c2) else none
      | none => none
    else none
  | none => none

/-- `ConstantExpr::getNot(C)` on a constant: `~C` for a `ConstantInt`, and poison and `undef` for themselves, as the
constant folder has `xor`. -/
def notConst : Term w → Option (Term w)
  | .const c => some (.const (~~~c))
  | .poison => some .poison
  | .undef => some .undef
  | _ => none

/-- The `add` and the `sub` `simplifyLogicOfAddSub` matched, either way round. -/
def addSubPairs (op0 op1 : Term w) : Option (Term w × Term w × Term w) :=
  match addSubPair op0 op1 with
  | some p => some p
  | none => addSubPair op1 op0

end Logic

/-- `simplifyLogicOfAddSub(Op0, Op1, Opcode)`, step by step: the `add` and `sub` either way round, then whether
`~C1 == C2`, by address, as LLVM uniques constants. -/
def simplifyLogicOfAddSub.steps (op0 op1 : Term w) (opc : BinOp) : List (Step w) :=
  [ match addSubPairs op0 op1 with
    | some (_, c1, c2) =>
      match notConst c1 with
      | some nc1 =>
        -- (X + C) & (~C - X) --> (X + C) & ~(X + C) --> 0
        -- (X + C) | (~C - X) --> (X + C) | ~(X + C) --> -1
        -- (X + C) ^ (~C - X) --> (X + C) ^ ~(X + C) --> -1
        if nc1.ident == c2.ident then
          .fire "IS.simplifyLogicOfAddSub.L2011"
            (if opc == .and then .const 0#w else .const (BitVec.allOnes w))
        else .next
      | none => .next
    | none => .next ]

namespace Logic

theorem addSubPair_denote {ρ : Env} {a s x c1 c2 : Term w} (h : addSubPair a s = some (x, c1, c2))
    (ca : a.Consistent ρ) (cs : s.Consistent ρ) (us : s.hasUndef = false) :
    c2.hasUndef = false ∧ ∃ f1 f2 f3 f4, a.denote ρ = Val.add (x.denote ρ) (c1.denote ρ) f1 f2 ∧
      s.denote ρ = Val.sub (c2.denote ρ) (x.denote ρ) f3 f4 := by
  unfold addSubPair at h
  split at h
  · next f x' c1' ha =>
    split at h
    · split at h
      · next f' c2' x'' hs =>
        split at h
        · next hh =>
          cases h
          simp only [Bool.and_eq_true] at hh
          obtain ⟨-, -, hda⟩ := add_denote ha ca
          obtain ⟨-, -, hds⟩ := sub_denote' hs cs
          exact ⟨(binop?_noUndef hs us).1, _, _, _, _, hda, by rw [hds, specific_denote hh.2]⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- What `notConst` says, with no `undef`: poison for poison, `~k` for `k`. -/
theorem notConst_denote {ρ : Env} {c d e : Term w} (h : notConst c = some d) (hid : d.ident = e.ident)
    (hu : e.hasUndef = false) :
    (c.denote ρ = none ∧ e.denote ρ = none) ∨ ∃ k, c.denote ρ = some k ∧ e.denote ρ = some (~~~k) := by
  cases c <;> simp only [notConst, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · next k => exact .inr ⟨k, rfl, by rw [← Term.denote_of_ident hid]; rfl⟩
  · exact .inl ⟨rfl, by rw [← Term.denote_of_ident hid]; rfl⟩
  · cases e <;> simp_all [Term.ident, Term.hasUndef]

end Logic

/-- `IS.simplifyLogicOfAddSub.L2011`: `(X + C) op (~C - X)`, either way round, to 0 for `and` and -1 for `or` and
`xor`. `C` may be poison, which makes both poison. -/
theorem simplifyLogicOfAddSub.L2011 (ρ : Env) (opc : BinOp) (d : Bool) (op0 op1 x c1 c2 nc1 : Term w)
    (c0 : op0.Consistent ρ) (c1' : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false)
    (hopc : opc = .and ∨ opc = .or ∨ opc = .xor) (hp : addSubPairs op0 op1 = some (x, c1, c2))
    (hn : notConst c1 = some nc1) (hid : nc1.ident = c2.ident) :
    Refines ((logicSrc opc d op0 op1).eval ρ)
      ((if opc == .and then Repl.const 0#w else .const (BitVec.allOnes w)).eval ρ) := by
  -- The values of the two operands, as `add` then `sub`.
  have key : ∃ A S, (Val.and (op0.denote ρ) (op1.denote ρ) = Val.and A S ∧
      Val.or (op0.denote ρ) (op1.denote ρ) d = Val.or A S d ∧ Val.xor (op0.denote ρ) (op1.denote ρ) = Val.xor A S) ∧
      ∃ f1 f2 f3 f4, A = Val.add (x.denote ρ) (c1.denote ρ) f1 f2 ∧ S = Val.sub (c2.denote ρ) (x.denote ρ) f3 f4 ∧
        c2.hasUndef = false := by
    unfold addSubPairs at hp
    split at hp
    · next p hp' =>
      cases hp
      obtain ⟨hu, f1, f2, f3, f4, ha, hs⟩ := addSubPair_denote hp' c0 c1' u1
      exact ⟨_, _, ⟨rfl, rfl, rfl⟩, f1, f2, f3, f4, ha, hs, hu⟩
    · obtain ⟨hu, f1, f2, f3, f4, ha, hs⟩ := addSubPair_denote hp c1' c0 u0
      exact ⟨_, _, ⟨Lemmas.Logic.and_comm _ _, Lemmas.Logic.or_comm _ _ _, Lemmas.Logic.xor_comm _ _⟩,
        f1, f2, f3, f4, ha, hs, hu⟩
  obtain ⟨A, S, ⟨hand, hor, hxor⟩, f1, f2, f3, f4, rfl, rfl, hu⟩ := key
  rcases hopc with rfl | rfl | rfl
  · show Refines (Outcome.ok (Val.and (op0.denote ρ) (op1.denote ρ))) (Outcome.ok (some 0#w))
    refine refines_ok ?_
    rw [hand]
    rcases notConst_denote hn hid hu with ⟨h1, -⟩ | ⟨k, h1, h2⟩
    · rw [h1, Lemmas.add_none_right, Lemmas.Logic.and_none_left]; exact Refine.val_none _
    · rw [h1, h2]; exact Lemmas.and_add_sub_not_refines _ _ _ _ _ _
  · show Refines (Outcome.ok (Val.or (op0.denote ρ) (op1.denote ρ) d)) (Outcome.ok (some (BitVec.allOnes w)))
    refine refines_ok ?_
    rw [hor]
    rcases notConst_denote hn hid hu with ⟨h1, -⟩ | ⟨k, h1, h2⟩
    · rw [h1, Lemmas.add_none_right, Lemmas.Logic.or_none_left]; exact Refine.val_none _
    · rw [h1, h2]; exact Lemmas.or_add_sub_not_refines _ _ _ _ _ _ _
  · show Refines (Outcome.ok (Val.xor (op0.denote ρ) (op1.denote ρ))) (Outcome.ok (some (BitVec.allOnes w)))
    refine refines_ok ?_
    rw [hxor]
    rcases notConst_denote hn hid hu with ⟨h1, -⟩ | ⟨k, h1, h2⟩
    · rw [h1, Lemmas.add_none_right, Lemmas.Logic.xor_none_left]; exact Refine.val_none _
    · rw [h1, h2]; exact Lemmas.xor_add_sub_not_refines _ _ _ _ _ _

/-- Theorem 1 for `simplifyLogicOfAddSub`: what it returns refines the `and`, `or` or `xor` it's called on. -/
theorem simplifyLogicOfAddSub.sound (ρ : Env) (opc : BinOp) (d : Bool) (op0 op1 : Term w)
    (cs0 : op0.Consistent ρ) (cs1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false)
    (hopc : opc = .and ∨ opc = .or ∨ opc = .xor) {r : Repl w}
    (h : run (simplifyLogicOfAddSub.steps op0 op1 opc) = .value r) :
    Refines ((logicSrc opc d op0 op1).eval ρ) (r.eval ρ) := by
  refine run_sound (P := fun r => Refines ((logicSrc opc d op0 op1).eval ρ) (r.eval ρ)) (fun s r hmem => ?_) h
  simp only [simplifyLogicOfAddSub.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  split at hmem
  · next x c1 c2 hp =>
    split at hmem
    · next nc1 hn =>
      split at hmem
      · next hid =>
        simp only [Step.fire.injEq] at hmem
        obtain ⟨-, rfl⟩ := hmem
        exact simplifyLogicOfAddSub.L2011 ρ opc d op0 op1 x c1 c2 nc1 cs0 cs1 u0 u1 hopc hp hn
          (by simpa using hid)
      · simp at hmem
    · simp at hmem
  · simp at hmem

/-! ## `simplifyAndOrWithICmpEq` -/

namespace Logic

/-- `ConstantExpr::getBinOpAbsorber(Opcode, Ty)`: 0 for `and`, -1 for `or`. -/
def absorber (isAnd : Bool) : BitVec w := if isAnd then 0#w else BitVec.allOnes w

/-- `ConstantExpr::getBinOpIdentity(Opcode, Ty)`: -1 for `and`, 0 for `or`. -/
def identity (isAnd : Bool) : BitVec w := if isAnd then BitVec.allOnes w else 0#w

/-- The `and` or `or` `simplifyAndOrWithICmpEq` is called on. -/
def andOrSrc (isAnd d : Bool) (op0 op1 : Term w) : Repl w := if isAnd then andSrc op0 op1 else orSrc op0 op1 d

end Logic

/-- The lambda `Simplify` in `simplifyAndOrWithICmpEq`, on what `simplifyWithOpReplaced` answered, `Res`, step by
step. `isEq` is whether the predicate is `eq`. -/
def simplifyAndOrWithICmpEq.Simplify.steps (isAnd isEq : Bool) (op0 op1 res : Term w) : List (Step w) :=
  [ -- and (icmp eq a, b), x implies (a==b) inside x.
    -- or (icmp ne a, b), x implies (a==b) inside x.
    -- If x simplifies to true/false, we can simplify the and/or.
    if isEq == isAnd && res.ident == (Term.const (absorber isAnd : BitVec w)).ident then
      .fire "IS.simplifyAndOrWithICmpEq.Simplify.L1965" (.const (absorber isAnd))
    else .next,
    if isEq == isAnd && res.ident == (Term.const (identity isAnd : BitVec w)).ident then
      .fire "IS.simplifyAndOrWithICmpEq.Simplify.L1967" (.old op0)
    else .next,
    if isEq == isAnd then .decline else .next,
    -- If we have and (icmp ne a, b), x and for a==b we can simplify x to false,
    -- then we can drop the icmp, as x will already be false in the case where
    -- the icmp is false. Similar for or and true.
    if res.ident == (Term.const (absorber isAnd : BitVec w)).ident then
      .fire "IS.simplifyAndOrWithICmpEq.Simplify.L1975" (.old op1)
    else .next ]

/-- `if (Value *Res = simplifyWithOpReplaced(Op1, A, B, ...)) return Simplify(Res);`, or with `B` replaced by `A`
if `swap`. With no `Ext`, the model hands over to `simplifyWithOpReplaced`, which it doesn't follow. -/
def simplifyAndOrWithICmpEq.replacedStep (x : Option Ext) (isAnd swap : Bool) (op0 op1 : Term w) (n : Nat) :
    Step w :=
  match icmpEq? op0 with
  | none => .next
  | some (isEq, p) =>
    match x with
    | none => .delegate "simplifyWithOpReplaced"
    | some e =>
      match (if swap then e.replaced n op1 p.2.2 p.2.1 else e.replaced n op1 p.2.1 p.2.2) with
      | some (some res) => tail (simplifyAndOrWithICmpEq.Simplify.steps isAnd isEq op0 op1 res)
      | some none => .next
      | none => .delegate "simplifyWithOpReplaced"

/-- `simplifyAndOrWithICmpEq(Opcode, Op0, Op1, Q, MaxRecurse)`, step by step, `isAnd` for `and`. -/
def simplifyAndOrWithICmpEq.steps (x : Option Ext) (isAnd : Bool) (op0 op1 : Term w) (n : Nat) : List (Step w) :=
  [ -- `match(Op0, m_ICmpLike(Pred, m_Value(A), m_Value(B)))` and `ICmpInst::isEquality(Pred)`, or return nullptr.
    if (icmpEq? op0).isNone then .decline else .next,
    -- In the final case (Res == Absorber with inverted predicate), it is safe to
    -- refine poison during simplification, but not undef. For simplicity always
    -- disable undef-based folds here.
    simplifyAndOrWithICmpEq.replacedStep x isAnd false op0 op1 n,
    simplifyAndOrWithICmpEq.replacedStep x isAnd true op0 op1 n ]

namespace Logic

theorem icmpEq_true {v : Nat} {a b : Val v} {s : Bool} {c : BitVec 1} (h : Val.icmpEq a b s = some c)
    (hc : c = BitVec.allOnes 1) : ∃ x, a = some x ∧ b = some x := by
  subst hc
  cases a with
  | none => cases h
  | some x =>
    cases b with
    | none => cases h
    | some y =>
      refine ⟨x, rfl, ?_⟩
      simp only [Val.icmpEq, Val.icmp] at h
      split at h
      · cases h
      · by_cases hxy : x = y
        · rw [hxy]
        · simp [hxy] at h

theorem icmpNe_false {v : Nat} {a b : Val v} {s : Bool} {c : BitVec 1} (h : Val.icmpNe a b s = some c)
    (hc : c = 0#1) : ∃ x, a = some x ∧ b = some x := by
  subst hc
  cases a with
  | none => cases h
  | some x =>
    cases b with
    | none => cases h
    | some y =>
      refine ⟨x, rfl, ?_⟩
      simp only [Val.icmpNe, Val.icmp] at h
      split at h
      · cases h
      · by_cases hxy : x = y
        · rw [hxy]
        · simp [hxy] at h

theorem trunc_nuw_false {v : Nat} {a : Val v} {nsw : Bool} (h : Val.trunc 1 a true nsw = some 0#1) :
    a = some 0#v := by
  cases a with
  | none => cases h
  | some x =>
    simp only [Val.trunc, Bool.true_and] at h
    split at h
    · cases h
    · next h1 =>
      split at h
      · cases h
      · simp only [Option.some.injEq] at h
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h1
        rw [← h1, h]
        simp

/-- What a match of `m_ICmpLike` with an equality predicate says: the operation is on `i1`, and where the `icmp` is
true for `eq`, or false for `ne`, `A` and `B` are the same value. -/
theorem icmpEq?_spec {ρ : Env} {op0 : Term w} {isEq : Bool} {p : (v : Nat) × Term v × Term v}
    (h : icmpEq? op0 = some (isEq, p)) (hc : op0.Consistent ρ) :
    w = 1 ∧ ∀ c : BitVec w, op0.denote ρ = some c → c = (if isEq then BitVec.allOnes w else 0#w) →
      ∃ x, p.2.1.denote ρ = some x ∧ p.2.2.denote ρ = some x := by
  cases op0 with
  | icmp id pr s a b =>
    refine ⟨rfl, fun c hd hcv => ?_⟩
    obtain ⟨-, -, he⟩ := hc
    simp only [Term.denote] at hd
    rw [hd] at he
    cases pr <;> simp only [icmpEq?, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h
    · exact icmpEq_true he hcv
    · exact icmpNe_false he hcv
  | trunc id nuw nsw a =>
    simp only [icmpEq?] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, fun c hd hcv => ⟨0#_, ?_, rfl⟩⟩
      obtain ⟨-, he⟩ := hc
      simp only [Term.denote] at hd
      simp only [Bool.false_eq_true, ite_false] at hcv
      rw [hd, hcv] at he
      exact trunc_nuw_false he
    · cases h
  | _ => simp [icmpEq?] at h

end Logic

/-- `IS.simplifyAndOrWithICmpEq.Simplify.L1965`: `and (icmp eq a, b), x` to false where `x` is false when `a == b`,
and `or (icmp ne a, b), x` to true where `x` is true when `a == b`. `hres` says `x` refines `Res` wherever the `icmp`
says `a == b`, which `simplifyWithOpReplaced`'s soundness gives. -/
theorem simplifyAndOrWithICmpEq.Simplify.L1965 (ρ : Env) (isAnd isEq d : Bool) (op0 op1 res : Term 1)
    (hres : ∀ c, op0.denote ρ = some c → c = (if isEq then BitVec.allOnes 1 else 0#1) →
      Refines (op1.denote ρ) (res.denote ρ))
    (h : (isEq == isAnd && res.ident == (Term.const (absorber isAnd : BitVec 1)).ident) = true) :
    Refines ((andOrSrc isAnd d op0 op1).eval ρ) ((Repl.const (absorber isAnd : BitVec 1)).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, hid⟩ := h
  have hr := Term.denote_of_ident (ρ := ρ) hid
  cases isEq <;> simp only [andOrSrc, absorber, Bool.false_eq_true, ite_false, ite_true] at hr ⊢ <;>
    rw [Repl.eval_const] <;> refine refines_ok ?_
  · refine Lemmas.or_refines_true_of_implies _ _ d fun hc => ?_
    have := hres _ hc rfl
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm.trans (by decide)
  · refine Lemmas.and_refines_false_of_implies _ _ fun hc => ?_
    have := hres _ hc (by decide)
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm

/-- `IS.simplifyAndOrWithICmpEq.Simplify.L1967`: `and (icmp eq a, b), x` to the `icmp` where `x` is true when
`a == b`, and `or (icmp ne a, b), x` to the `icmp` where `x` is false when `a == b`. -/
theorem simplifyAndOrWithICmpEq.Simplify.L1967 (ρ : Env) (isAnd isEq d : Bool) (op0 op1 res : Term 1)
    (hres : ∀ c, op0.denote ρ = some c → c = (if isEq then BitVec.allOnes 1 else 0#1) →
      Refines (op1.denote ρ) (res.denote ρ))
    (h : (isEq == isAnd && res.ident == (Term.const (identity isAnd : BitVec 1)).ident) = true) :
    Refines ((andOrSrc isAnd d op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, hid⟩ := h
  have hr := Term.denote_of_ident (ρ := ρ) hid
  cases isEq <;> simp only [andOrSrc, identity, Bool.false_eq_true, ite_false, ite_true] at hr ⊢ <;>
    rw [Repl.eval_old] <;> refine refines_ok ?_
  · refine Lemmas.or_refines_left_of_implies _ _ d fun hc => ?_
    have := hres _ hc rfl
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm
  · refine Lemmas.and_refines_left_of_implies _ _ fun hc => ?_
    have := hres _ hc (by decide)
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm.trans (by decide)

/-- `IS.simplifyAndOrWithICmpEq.Simplify.L1975`: `and (icmp ne a, b), x` to `x` where `x` is false when `a == b`, and
`or (icmp eq a, b), x` to `x` where `x` is true when `a == b`. -/
theorem simplifyAndOrWithICmpEq.Simplify.L1975 (ρ : Env) (isAnd isEq d : Bool) (op0 op1 res : Term 1)
    (hres : ∀ c, op0.denote ρ = some c → c = (if isEq then BitVec.allOnes 1 else 0#1) →
      Refines (op1.denote ρ) (res.denote ρ))
    (hp : (isEq == isAnd) = false) (h : (res.ident == (Term.const (absorber isAnd : BitVec 1)).ident) = true) :
    Refines ((andOrSrc isAnd d op0 op1).eval ρ) ((Repl.old op1).eval ρ) := by
  simp only [beq_iff_eq] at h
  have hr := Term.denote_of_ident (ρ := ρ) h
  cases isAnd <;> cases isEq <;> simp at hp <;>
    simp only [andOrSrc, absorber, Bool.false_eq_true, ite_false, ite_true] at hr ⊢ <;>
    rw [Repl.eval_old] <;> refine refines_ok ?_
  · refine Lemmas.or_refines_right_of_true _ _ d fun hc => ?_
    have := hres _ hc (by decide)
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm.trans (by decide)
  · refine Lemmas.and_refines_right_of_false _ _ fun hc => ?_
    have := hres _ hc rfl
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm

/-- Theorem 1 for the lambda `Simplify`: what it returns refines the `and` or `or`, given `x` refines `Res` wherever
the `icmp` says `a == b`. -/
theorem simplifyAndOrWithICmpEq.Simplify.sound (ρ : Env) (isAnd isEq d : Bool) (op0 op1 res : Term 1)
    (hres : ∀ c, op0.denote ρ = some c → c = (if isEq then BitVec.allOnes 1 else 0#1) →
      Refines (op1.denote ρ) (res.denote ρ))
    {r : Repl 1} (h : run (simplifyAndOrWithICmpEq.Simplify.steps isAnd isEq op0 op1 res) = .value r) :
    Refines ((andOrSrc isAnd d op0 op1).eval ρ) (r.eval ρ) := by
  refine run_sound_ordered (P := fun r => Refines ((andOrSrc isAnd d op0 op1).eval ρ) (r.eval ρ))
    (fun pre s r post hs hpre => ?_) h
  simp only [simplifyAndOrWithICmpEq.Simplify.steps] at hs
  match pre, hs with
  | [], hs =>
    simp only [List.nil_append, List.cons.injEq] at hs
    obtain ⟨h1, -⟩ := hs
    split at h1 <;> simp only [Step.fire.injEq, reduceCtorEq] at h1
    obtain ⟨-, rfl⟩ := h1
    exact simplifyAndOrWithICmpEq.Simplify.L1965 ρ isAnd isEq d op0 op1 res hres (by assumption)
  | [_], hs =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hs
    obtain ⟨-, h1, -⟩ := hs
    split at h1 <;> simp only [Step.fire.injEq, reduceCtorEq] at h1
    obtain ⟨-, rfl⟩ := h1
    exact simplifyAndOrWithICmpEq.Simplify.L1967 ρ isAnd isEq d op0 op1 res hres (by assumption)
  | [_, _], hs =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hs
    obtain ⟨-, -, h1, -⟩ := hs
    split at h1 <;> simp only [reduceCtorEq] at h1
  | [_, _, s3], hs =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hs
    obtain ⟨-, -, h3, h1, -⟩ := hs
    split at h1 <;> simp only [Step.fire.injEq, reduceCtorEq] at h1
    obtain ⟨-, rfl⟩ := h1
    have h3' := hpre s3 (by simp)
    rw [h3'] at h3
    have hp : (isEq == isAnd) = false := by
      cases hq : (isEq == isAnd) <;> simp_all
    exact simplifyAndOrWithICmpEq.Simplify.L1975 ρ isAnd isEq d op0 op1 res hres hp (by assumption)
  | _ :: _ :: _ :: _ :: _, hs =>
    simp only [List.cons_append, List.cons.injEq] at hs
    obtain ⟨-, -, -, -, h⟩ := hs
    simp at h

/-- Theorem 1 for `simplifyAndOrWithICmpEq`: what it returns refines the `and` or `or`, in a run where the answers
of `Logic.Ext`, if given, are sound: it rests on `simplifyWithOpReplaced`'s soundness, `Logic.Ext.Sound.replaced`. -/
theorem simplifyAndOrWithICmpEq.sound (ρ : Env) (x : Option Ext) (hx : ∀ e, x = some e → e.Sound ρ)
    (isAnd d : Bool) (op0 op1 : Term w) (n : Nat) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) {r : Repl w}
    (h : run (simplifyAndOrWithICmpEq.steps x isAnd op0 op1 n) = .value r) :
    Refines ((andOrSrc isAnd d op0 op1).eval ρ) (r.eval ρ) := by
  refine run_sound (P := fun r => Refines ((andOrSrc isAnd d op0 op1).eval ρ) (r.eval ρ)) (fun s r hmem => ?_) h
  simp only [simplifyAndOrWithICmpEq.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h1 | h1 | h1
  · split at h1 <;> simp only [reduceCtorEq] at h1
  all_goals
    unfold simplifyAndOrWithICmpEq.replacedStep at h1
    split at h1
    · simp only [reduceCtorEq] at h1
    · next isEq p hp =>
      split at h1
      · simp only [reduceCtorEq] at h1
      · next e =>
        split at h1
        · next res hres =>
          obtain ⟨rfl, hspec⟩ := icmpEq?_spec hp c0
          have hs := hx e rfl
          refine simplifyAndOrWithICmpEq.Simplify.sound ρ isAnd isEq d op0 op1 res (fun c hd hc => ?_)
            (run_of_tail h1.symm)
          obtain ⟨v, ha, hb⟩ := hspec c hd hc
          simp only [Bool.false_eq_true, ite_false, ite_true] at hres
          first
            | exact hs.replaced n op1 res _ _ v hres c1 ha hb
            | exact hs.replaced n op1 res _ _ v hres c1 hb ha
        · simp only [reduceCtorEq] at h1
        · simp only [reduceCtorEq] at h1

end Peephole.IS
