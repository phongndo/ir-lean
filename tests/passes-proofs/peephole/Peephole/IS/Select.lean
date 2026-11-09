import Peephole.IS.Cast

/-! # Three of InstSimplify's helpers for `select`, and their rewrites for every input

`simplifySelectBitTest` (`llvm/lib/Analysis/InstructionSimplify.cpp:4675-4713`), `simplifyWithOpsReplaced`
(`4413-4649`) and `simplifySelectWithEquivalence` (`4801-4822`), at `llvmorg-23.1.3`. None is an entry: each answers its caller with a value, and is right under what its caller knows,
which each theorem here takes as a hypothesis, by name.

| ID | Rewrite |
| --- | --- |
| `IS.simplifySelectBitTest.L4683` | `(X & Y) == 0 ? X & ~Y : X` to `X`, and with `!=` to `X & ~Y` |
| `IS.simplifySelectBitTest.L4689` | `(X & Y) == 0 ? X : X & ~Y` to `X & ~Y`, and with `!=` to `X` |
| `IS.simplifySelectBitTest.L4699` | `(X & Y) == 0 ? X \| Y : X` to `X \| Y`, and with `!=` to `X`, for `Y` a power of two |
| `IS.simplifySelectBitTest.L4709` | `(X & Y) == 0 ? X : X \| Y` to `X`, and with `!=` to `X \| Y`, for `Y` a power of two |
| `IS.simplifyWithOpsReplaced.L4428` | `V` replaced with `RepOp`, where `V` is the `Op` of one of `Ops` |
| `IS.simplifySelectWithEquivalence.L4819` | A `select` whose arms are the same value with `Replacements` made, to its false arm |

- `simplifySelectBitTest(TrueVal, FalseVal, X, Y, TrueWhenUnset)` is called on a `select` whose condition, where it and
  `X` aren't poison, is `(X & Y) == 0` if `TrueWhenUnset` and `(X & Y) != 0` if not: `Select.BitTest`. Its callers,
  `simplifySelectWithBitTest` through `decomposeBitTest` and `simplifySelectWithICmpCond` from `icmp eq (and X, Y), 0`,
  owe that. Under it, each answer refines the `select`.
- `simplifyWithOpsReplaced(V, Ops, ...)` is modelled as far as its first loop and the checks after it; the replacement
  through `V`'s operands, and what it calls, are `.delegate`d. Its answer is `V` wherever each `Op` is its `RepOp`,
  `Select.OpsHold`, which its callers know where the condition they took `Ops` from is true.
- `simplifySelectWithEquivalence` compares what `simplifyWithOpsReplaced` gives for each arm, and is `.delegate`d where
  that isn't modelled. Its callers know `Replacements` hold where the `select`'s condition is true. -/

namespace Peephole.IS

open IRLean

variable {w : Nat}

namespace Select

/-! ### Matchers -/

/-- `m_And(m_Specific(X), m_APInt(C))` on `V`, binding `C`: the `and`'s operand 0 is `X`. -/
def andOf (x v : Term w) : Option (BitVec w) :=
  match binop? .and v with
  | some (_, a, c) => if specific x a then apint c else none
  | none => none

/-- `m_Or(m_Specific(X), m_APInt(C))` on `V`, binding `C`, with the `or`'s `disjoint` flag, which
`cast<PossiblyDisjointInst>(V)->isDisjoint()` reads. -/
def orOf (x v : Term w) : Option (BitVec w × Bool) :=
  match binop? .or v with
  | some (f, a, c) => if specific x a then (apint c).map (·, f.disjoint) else none
  | none => none

/-- What `simplifySelectBitTest`'s callers know of the `select`'s condition `c`: where it and `X` aren't poison, it's
true exactly when `(X & Y) == 0` is `TrueWhenUnset`. -/
def BitTest (c : Val 1) (x : Val w) (y : BitVec w) (trueWhenUnset : Bool) : Prop :=
  ∀ b v, c = some b → x = some v → (b == 1#1) = ((v &&& y == 0#w) == trueWhenUnset)

/-- The `select` a fold replaces. -/
def selSrc (cond : Term 1) (t e : Term w) : Repl w := .select (.old cond) (.old t) (.old e)

theorem selSrc_eval (ρ : Env) (cond : Term 1) (t e : Term w) :
    (selSrc cond t e).eval ρ = Outcome.ok (IRLean.select (cond.denote ρ) (t.denote ρ) (e.denote ρ)) := rfl

end Select

/-! ### `simplifySelectBitTest` -/

/-- `simplifySelectBitTest(TrueVal, FalseVal, X, Y, TrueWhenUnset)`, step by step. The block under `Y->isPowerOf2()`
has two statements that can end it each time, a `return nullptr` for a `disjoint` `or` and the rewrite, which are one
step each time here. -/
def simplifySelectBitTest.steps (trueVal falseVal x : Term w) (y : BitVec w) (trueWhenUnset : Bool) : List (Step w) :=
  [ -- (X & Y) == 0 ? X & ~Y : X  --> X
    -- (X & Y) != 0 ? X & ~Y : X  --> X & ~Y
    if specific x falseVal && (Select.andOf x trueVal).any (y == ~~~·) then
      .fire "IS.simplifySelectBitTest.L4683" (.old (if trueWhenUnset then falseVal else trueVal))
    else .next,
    -- (X & Y) == 0 ? X : X & ~Y  --> X & ~Y
    -- (X & Y) != 0 ? X : X & ~Y  --> X
    if specific x trueVal && (Select.andOf x falseVal).any (y == ~~~·) then
      .fire "IS.simplifySelectBitTest.L4689" (.old (if trueWhenUnset then falseVal else trueVal))
    else .next,
    -- (X & Y) == 0 ? X | Y : X  --> X | Y
    -- (X & Y) != 0 ? X | Y : X  --> X
    -- We can't return the or if it has the disjoint flag.
    if decide y.toNat.isPowerOfTwo && specific x falseVal then
      match Select.orOf x trueVal with
      | some (c, disjoint) =>
        if y = c then
          if trueWhenUnset && disjoint then .decline
          else .fire "IS.simplifySelectBitTest.L4699" (.old (if trueWhenUnset then trueVal else falseVal))
        else .next
      | none => .next
    else .next,
    -- (X & Y) == 0 ? X : X | Y  --> X
    -- (X & Y) != 0 ? X : X | Y  --> X | Y
    -- We can't return the or if it has the disjoint flag.
    if decide y.toNat.isPowerOfTwo && specific x trueVal then
      match Select.orOf x falseVal with
      | some (c, disjoint) =>
        if y = c then
          if !trueWhenUnset && disjoint then .decline
          else .fire "IS.simplifySelectBitTest.L4709" (.old (if trueWhenUnset then trueVal else falseVal))
        else .next
      | none => .next
    else .next ]

def simplifySelectBitTest (trueVal falseVal x : Term w) (y : BitVec w) (trueWhenUnset : Bool) : Result w :=
  run (simplifySelectBitTest.steps trueVal falseVal x y trueWhenUnset)

namespace Select

theorem andOf_denote {ρ : Env} {x v : Term w} {c : BitVec w} (h : andOf x v = some c) (hc : v.Consistent ρ) :
    v.denote ρ = Val.and (x.denote ρ) (some c) := by
  unfold andOf at h
  split at h
  · next f a c' hb =>
    split at h
    · next hx =>
      rw [← specific_denote hx, ← apint_denote h]
      exact (ok_inj (Shift.binop?_denote hb hc)).symm
    · cases h
  · cases h

theorem orOf_denote {ρ : Env} {x v : Term w} {c : BitVec w} {d : Bool} (h : orOf x v = some (c, d))
    (hc : v.Consistent ρ) : v.denote ρ = Val.or (x.denote ρ) (some c) d := by
  unfold orOf at h
  split at h
  · next f a c' hb =>
    split at h
    · next hx =>
      cases hac : apint c' with
      | none => simp [hac] at h
      | some c'' =>
        simp only [hac, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [← specific_denote hx, ← apint_denote hac]
        exact (ok_inj (Shift.binop?_denote hb hc)).symm
    · cases h
  · cases h

/-- Where `v` has no bit of `~c`, masking it with `c` keeps it. -/
theorem and_eq_of_and_not {v c : BitVec w} (h : v &&& ~~~c = 0#w) : v &&& c = v := by
  ext i hi
  have := congrArg (·[i]) h
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero] at this
  simp only [BitVec.getElem_and]
  cases hv : v[i] <;> simp_all

/-- Where `v` has the one bit of a power of two `y`, setting it changes nothing. -/
theorem or_eq_of_and_ne {v y : BitVec w} (hy : y.toNat.isPowerOfTwo) (h : (v &&& y == 0#w) = false) :
    v ||| y = v := by
  obtain ⟨k, hk⟩ := hy
  have hkw : k < w := by
    have := y.isLt
    rw [hk] at this
    exact (Nat.pow_lt_pow_iff_right (by decide)).1 this
  have hyk : y = BitVec.twoPow w k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_twoPow, hk, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hkw)]
  subst hyk
  rw [BitVec.and_twoPow] at h
  have hvk : v.getLsbD k = true := by
    false_or_by_contra
    rename_i hn
    simp [hn] at h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_twoPow]
  by_cases hik : k = i
  · subst hik; simp [hvk]
  · simp [hik]

/-! ### The four selects, as values -/

/-- `(X & Y) == 0 ? X & ~Y : X` refines `X`, and with `!=`, `X & ~Y`. -/
theorem select_and_left {c : Val 1} {a : Val w} {k : BitVec w} {tw : Bool} (h : BitTest c a (~~~k) tw) :
    Refines (IRLean.select c (Val.and a (some k)) a) (if tw then a else Val.and a (some k)) := by
  cases c with
  | none => exact Refine.val_none _
  | some b =>
  cases a with
  | none => simp only [IRLean.select, Val.and, Val.map₂]; split <;> exact Refine.val_none _
  | some v =>
  have hb := h b v rfl rfl
  simp only [IRLean.select, Val.and, Val.map₂]
  by_cases hz : v &&& ~~~k = 0#w
  · rw [and_eq_of_and_not hz]
    cases tw <;> (split <;> exact Refine.refl_val _)
  · have hz2 : (v &&& ~~~k == 0#w) = false := by simpa using hz
    rw [hz2] at hb
    cases tw <;> cases hb1 : (b == 1#1) <;> simp_all <;> exact Refine.refl_val _

/-- `(X & Y) == 0 ? X : X & ~Y` refines `X & ~Y`, and with `!=`, `X`. -/
theorem select_and_right {c : Val 1} {a : Val w} {k : BitVec w} {tw : Bool} (h : BitTest c a (~~~k) tw) :
    Refines (IRLean.select c a (Val.and a (some k))) (if tw then Val.and a (some k) else a) := by
  cases c with
  | none => exact Refine.val_none _
  | some b =>
  cases a with
  | none => simp only [IRLean.select, Val.and, Val.map₂]; split <;> exact Refine.val_none _
  | some v =>
  have hb := h b v rfl rfl
  simp only [IRLean.select, Val.and, Val.map₂]
  by_cases hz : v &&& ~~~k = 0#w
  · rw [and_eq_of_and_not hz]
    cases tw <;> (split <;> exact Refine.refl_val _)
  · have hz2 : (v &&& ~~~k == 0#w) = false := by simpa using hz
    rw [hz2] at hb
    cases tw <;> cases hb1 : (b == 1#1) <;> simp_all <;> exact Refine.refl_val _

theorem or_some_none (v : BitVec w) (y : BitVec w) (d : Bool) :
    Val.or (some v) (some y) d = if d && v &&& y != 0#w then none else some (v ||| y) := rfl

/-- `(X & Y) == 0 ? X | Y : X` refines `X | Y`, and with `!=`, `X`, for `Y` a power of two, and the `or` not
`disjoint` where it's the answer. -/
theorem select_or_left {c : Val 1} {a : Val w} {y : BitVec w} {tw d : Bool} (hy : y.toNat.isPowerOfTwo)
    (hd : (tw && d) = false) (h : BitTest c a y tw) :
    Refines (IRLean.select c (Val.or a (some y) d) a) (if tw then Val.or a (some y) d else a) := by
  cases c with
  | none => exact Refine.val_none _
  | some b =>
  cases a with
  | none => simp only [IRLean.select, Val.or]; split <;> exact Refine.val_none _
  | some v =>
  have hb := h b v rfl rfl
  simp only [IRLean.select]
  cases hz : (v &&& y == 0#w)
  · -- `X` has the bit: `X | Y` is `X`, or poison if `disjoint`.
    have hor := or_eq_of_and_ne hy hz
    have hz' : (v &&& y != 0#w) = true := by simp [bne, hz]
    simp only [or_some_none, hz', Bool.and_true, hor]
    cases tw <;> cases d <;> cases hb1 : (b == 1#1) <;> simp_all <;>
      first | exact Refine.refl_val _ | exact Refine.val_none _
  · -- `X` hasn't the bit: the condition is `TrueWhenUnset`.
    have hz' : (v &&& y != 0#w) = false := by simp [bne, hz]
    simp only [or_some_none, hz', Bool.and_false]
    cases tw <;> cases hb1 : (b == 1#1) <;> simp_all <;> exact Refine.refl_val _

/-- `(X & Y) == 0 ? X : X | Y` refines `X`, and with `!=`, `X | Y`, for `Y` a power of two, and the `or` not
`disjoint` where it's the answer. -/
theorem select_or_right {c : Val 1} {a : Val w} {y : BitVec w} {tw d : Bool} (hy : y.toNat.isPowerOfTwo)
    (hd : (!tw && d) = false) (h : BitTest c a y tw) :
    Refines (IRLean.select c a (Val.or a (some y) d)) (if tw then a else Val.or a (some y) d) := by
  cases c with
  | none => exact Refine.val_none _
  | some b =>
  cases a with
  | none => simp only [IRLean.select, Val.or]; split <;> exact Refine.val_none _
  | some v =>
  have hb := h b v rfl rfl
  simp only [IRLean.select]
  cases hz : (v &&& y == 0#w)
  · have hor := or_eq_of_and_ne hy hz
    have hz' : (v &&& y != 0#w) = true := by simp [bne, hz]
    simp only [or_some_none, hz', Bool.and_true, hor]
    cases tw <;> cases d <;> cases hb1 : (b == 1#1) <;> simp_all <;>
      first | exact Refine.refl_val _ | exact Refine.val_none _
  · have hz' : (v &&& y != 0#w) = false := by simp [bne, hz]
    simp only [or_some_none, hz', Bool.and_false]
    cases tw <;> cases hb1 : (b == 1#1) <;> simp_all <;> exact Refine.refl_val _

theorem eval_old_ite (ρ : Env) (tw : Bool) (t e : Term w) :
    (Repl.old (if tw then t else e)).eval ρ = Outcome.ok (if tw then t.denote ρ else e.denote ρ) := by
  cases tw <;> rfl

end Select

open Select in
/-- `IS.simplifySelectBitTest.L4683`: `(X & Y) == 0 ? X & ~Y : X` to `X`, and `(X & Y) != 0 ? X & ~Y : X` to
`X & ~Y`. It rests on `Select.BitTest`, the callers' contract. -/
theorem simplifySelectBitTest.L4683 (ρ : Env) (cond : Term 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw : Bool) (hbt : BitTest (cond.denote ρ) (x.denote ρ) y tw) (ct : trueVal.Consistent ρ)
    (h : (specific x falseVal && (andOf x trueVal).any (y == ~~~·)) = true) :
    Refines ((selSrc cond trueVal falseVal).eval ρ) ((Repl.old (if tw then falseVal else trueVal)).eval ρ) := by
  simp only [Bool.and_eq_true, Option.any_eq_true, beq_iff_eq] at h
  obtain ⟨hf, k, hk, rfl⟩ := h
  rw [selSrc_eval, eval_old_ite, andOf_denote hk ct, specific_denote hf]
  exact refines_ok (select_and_left hbt)

open Select in
/-- `IS.simplifySelectBitTest.L4689`: `(X & Y) == 0 ? X : X & ~Y` to `X & ~Y`, and `(X & Y) != 0 ? X : X & ~Y` to
`X`. It rests on `Select.BitTest`. -/
theorem simplifySelectBitTest.L4689 (ρ : Env) (cond : Term 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw : Bool) (hbt : BitTest (cond.denote ρ) (x.denote ρ) y tw) (cf : falseVal.Consistent ρ)
    (h : (specific x trueVal && (andOf x falseVal).any (y == ~~~·)) = true) :
    Refines ((selSrc cond trueVal falseVal).eval ρ) ((Repl.old (if tw then falseVal else trueVal)).eval ρ) := by
  simp only [Bool.and_eq_true, Option.any_eq_true, beq_iff_eq] at h
  obtain ⟨ht, k, hk, rfl⟩ := h
  rw [selSrc_eval, eval_old_ite, andOf_denote hk cf, specific_denote ht]
  exact refines_ok (select_and_right hbt)

open Select in
/-- `IS.simplifySelectBitTest.L4699`: `(X & Y) == 0 ? X | Y : X` to `X | Y`, if the `or` isn't `disjoint`, and
`(X & Y) != 0 ? X | Y : X` to `X`, for `Y` a power of two. It rests on `Select.BitTest`. -/
theorem simplifySelectBitTest.L4699 (ρ : Env) (cond : Term 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw d : Bool) (hbt : BitTest (cond.denote ρ) (x.denote ρ) y tw) (ct : trueVal.Consistent ρ)
    (hp : y.toNat.isPowerOfTwo) (hf : specific x falseVal = true) (ho : orOf x trueVal = some (y, d))
    (hd : (tw && d) = false) :
    Refines ((selSrc cond trueVal falseVal).eval ρ) ((Repl.old (if tw then trueVal else falseVal)).eval ρ) := by
  rw [selSrc_eval, eval_old_ite, orOf_denote ho ct, specific_denote hf]
  exact refines_ok (select_or_left hp hd hbt)

open Select in
/-- `IS.simplifySelectBitTest.L4709`: `(X & Y) == 0 ? X : X | Y` to `X`, and `(X & Y) != 0 ? X : X | Y` to `X | Y`, if
the `or` isn't `disjoint`, for `Y` a power of two. It rests on `Select.BitTest`. -/
theorem simplifySelectBitTest.L4709 (ρ : Env) (cond : Term 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw d : Bool) (hbt : BitTest (cond.denote ρ) (x.denote ρ) y tw) (cf : falseVal.Consistent ρ)
    (hp : y.toNat.isPowerOfTwo) (ht : specific x trueVal = true) (ho : orOf x falseVal = some (y, d))
    (hd : (!tw && d) = false) :
    Refines ((selSrc cond trueVal falseVal).eval ρ) ((Repl.old (if tw then trueVal else falseVal)).eval ρ) := by
  rw [selSrc_eval, eval_old_ite, orOf_denote ho cf, specific_denote ht]
  exact refines_ok (select_or_right hp hd hbt)

open Select in
theorem simplifySelectBitTest.steps_sound (ρ : Env) (cond : Term 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw : Bool) (hbt : BitTest (cond.denote ρ) (x.denote ρ) y tw) (ct : trueVal.Consistent ρ)
    (cf : falseVal.Consistent ρ) :
    ∀ s r, Step.fire s r ∈ simplifySelectBitTest.steps trueVal falseVal x y tw →
      Refines ((selSrc cond trueVal falseVal).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifySelectBitTest.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifySelectBitTest.L4683 ρ cond trueVal falseVal x y tw hbt ct (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifySelectBitTest.L4689 ρ cond trueVal falseVal x y tw hbt cf (by assumption)
  · split at h
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      split at h
      · next c d ho =>
        split at h
        · next hyc =>
          subst hyc
          split at h
          · simp only [reduceCtorEq] at h
          · next hd =>
            simp only [Step.fire.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact simplifySelectBitTest.L4699 ρ cond trueVal falseVal x y tw d hbt ct hc.1 hc.2 ho
              (by simpa using hd)
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  · split at h
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      split at h
      · next c d ho =>
        split at h
        · next hyc =>
          subst hyc
          split at h
          · simp only [reduceCtorEq] at h
          · next hd =>
            simp only [Step.fire.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact simplifySelectBitTest.L4709 ρ cond trueVal falseVal x y tw d hbt cf hc.1 hc.2 ho
              (by simpa using hd)
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h

/-- Theorem 1 for `simplifySelectBitTest`: every value it returns refines a `select` of `TrueVal` and `FalseVal` on a
condition its callers know is `(X & Y) == 0`, or `!= 0`, `Select.BitTest`, at every width, in every run the arms are
consistent with, poison included. -/
theorem simplifySelectBitTest.sound (ρ : Env) (cond : Term 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw : Bool) (hbt : Select.BitTest (cond.denote ρ) (x.denote ρ) y tw) (ct : trueVal.Consistent ρ)
    (cf : falseVal.Consistent ρ) {r : Repl w} (h : simplifySelectBitTest trueVal falseVal x y tw = .value r) :
    Refines ((Select.selSrc cond trueVal falseVal).eval ρ) (r.eval ρ) :=
  run_sound (simplifySelectBitTest.steps_sound ρ cond trueVal falseVal x y tw hbt ct cf) h

/-! ### `simplifyWithOpsReplaced`, as far as its first loop, and `simplifySelectWithEquivalence` -/

namespace Select

/-- One of `Ops`: a value, and the value it's replaced with, of one type. -/
abbrev OpPair := (u : Nat) × Term u × Term u

/-- Every value in `Ops` is the value it's replaced with, in the run `ρ`: what a caller knows where the condition it
took `Ops` from, such as `icmp eq X, Y` for `{X, Y}`, is true. -/
def OpsHold (ρ : Env) (ops : List OpPair) : Prop := ∀ p ∈ ops, p.2.1.denote ρ = p.2.2.denote ρ

/-- A `var`: an argument, or an instruction a `Term` doesn't see into. -/
def isVar {v : Nat} : Term v → Bool
  | .var _ => true
  | _ => false

/-- `isa<FreezeInst>(V)`. -/
def isFreeze {v : Nat} : Term v → Bool
  | .freeze .. => true
  | _ => false

end Select

/-- `simplifyWithOpsReplaced(V, Ops, Q, AllowRefinement, DropFlags, MaxRecurse)`, as far as the C++ goes before it
replaces `V`'s operands: its first loop, over `Ops` in order, and the checks after it. What follows, the replacement
through the operands, which calls `simplifyWithOpsReplaced` on each and `simplifyInstructionWithOperands` or the constant
folder on the result, is `.delegate`d, as is an operand a `Term` shows as `var`: an argument, which isn't an
`Instruction`, or an instruction a `Term` doesn't see into, a `phi` or an `llvm.is.constant` call among them. Nothing
before the replacement reads `Q`, `AllowRefinement` or `DropFlags`. -/
def simplifyWithOpsReplaced.steps {v : Nat} (V : Term v) (ops : List Select.OpPair) (maxRecurse : Nat) :
    List (Step v) :=
  ops.flatMap (fun p =>
    [ -- We cannot replace a constant, and shouldn't even try.
      if p.2.1.isConstant then .decline else .next,
      -- Trivial replacement.
      if h : p.1 = v then
        if specific (h ▸ p.2.1) V then .fire "IS.simplifyWithOpsReplaced.L4428" (.old (h ▸ p.2.2)) else .next
      else .next ]) ++
  [ -- if (!MaxRecurse--) return nullptr;
    if maxRecurse == 0 then .decline else .next,
    -- auto *I = dyn_cast<Instruction>(V); if (!I) return nullptr;
    if V.isConstant then .decline else .next,
    -- An argument, or an instruction a `Term` doesn't see into.
    if Select.isVar V then .delegate "simplifyWithOpsReplaced" else .next,
    -- Don't simplify freeze.
    if Select.isFreeze V then .decline else .next,
    -- Replace Op with RepOp in instruction operands, and what follows.
    .delegate "simplifyWithOpsReplaced" ]

def simplifyWithOpsReplaced {v : Nat} (V : Term v) (ops : List Select.OpPair) (maxRecurse : Nat) : Result v :=
  run (simplifyWithOpsReplaced.steps V ops maxRecurse)

open Select in
/-- `IS.simplifyWithOpsReplaced.L4428`: `V` is one of `Ops`, so it's replaced with its `RepOp`, which is `V` wherever
`Ops` hold, `Select.OpsHold`, as its callers know they do. -/
theorem simplifyWithOpsReplaced.L4428 (ρ : Env) {v : Nat} (V : Term v) (ops : List OpPair) (p : OpPair)
    (hp : p ∈ ops) (hold : OpsHold ρ ops) (h : p.1 = v) (hs : specific (h ▸ p.2.1) V = true) :
    (h ▸ p.2.2).denote ρ = V.denote ρ := by
  obtain ⟨u, op, rep⟩ := p
  have := hold _ hp
  simp only at h this hs ⊢
  subst h
  rw [specific_denote hs, this]

open Select in
/-- Theorem 1 for `simplifyWithOpsReplaced`, as far as it's modelled: what it returns is a value already in the IR, and
is `V` wherever `Ops` hold, at every width. Whether it refines `V` or `V` refines it, as `AllowRefinement` asks, it's
both. -/
theorem simplifyWithOpsReplaced.sound (ρ : Env) {v : Nat} (V : Term v) (ops : List OpPair) (n : Nat)
    (hold : OpsHold ρ ops) {r : Repl v} (h : simplifyWithOpsReplaced V ops n = .value r) :
    ∃ t : Term v, r = .old t ∧ t.denote ρ = V.denote ρ := by
  refine run_sound (P := fun r => ∃ t : Term v, r = .old t ∧ t.denote ρ = V.denote ρ) ?_ h
  intro s r hmem
  simp only [simplifyWithOpsReplaced.steps, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with ⟨p, hp, h | h⟩ | h | h | h | h | h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h
    · next hw =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hs =>
      obtain ⟨-, rfl⟩ := h
      exact ⟨_, rfl, simplifyWithOpsReplaced.L4428 ρ V ops p hp hold hw hs⟩
    · simp only [reduceCtorEq] at h
  all_goals first
    | (split at h <;> simp only [reduceCtorEq] at h)
    | simp only [reduceCtorEq] at h

namespace Select

/-- What `simplifyWithOpsReplaced` gives `simplifySelectWithEquivalence`, `V` itself where it answers `nullptr`, or
`none` where what it answers isn't modelled. -/
def replaced {v : Nat} (V : Term v) (ops : List OpPair) (n : Nat) : Option (Term v) :=
  match simplifyWithOpsReplaced V ops n with
  | .value (.old t) => some t
  | .value _ => none
  | .null => some V
  | .delegated _ => none

theorem replaced_denote {ρ : Env} {v : Nat} {V t : Term v} {ops : List OpPair} {n : Nat}
    (h : replaced V ops n = some t) (hold : OpsHold ρ ops) : t.denote ρ = V.denote ρ := by
  unfold replaced at h
  split at h
  · next t' hr =>
    cases h
    obtain ⟨t'', ht, hd⟩ := simplifyWithOpsReplaced.sound ρ V ops n hold hr
    cases ht
    exact hd
  · cases h
  · cases h; rfl
  · cases h

end Select

/-- `simplifySelectWithEquivalence(Replacements, TrueVal, FalseVal, Q, MaxRecurse)`: if `FalseVal` and `TrueVal`, with
`Replacements` made, are the same value, the `select` is `FalseVal`. Where `simplifyWithOpsReplaced`'s answer isn't
modelled, neither is this. -/
def simplifySelectWithEquivalence.steps (ops : List Select.OpPair) (trueVal falseVal : Term w) (maxRecurse : Nat) :
    List (Step w) :=
  match Select.replaced falseVal ops maxRecurse, Select.replaced trueVal ops maxRecurse with
  | some sf, some st =>
    [ -- if (SimplifiedFalseVal == SimplifiedTrueVal) return FalseVal;
      if specific sf st then .fire "IS.simplifySelectWithEquivalence.L4819" (.old falseVal) else .next ]
  | _, _ => [ .delegate "simplifyWithOpsReplaced" ]

def simplifySelectWithEquivalence (ops : List Select.OpPair) (trueVal falseVal : Term w) (maxRecurse : Nat) :
    Result w :=
  run (simplifySelectWithEquivalence.steps ops trueVal falseVal maxRecurse)

open Select in
/-- `IS.simplifySelectWithEquivalence.L4819`: a `select` whose arms are the same value once `Replacements` are made is
its false arm. It rests on the callers' contract: where the condition is true, `Replacements` hold, as they do for
`icmp eq X, Y` and `{X, Y}`. -/
theorem simplifySelectWithEquivalence.L4819 (ρ : Env) (cond : Term 1) (ops : List OpPair) (trueVal falseVal : Term w)
    (n : Nat) (hcond : cond.denote ρ = some 1#1 → OpsHold ρ ops) (sf st : Term w)
    (hf : replaced falseVal ops n = some sf) (ht : replaced trueVal ops n = some st) (h : specific sf st = true) :
    Refines ((selSrc cond trueVal falseVal).eval ρ) ((Repl.old falseVal).eval ρ) := by
  rw [selSrc_eval, Repl.eval_old]
  refine refines_ok ?_
  cases hc : cond.denote ρ with
  | none => exact Refine.val_none _
  | some b =>
    simp only [IRLean.select]
    split
    · next hb =>
      have hb : b = 1#1 := by simpa using hb
      subst hb
      have hold := hcond hc
      rw [← replaced_denote ht hold, specific_denote h, replaced_denote hf hold]
      exact Refine.refl_val _
    · exact Refine.refl_val _

open Select in
/-- Theorem 1 for `simplifySelectWithEquivalence`: what it returns refines a `select` on a condition its callers know
makes `Replacements` hold where it's true, at every width, poison included. -/
theorem simplifySelectWithEquivalence.sound (ρ : Env) (cond : Term 1) (ops : List OpPair) (trueVal falseVal : Term w)
    (n : Nat) (hcond : cond.denote ρ = some 1#1 → OpsHold ρ ops) {r : Repl w}
    (h : simplifySelectWithEquivalence ops trueVal falseVal n = .value r) :
    Refines ((selSrc cond trueVal falseVal).eval ρ) (r.eval ρ) := by
  refine run_sound (P := fun r => Refines ((selSrc cond trueVal falseVal).eval ρ) (r.eval ρ)) ?_ h
  intro s r hmem
  unfold simplifySelectWithEquivalence.steps at hmem
  split at hmem
  · next sf st hf ht =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    split at hmem <;> simp only [Step.fire.injEq, reduceCtorEq] at hmem
    next hs =>
    obtain ⟨-, rfl⟩ := hmem
    exact simplifySelectWithEquivalence.L4819 ρ cond ops trueVal falseVal n hcond sf st hf ht hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hmem

end Peephole.IS
