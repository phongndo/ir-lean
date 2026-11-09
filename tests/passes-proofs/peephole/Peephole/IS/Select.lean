import Peephole.IS.Cast

/-! # Three of InstSimplify's helpers for `select`, and their rewrites for every input

`simplifySelectBitTest` (`llvm/lib/Analysis/InstructionSimplify.cpp:4675-4713`), `simplifyWithOpsReplaced`
(`4413-4649`) and `simplifySelectWithEquivalence` (`4801-4822`), at `llvmorg-23.1.3`. None is called on an
instruction: each answers its caller with a value, and is right under what its caller knows, which each theorem here
takes as a hypothesis, by name. Each theorem is about the value of the `select`'s condition, so a caller that swaps the
arms for `ne` can use it too. `Select.selectOnInst`, at the end, follows `simplifySelectInst` and
`simplifySelectWithICmpCond` to them, for the comparison with `opt`, and `Select.selectOnInst_sound` discharges their
hypotheses there.

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
  that isn't modelled. Its callers know `Replacements` hold where the `select`'s condition is true.

Each theorem is for scalar integer values, the ones a `Term` has. `simplifySelectBitTest`'s answers are all `X`, or an
`and` or `or` of `X` with an integer constant, so integers alone reach it. A `select`'s arms, and the values
`simplifyWithOpsReplaced` replaces, can be of any type, so the C++ reaches `L4428` and `L4819` with floating-point and
pointer values too, and the family's registry lists those two as integer instances, under `unproved`. -/

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
theorem simplifySelectBitTest.L4683 (ρ : Env) (c : Val 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw : Bool) (hbt : BitTest c (x.denote ρ) y tw) (ct : trueVal.Consistent ρ)
    (h : (specific x falseVal && (andOf x trueVal).any (y == ~~~·)) = true) :
    Refines (Outcome.ok (IRLean.select c (trueVal.denote ρ) (falseVal.denote ρ)))
      ((Repl.old (if tw then falseVal else trueVal)).eval ρ) := by
  simp only [Bool.and_eq_true, Option.any_eq_true, beq_iff_eq] at h
  obtain ⟨hf, k, hk, rfl⟩ := h
  rw [eval_old_ite, andOf_denote hk ct, specific_denote hf]
  exact refines_ok (select_and_left hbt)

open Select in
/-- `IS.simplifySelectBitTest.L4689`: `(X & Y) == 0 ? X : X & ~Y` to `X & ~Y`, and `(X & Y) != 0 ? X : X & ~Y` to
`X`. It rests on `Select.BitTest`. -/
theorem simplifySelectBitTest.L4689 (ρ : Env) (c : Val 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw : Bool) (hbt : BitTest c (x.denote ρ) y tw) (cf : falseVal.Consistent ρ)
    (h : (specific x trueVal && (andOf x falseVal).any (y == ~~~·)) = true) :
    Refines (Outcome.ok (IRLean.select c (trueVal.denote ρ) (falseVal.denote ρ)))
      ((Repl.old (if tw then falseVal else trueVal)).eval ρ) := by
  simp only [Bool.and_eq_true, Option.any_eq_true, beq_iff_eq] at h
  obtain ⟨ht, k, hk, rfl⟩ := h
  rw [eval_old_ite, andOf_denote hk cf, specific_denote ht]
  exact refines_ok (select_and_right hbt)

open Select in
/-- `IS.simplifySelectBitTest.L4699`: `(X & Y) == 0 ? X | Y : X` to `X | Y`, if the `or` isn't `disjoint`, and
`(X & Y) != 0 ? X | Y : X` to `X`, for `Y` a power of two. It rests on `Select.BitTest`. -/
theorem simplifySelectBitTest.L4699 (ρ : Env) (c : Val 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw d : Bool) (hbt : BitTest c (x.denote ρ) y tw) (ct : trueVal.Consistent ρ)
    (hp : y.toNat.isPowerOfTwo) (hf : specific x falseVal = true) (ho : orOf x trueVal = some (y, d))
    (hd : (tw && d) = false) :
    Refines (Outcome.ok (IRLean.select c (trueVal.denote ρ) (falseVal.denote ρ)))
      ((Repl.old (if tw then trueVal else falseVal)).eval ρ) := by
  rw [eval_old_ite, orOf_denote ho ct, specific_denote hf]
  exact refines_ok (select_or_left hp hd hbt)

open Select in
/-- `IS.simplifySelectBitTest.L4709`: `(X & Y) == 0 ? X : X | Y` to `X`, and `(X & Y) != 0 ? X : X | Y` to `X | Y`, if
the `or` isn't `disjoint`, for `Y` a power of two. It rests on `Select.BitTest`. -/
theorem simplifySelectBitTest.L4709 (ρ : Env) (c : Val 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw d : Bool) (hbt : BitTest c (x.denote ρ) y tw) (cf : falseVal.Consistent ρ)
    (hp : y.toNat.isPowerOfTwo) (ht : specific x trueVal = true) (ho : orOf x falseVal = some (y, d))
    (hd : (!tw && d) = false) :
    Refines (Outcome.ok (IRLean.select c (trueVal.denote ρ) (falseVal.denote ρ)))
      ((Repl.old (if tw then trueVal else falseVal)).eval ρ) := by
  rw [eval_old_ite, orOf_denote ho cf, specific_denote ht]
  exact refines_ok (select_or_right hp hd hbt)

open Select in
theorem simplifySelectBitTest.steps_sound (ρ : Env) (c : Val 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw : Bool) (hbt : BitTest c (x.denote ρ) y tw) (ct : trueVal.Consistent ρ)
    (cf : falseVal.Consistent ρ) :
    ∀ s r, Step.fire s r ∈ simplifySelectBitTest.steps trueVal falseVal x y tw →
      Refines (Outcome.ok (IRLean.select c (trueVal.denote ρ) (falseVal.denote ρ))) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifySelectBitTest.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifySelectBitTest.L4683 ρ c trueVal falseVal x y tw hbt ct (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifySelectBitTest.L4689 ρ c trueVal falseVal x y tw hbt cf (by assumption)
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
            exact simplifySelectBitTest.L4699 ρ c trueVal falseVal x y tw d hbt ct hc.1 hc.2 ho
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
            exact simplifySelectBitTest.L4709 ρ c trueVal falseVal x y tw d hbt cf hc.1 hc.2 ho
              (by simpa using hd)
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h

/-- Theorem 1 for `simplifySelectBitTest`: every value it returns refines a `select` of `TrueVal` and `FalseVal` on a
condition its callers know is `(X & Y) == 0`, or `!= 0`, `Select.BitTest`, at every width, in every run the arms are
consistent with, poison included. -/
theorem simplifySelectBitTest.sound (ρ : Env) (c : Val 1) (trueVal falseVal x : Term w) (y : BitVec w)
    (tw : Bool) (hbt : Select.BitTest c (x.denote ρ) y tw) (ct : trueVal.Consistent ρ)
    (cf : falseVal.Consistent ρ) {r : Repl w} (h : simplifySelectBitTest trueVal falseVal x y tw = .value r) :
    Refines (Outcome.ok (IRLean.select c (trueVal.denote ρ) (falseVal.denote ρ))) (r.eval ρ) :=
  run_sound (simplifySelectBitTest.steps_sound ρ c trueVal falseVal x y tw hbt ct cf) h

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
through the operands, which calls `simplifyWithOpsReplaced` on each and `simplifyInstructionWithOperands` or the
constant folder on the result, is `.delegate`d, as is an operand a `Term` shows as `var`: an argument, which isn't an
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

/-- Which delegation of `simplifyWithOpsReplaced` leaves `simplifySelectWithEquivalence` unmodelled: the false arm's,
which the C++ asks first, else the true arm's. -/
def delegatedTo {v : Nat} (a b : Result v) : String :=
  match a, b with
  | .delegated c, _ => c
  | _, .delegated c => c
  | _, _ => "simplifyWithOpsReplaced"

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
  | _, _ =>
    [ .delegate (Select.delegatedTo (simplifyWithOpsReplaced falseVal ops maxRecurse)
        (simplifyWithOpsReplaced trueVal ops maxRecurse)) ]

def simplifySelectWithEquivalence (ops : List Select.OpPair) (trueVal falseVal : Term w) (maxRecurse : Nat) :
    Result w :=
  run (simplifySelectWithEquivalence.steps ops trueVal falseVal maxRecurse)

open Select in
/-- `IS.simplifySelectWithEquivalence.L4819`: a `select` whose arms are the same value once `Replacements` are made is
its false arm. It rests on the callers' contract: where the condition is true, `Replacements` hold, as they do for
`icmp eq X, Y` and `{X, Y}`. -/
theorem simplifySelectWithEquivalence.L4819 (ρ : Env) (c : Val 1) (ops : List OpPair) (trueVal falseVal : Term w)
    (n : Nat) (hcond : c = some 1#1 → OpsHold ρ ops) (sf st : Term w)
    (hf : replaced falseVal ops n = some sf) (ht : replaced trueVal ops n = some st) (h : specific sf st = true) :
    Refines (Outcome.ok (IRLean.select c (trueVal.denote ρ) (falseVal.denote ρ))) ((Repl.old falseVal).eval ρ) := by
  rw [Repl.eval_old]
  refine refines_ok ?_
  cases hc : c with
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
theorem simplifySelectWithEquivalence.sound (ρ : Env) (c : Val 1) (ops : List OpPair) (trueVal falseVal : Term w)
    (n : Nat) (hcond : c = some 1#1 → OpsHold ρ ops) {r : Repl w}
    (h : simplifySelectWithEquivalence ops trueVal falseVal n = .value r) :
    Refines (Outcome.ok (IRLean.select c (trueVal.denote ρ) (falseVal.denote ρ))) (r.eval ρ) := by
  refine run_sound
    (P := fun r => Refines (Outcome.ok (IRLean.select c (trueVal.denote ρ) (falseVal.denote ρ))) (r.eval ρ)) ?_ h
  intro s r hmem
  unfold simplifySelectWithEquivalence.steps at hmem
  split at hmem
  · next sf st hf ht =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    split at hmem <;> simp only [Step.fire.injEq, reduceCtorEq] at hmem
    next hs =>
    obtain ⟨-, rfl⟩ := hmem
    exact simplifySelectWithEquivalence.L4819 ρ c ops trueVal falseVal n hcond sf st hf ht hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hmem

/-! ### Where InstSimplify reaches these helpers: `simplifySelectInst`, for the comparison with `opt`

`simplifyInstructionWithOperands` calls `simplifySelectInst` on a `select`, which calls `simplifySelectWithICmpCond`,
which calls `simplifySelectBitTest` and `simplifySelectWithEquivalence`. `Select.selectOnInst` follows them there:

- Every statement of `simplifySelectInst` before `simplifySelectWithICmpCond` that could end it, where it could, is a
  `.delegate`, read from the C++'s guards: a constant condition, an `i1` `select`, the same value in both arms, and a
  poison or `undef` arm.
- In `simplifySelectWithICmpCond`, `simplifyCmpSelOfMaxMin` answers only where an arm is a min or max intrinsic, and is
  delegated there. Its min/max limit test answers for no equality, and is delegated for the other predicates. Its
  funnel shift, rotate and `abs` steps, between the bit test and the equivalences, are delegated wherever an arm is a
  funnel shift or an `abs`. The rest it runs as the C++ does, with `simplifySelectBitTest` and
  `simplifySelectWithEquivalence` as modelled here.
- After `simplifySelectWithICmpCond`, the rest of `simplifySelectInst` is a `.delegate`. -/

namespace Select

/-- `if (Value *V = g(...)) return V;`, where `g` is a fold modelled here: `g`'s answer, or fall through. -/
def fwd (callee : String) : Result w → Step w
  | .value r => .fire callee r
  | .null => .next
  | .delegated c => .delegate c

theorem fwd_fire {c s : String} {res : Result w} {r : Repl w} (h : fwd c res = .fire s r) : res = .value r := by
  cases res <;> simp_all [fwd]

/-- `isa<MinMaxIntrinsic>(V)`: `umin`, `umax`, `smin` or `smax`. -/
def isMinMax : Term w → Bool
  | .bi _ .umin .. | .bi _ .umax .. | .bi _ .smin .. | .bi _ .smax .. => true
  | _ => false

/-- A funnel shift or an `abs`: one arm of `simplifySelectWithICmpCond`'s funnel shift, rotate and `abs` patterns is
one. -/
def fshOrAbs : Term w → Bool
  | .fsh .. => true
  | .un _ (.abs _) _ => true
  | _ => false

/-- Whether a statement of `simplifySelectInst` before `simplifySelectWithICmpCond` could end it: a constant condition,
the folds where the condition has the arms' type, `i1`, `select ?, X, X`, and a poison or `undef` arm. -/
def selectEarlier (c : Term 1) (t e : Term w) : Bool :=
  c.isConstant || w == 1 || specific t e || isUndefValue t || isUndefValue e

/-- `m_And(m_Value(X), m_APInt(Y))`, binding `X` and `Y`. -/
def andConst? {u : Nat} (t : Term u) : Option (Term u × BitVec u) :=
  match binop? .and t with
  | some (_, x, yc) => (apint yc).map (x, ·)
  | none => none

end Select

/-- The steps of `simplifySelectWithICmpCond` under `Pred == ICMP_EQ`, once `ne` is made `eq` and the arms swapped for
it, on the compare's operands `CmpLHS` and `CmpRHS` and the arms `TrueVal` and `FalseVal`. -/
def simplifySelectWithICmpCond.eqSteps {u : Nat} (cl cr : Term u) (tv fv : Term w) (n : Nat) : List (Step w) :=
  [ -- if (Pred == ICmpInst::ICMP_EQ && match(CmpRHS, m_Zero())) {
    --   if (match(CmpLHS, m_And(m_Value(X), m_APInt(Y))))
    --     if (Value *V = simplifySelectBitTest(TrueVal, FalseVal, X, Y, /*TrueWhenUnset=*/true)) return V;
    -- An `X` of another type than the arms is no arm, which each of its rewrites needs.
    if zero cr then
      match Select.andConst? cl with
      | some (x, y) =>
        if h : u = w then Select.fwd "IS.simplifySelectBitTest" (simplifySelectBitTest tv fv (h ▸ x) (h ▸ y) true)
        else .next
      | none => .next
    else .next,
    -- Test for a bogus zero-shift-guard-op around funnel-shift or rotate, and X == 0 ? abs(X) : -abs(X): not
    -- modelled here, and delegated wherever an arm is a funnel shift or an `abs`.
    if zero cr && (Select.fshOrAbs tv || Select.fshOrAbs fv) then
      .delegate "simplifySelectWithICmpCond: a funnel shift or abs step"
    else .next,
    -- If we have a scalar equality comparison, then we know the value in one of the arms of the select.
    Select.fwd "IS.simplifySelectWithEquivalence" (simplifySelectWithEquivalence [⟨u, cl, cr⟩] tv fv n),
    Select.fwd "IS.simplifySelectWithEquivalence" (simplifySelectWithEquivalence [⟨u, cr, cl⟩] tv fv n),
    -- select((X | Y) == 0 ?  X : 0) --> 0 (commuted 2 ways)
    if zero cr then
      match binop? .or cl with
      | some (_, x, y) =>
        Select.fwd "IS.simplifySelectWithEquivalence" (simplifySelectWithEquivalence [⟨u, x, cr⟩, ⟨u, y, cr⟩] tv fv n)
      | none => .next
    else .next,
    -- select((X & Y) == -1 ?  X : -1) --> -1 (commuted 2 ways)
    if allOnes cr then
      match binop? .and cl with
      | some (_, x, y) =>
        Select.fwd "IS.simplifySelectWithEquivalence" (simplifySelectWithEquivalence [⟨u, x, cr⟩, ⟨u, y, cr⟩] tv fv n)
      | none => .next
    else .next ]

/-- `simplifySelectWithICmpCond(CondVal, TrueVal, FalseVal, Q, MaxRecurse)`, as far as it reaches the helpers here. A
condition that isn't an `icmp` answers `nullptr` at once. -/
def simplifySelectWithICmpCond.steps (c : Term 1) (t e : Term w) (n : Nat) : List (Step w) :=
  match c with
  | .icmp _ p _ cl cr =>
    -- if (Value *V = simplifyCmpSelOfMaxMin(...)) return V;
    (if Select.isMinMax t || Select.isMinMax e then .delegate "simplifyCmpSelOfMaxMin" else .next) ::
    -- Canonicalize ne to eq predicate. The min/max limit test after it answers for no `eq`.
    if p = .eq then simplifySelectWithICmpCond.eqSteps cl cr t e n
    else if p = .ne then simplifySelectWithICmpCond.eqSteps cl cr e t n
    else [ .delegate "matchDecomposedSelectPattern" ]
  | _ => []

/-- `simplifySelectInst(Cond, TrueVal, FalseVal, FMF, Q, MaxRecurse)`, as far as it reaches the helpers here. -/
def Select.selectEntry.steps (c : Term 1) (t e : Term w) (n : Nat) : List (Step w) :=
  (if Select.selectEarlier c t e then .delegate "simplifySelectInst: a step before simplifySelectWithICmpCond"
    else .next) ::
  simplifySelectWithICmpCond.steps c t e n ++
  [ .delegate "simplifySelectInst: a step after simplifySelectWithICmpCond" ]

/-- What InstSimplify does with a `select`, as far as it reaches the helpers here: `simplifyInstructionWithOperands`
calls `simplifySelectInst` with `MaxRecurse` at `RecursionLimit`, 3. -/
def Select.selectOnInst (_o : Oracle) : {w : Nat} → Term w → Result w
  | _, .select _ c t e => run (Select.selectEntry.steps c t e 3)
  | _, _ => .null

namespace Select

theorem icmpEq_eq_one {u : Nat} {a b : Val u} {s : Bool} (h : Val.icmpEq a b s = some 1#1) : a = b ∧ a ≠ none := by
  cases a <;> cases b <;> simp only [Val.icmpEq, Val.icmp, reduceCtorEq] at h
  · next x y =>
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      have : (x == y) = true := by
        cases hxy : (x == y)
        · rw [hxy] at h; exact absurd h (by decide)
        · rfl
      simp only [beq_iff_eq] at this
      subst this
      exact ⟨rfl, nofun⟩
  all_goals simp_all

theorem select_ne {u : Nat} (a b : Val u) (s : Bool) (t e : Val w) :
    IRLean.select (Val.icmpNe a b s) t e = IRLean.select (Val.icmpEq a b s) e t := by
  cases a <;> cases b <;> simp only [Val.icmpNe, Val.icmpEq, Val.icmp]
  any_goals rfl
  next x y =>
  split
  · rfl
  · by_cases hxy : x = y <;> simp [IRLean.select, hxy]

theorem bitTest_of_icmpEq {a : Val w} {y : BitVec w} {s : Bool} :
    BitTest (Val.icmpEq (Val.and a (some y)) (some 0#w) s) a y true := by
  intro b v hb hv
  subst hv
  simp only [Val.icmpEq, Val.icmp, Val.and, Val.map₂] at hb
  split at hb
  · cases hb
  · simp only [Option.some.injEq] at hb
    subst hb
    cases (v &&& y == 0#w) <;> decide

theorem or_eq_zero {a b : Val w} {d : Bool} (h : Val.or a b d = some 0#w) : a = some 0#w ∧ b = some 0#w := by
  cases a <;> cases b <;> simp only [Val.or, reduceCtorEq] at h
  next x y =>
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    have hx : x = 0#w := by
      ext i hi
      have := congrArg (·[i]) h
      simp only [BitVec.getElem_or, BitVec.getElem_zero, Bool.or_eq_false_iff] at this
      simp [this.1]
    have hy : y = 0#w := by
      ext i hi
      have := congrArg (·[i]) h
      simp only [BitVec.getElem_or, BitVec.getElem_zero, Bool.or_eq_false_iff] at this
      simp [this.2]
    exact ⟨by rw [hx], by rw [hy]⟩

theorem and_eq_allOnes {a b : Val w} (h : Val.and a b = some (BitVec.allOnes w)) :
    a = some (BitVec.allOnes w) ∧ b = some (BitVec.allOnes w) := by
  cases a <;> cases b <;> simp only [Val.and, Val.map₂, reduceCtorEq, Option.some.injEq] at h
  next x y =>
  have hx : x = BitVec.allOnes w := by
    ext i hi
    have := congrArg (·[i]) h
    simp only [BitVec.getElem_and, BitVec.getElem_allOnes, Bool.and_eq_true] at this
    simp [this.1]
  have hy : y = BitVec.allOnes w := by
    ext i hi
    have := congrArg (·[i]) h
    simp only [BitVec.getElem_and, BitVec.getElem_allOnes, Bool.and_eq_true] at this
    simp [this.2]
  exact ⟨by rw [hx], by rw [hy]⟩

theorem andConst?_denote {ρ : Env} {u : Nat} {t x : Term u} {y : BitVec u} (h : andConst? t = some (x, y))
    (hc : t.Consistent ρ) : t.denote ρ = Val.and (x.denote ρ) (some y) := by
  unfold andConst? at h
  split at h
  · next f x' yc hb =>
    cases hy : apint yc with
    | none => simp [hy] at h
    | some y' =>
      simp only [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [← apint_denote hy]
      exact (ok_inj (Shift.binop?_denote hb hc)).symm
  · cases h

end Select

open Select in
/-- What `simplifySelectWithICmpCond`'s steps under `eq` return refines a `select` on `CmpLHS == CmpRHS`, with or
without `samesign`, at every width, in every run its operands are consistent with. -/
theorem simplifySelectWithICmpCond.eqSteps_sound (ρ : Env) {u : Nat} (cl cr : Term u) (tv fv : Term w) (n : Nat)
    (s : Bool) (ccl : cl.Consistent ρ) (ctv : tv.Consistent ρ) (cfv : fv.Consistent ρ) :
    ∀ site r, Step.fire site r ∈ simplifySelectWithICmpCond.eqSteps cl cr tv fv n →
      Refines (Outcome.ok (IRLean.select (Val.icmpEq (cl.denote ρ) (cr.denote ρ) s) (tv.denote ρ) (fv.denote ρ)))
        (r.eval ρ) := by
  intro site r hmem
  have hold : Val.icmpEq (cl.denote ρ) (cr.denote ρ) s = some 1#1 → cl.denote ρ = cr.denote ρ :=
    fun h => (icmpEq_eq_one h).1
  simp only [simplifySelectWithICmpCond.eqSteps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h
  · -- The bit test.
    split at h
    · next hz =>
      split at h
      · next x y hxy =>
        split at h
        · next hu =>
          subst hu
          have hres := fwd_fire h.symm
          have hbt : BitTest (Val.icmpEq (cl.denote ρ) (cr.denote ρ) s) (x.denote ρ) y true := by
            rw [andConst?_denote hxy ccl, cst_eq hz]
            exact bitTest_of_icmpEq
          exact simplifySelectBitTest.sound ρ _ tv fv x y true hbt ctv cfv hres
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · exact simplifySelectWithEquivalence.sound ρ _ _ tv fv n
      (fun hc p hp => by simp only [List.mem_singleton] at hp; subst hp; exact hold hc) (fwd_fire h.symm)
  · exact simplifySelectWithEquivalence.sound ρ _ _ tv fv n
      (fun hc p hp => by simp only [List.mem_singleton] at hp; subst hp; exact (hold hc).symm) (fwd_fire h.symm)
  · split at h
    · next hz =>
      split at h
      · next f x y hb =>
        refine simplifySelectWithEquivalence.sound ρ _ _ tv fv n (fun hc p hp => ?_) (fwd_fire h.symm)
        have hcl := hold hc
        rw [cst_eq hz, ← (ok_inj (Shift.binop?_denote hb ccl))] at hcl
        have := or_eq_zero hcl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · simp only [cst_eq hz]; exact this.1
        · simp only [cst_eq hz]; exact this.2
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  · split at h
    · next ha =>
      split at h
      · next f x y hb =>
        refine simplifySelectWithEquivalence.sound ρ _ _ tv fv n (fun hc p hp => ?_) (fwd_fire h.symm)
        have hcl := hold hc
        rw [cst_eq ha, ← (ok_inj (Shift.binop?_denote hb ccl))] at hcl
        have := and_eq_allOnes hcl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · simp only [cst_eq ha]; exact this.1
        · simp only [cst_eq ha]; exact this.2
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h

open Select in
/-- What `Select.selectOnInst` returns refines the `select` it's given, at every width, in every run the `select` is
consistent with, poison included. -/
theorem Select.selectOnInst_sound (o : Oracle) (ρ : Env) (t : Term w) (ct : t.Consistent ρ) {r : Repl w}
    (h : Select.selectOnInst o t = .value r) : Refines (t.top.eval ρ) (r.eval ρ) := by
  unfold Select.selectOnInst at h
  split at h
  · next id c a b =>
    obtain ⟨cc, ca, cb, -⟩ := ct
    change Refines (Outcome.ok (IRLean.select (c.denote ρ) (a.denote ρ) (b.denote ρ))) (r.eval ρ)
    refine run_sound (P := fun r => Refines (Outcome.ok (IRLean.select (c.denote ρ) (a.denote ρ) (b.denote ρ)))
      (r.eval ρ)) ?_ h
    intro site r hmem
    simp only [Select.selectEntry.steps, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with hm | hm | hm
    · split at hm <;> simp only [reduceCtorEq] at hm
    · unfold simplifySelectWithICmpCond.steps at hm
      split at hm
      · next id' p s cl cr =>
        obtain ⟨ccl, -, hd⟩ := cc
        have hcd : (Term.icmp id' p s cl cr).denote ρ = p.eval (cl.denote ρ) (cr.denote ρ) s := hd.symm
        rw [hcd]
        simp only [List.mem_cons] at hm
        rcases hm with hm | hm
        · split at hm <;> simp only [reduceCtorEq] at hm
        · split at hm
          · next hp =>
            subst hp
            exact simplifySelectWithICmpCond.eqSteps_sound ρ cl cr a b 3 s ccl ca cb site r hm
          · split at hm
            · next hp =>
              subst hp
              rw [show Pred.eval .ne (cl.denote ρ) (cr.denote ρ) s = Val.icmpNe (cl.denote ρ) (cr.denote ρ) s from rfl,
                select_ne]
              exact simplifySelectWithICmpCond.eqSteps_sound ρ cl cr b a 3 s ccl cb ca site r hm
            · simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hm
      · simp only [List.not_mem_nil] at hm
    · simp only [reduceCtorEq] at hm
  · cases h

end Peephole.IS
