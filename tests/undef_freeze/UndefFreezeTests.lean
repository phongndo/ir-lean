import IRLean.Experimental.UndefFreeze

/-! Tests for `IRLean.Experimental.UndefFreeze`, run by `tests/undef_freeze.sh`.

1. LangRef 23.1.3's own examples, from "Undefined Values" and the `freeze` instruction, with its verdicts: what it
   calls safe is a refinement here, and what it calls unsafe isn't, with the counterexample.
2. Rewrites with a known verdict: the `freeze` cases of `tests/verification_negative`, under their names, and the
   `mul`/`add` example of "Taming Undefined Behavior in LLVM" (PLDI 2017).
3. Four shortcuts a semantics or a checker could take, each certifying a wrong rewrite that `Refines` rejects.

`tests/undef_freeze/alive2.tsv` lists the rewrites of sections 1 and 2 that are LLVM IR, with the verdict here, and
`tests/undef_freeze.sh` checks Alive2 gives the same one. -/

namespace UndefFreezeTests

open IRLean IRLean.Experimental.UndefFreeze

/-! ### Inputs -/

def undefArg : Arg w := ⟨UVal.undef, some 0, 0, rfl⟩
def poisonArg : Arg w := ⟨UVal.poison, none, rfl⟩
def constArg (x : BitVec w) : Arg w := ⟨UVal.const x, some x, rfl⟩

/-- A refinement that fails: a result of the target that no result of the source allows. The refinement comes first, so
its sets are known by the time the last argument is checked. -/
theorem refute {S T : UVal w} (hle : UVal.le S T) (b : Val w) (hb : T b) (h : ∀ a, S a → ¬ ValLe a b) : False := by
  obtain ⟨a, ha, hab⟩ := hle b hb
  exact h a ha hab

/-- The same, for computations without `freeze`. -/
theorem refute_pure {S T : UVal w} (hle : Run.le (Pure.pure S) (Pure.pure T)) (b : Val w) (hb : T b)
    (h : ∀ a, S a → ¬ ValLe a b) : False :=
  refute ((Run.le_pure S T).1 hle) b hb h

/-! ## 1. LangRef's examples

"Undefined Values", in pseudo IR without types. They're at `i8` here, apart from `select`'s condition. `%X` and `%Y`
are inputs, so any `Arg`: a value, poison, `undef`, or anything in between. -/

/-- `%A = add %X, undef` to `%A = undef`: safe, "because all of the output bits are affected by the undef bits". -/
theorem langref_add_undef_safe :
    Refines (fun x : Arg 8 => pure (add x.uses UVal.undef)) (fun _ => pure UVal.undef) := by
  intro x
  rw [Run.le_pure]
  rintro b ⟨v, rfl⟩
  obtain ⟨e, he⟩ := x.nonempty
  cases e with
  | none => exact ⟨none, ⟨none, some 0, he, ⟨0, rfl⟩, rfl⟩, trivial⟩
  | some a =>
    refine ⟨some v, ⟨some a, some (v - a), he, ⟨_, rfl⟩, ?_⟩, ValLe.refl _⟩
    simp only [Val.add, Bool.false_and, Bool.or_self, Bool.false_eq_true, ite_false, Option.some.injEq]
    bv_decide

/-- `%B = sub %X, undef` to `%B = undef`: safe. -/
theorem langref_sub_undef_safe :
    Refines (fun x : Arg 8 => pure (sub x.uses UVal.undef)) (fun _ => pure UVal.undef) := by
  intro x
  rw [Run.le_pure]
  rintro b ⟨v, rfl⟩
  obtain ⟨e, he⟩ := x.nonempty
  cases e with
  | none => exact ⟨none, ⟨none, some 0, he, ⟨0, rfl⟩, rfl⟩, trivial⟩
  | some a =>
    refine ⟨some v, ⟨some a, some (a - v), he, ⟨_, rfl⟩, ?_⟩, ValLe.refl _⟩
    simp only [Val.sub, Bool.false_and, Bool.or_self, Bool.false_eq_true, ite_false, Option.some.injEq]
    bv_decide

/-- `%C = xor %X, undef` to `%C = undef`: safe. -/
theorem langref_xor_undef_safe :
    Refines (fun x : Arg 8 => pure (xor x.uses UVal.undef)) (fun _ => pure UVal.undef) := by
  intro x
  rw [Run.le_pure]
  rintro b ⟨v, rfl⟩
  obtain ⟨e, he⟩ := x.nonempty
  cases e with
  | none => exact ⟨none, ⟨none, some 0, he, ⟨0, rfl⟩, rfl⟩, trivial⟩
  | some a =>
    refine ⟨some v, ⟨some a, some (a ^^^ v), he, ⟨_, rfl⟩, ?_⟩, ValLe.refl _⟩
    simp only [Val.xor, Val.map₂, Option.some.injEq]
    bv_decide

/-- `%A = or %X, undef` to `%A = -1`: safe. -/
theorem langref_or_undef_allOnes_safe :
    Refines (fun x : Arg 8 => pure (or x.uses UVal.undef)) (fun _ => pure (UVal.const (-1))) := by
  intro x
  rw [Run.le_pure]
  rintro b rfl
  obtain ⟨e, he⟩ := x.nonempty
  cases e with
  | none => exact ⟨none, ⟨none, some 0, he, ⟨0, rfl⟩, rfl⟩, trivial⟩
  | some a =>
    refine ⟨some (-1), ⟨some a, some (-1), he, ⟨_, rfl⟩, ?_⟩, ValLe.refl _⟩
    simp only [Val.or, Bool.false_and, Bool.false_eq_true, ite_false, Option.some.injEq]
    bv_decide

/-- `%B = and %X, undef` to `%B = 0`: safe. -/
theorem langref_and_undef_zero_safe :
    Refines (fun x : Arg 8 => pure (and x.uses UVal.undef)) (fun _ => pure (UVal.const 0)) := by
  intro x
  rw [Run.le_pure]
  rintro b rfl
  obtain ⟨e, he⟩ := x.nonempty
  cases e with
  | none => exact ⟨none, ⟨none, some 0, he, ⟨0, rfl⟩, rfl⟩, trivial⟩
  | some a =>
    refine ⟨some 0, ⟨some a, some 0, he, ⟨_, rfl⟩, ?_⟩, ValLe.refl _⟩
    simp only [Val.and, Val.map₂, Option.some.injEq]
    bv_decide

/-- `%A = or %X, undef` to `%A = %X`, "by choosing undef as 0": safe. -/
theorem langref_or_undef_self_safe :
    Refines (fun x : Arg 8 => pure (or x.uses UVal.undef)) (fun x => pure x.uses) := by
  intro x
  rw [Run.le_pure]
  intro b hb
  refine ⟨Val.or b (some 0), ⟨b, some 0, hb, ⟨0, rfl⟩, rfl⟩, ?_⟩
  cases b with
  | none => trivial
  | some a =>
    simp only [Val.or, Bool.false_and, Bool.false_eq_true, ite_false, ValLe, Option.some.injEq]
    bv_decide

/-- `%B = and %X, undef` to `%B = %X`, "by choosing undef as -1": safe. -/
theorem langref_and_undef_self_safe :
    Refines (fun x : Arg 8 => pure (and x.uses UVal.undef)) (fun x => pure x.uses) := by
  intro x
  rw [Run.le_pure]
  intro b hb
  refine ⟨Val.and b (some (-1)), ⟨b, some (-1), hb, ⟨_, rfl⟩, rfl⟩, ?_⟩
  cases b with
  | none => trivial
  | some a =>
    simp only [Val.and, Val.map₂, ValLe, Option.some.injEq]
    bv_decide

/-- `%A = or %X, undef` to `%A = undef`: unsafe. With `%X = 1`, the low bit is always set. -/
theorem langref_or_undef_undef_unsafe :
    ¬ Refines (fun x : Arg 8 => pure (or x.uses UVal.undef)) (fun _ => pure UVal.undef) := by
  intro h
  refine refute_pure (h (constArg 1)) (some 0) ⟨0, rfl⟩ ?_
  rintro a ⟨x, y, rfl, ⟨u, rfl⟩, rfl⟩
  simp only [Val.or, Bool.false_and, Bool.false_eq_true, ite_false, ValLe, Option.some.injEq]
  bv_decide

/-- `%B = and %X, undef` to `%B = undef`: unsafe. "If `%X` has a zero bit, then the output of the `and` operation
will always be a zero for that bit". -/
theorem langref_and_undef_undef_unsafe :
    ¬ Refines (fun x : Arg 8 => pure (and x.uses UVal.undef)) (fun _ => pure UVal.undef) := by
  intro h
  refine refute_pure (h (constArg 0)) (some 1) ⟨1, rfl⟩ ?_
  rintro a ⟨x, y, rfl, ⟨u, rfl⟩, rfl⟩
  simp only [Val.and, Val.map₂, ValLe, Option.some.injEq]
  bv_decide

/-! `select` on an `undef` condition "can go either way, but they have to come from one of the two operands". -/

/-- `%A = select undef, %X, %Y` to `%A = %X`: safe. -/
theorem langref_select_undef_left_safe :
    Refines (fun xy : Arg 8 × Arg 8 => pure (select UVal.undef xy.1.uses xy.2.uses)) (fun xy => pure xy.1.uses) := by
  rintro ⟨x, y⟩
  rw [Run.le_pure]
  intro b hb
  obtain ⟨e, he⟩ := y.nonempty
  exact ⟨b, ⟨some 1, b, e, ⟨1, rfl⟩, hb, he, rfl⟩, ValLe.refl b⟩

/-- `%A = select undef, %X, %Y` to `%A = %Y`: safe. -/
theorem langref_select_undef_right_safe :
    Refines (fun xy : Arg 8 × Arg 8 => pure (select UVal.undef xy.1.uses xy.2.uses)) (fun xy => pure xy.2.uses) := by
  rintro ⟨x, y⟩
  rw [Run.le_pure]
  intro b hb
  obtain ⟨e, he⟩ := x.nonempty
  exact ⟨b, ⟨some 0, e, b, ⟨0, rfl⟩, he, hb, rfl⟩, ValLe.refl b⟩

/-- `%B = select undef, 42, %Y` to `%B = 42`: safe. -/
theorem langref_select_undef_const_safe :
    Refines (fun y : Arg 8 => pure (select UVal.undef (UVal.const 42) y.uses)) (fun _ => pure (UVal.const 42)) := by
  intro y
  rw [Run.le_pure]
  rintro b rfl
  obtain ⟨e, he⟩ := y.nonempty
  exact ⟨some 42, ⟨some 1, some 42, e, ⟨1, rfl⟩, rfl, he, rfl⟩, ValLe.refl _⟩

/-- `%A = select undef, %X, %Y` to `%A = undef`: unsafe. With `%X = %Y = 0`, either arm is 0. -/
theorem langref_select_undef_undef_unsafe :
    ¬ Refines (fun xy : Arg 8 × Arg 8 => pure (select UVal.undef xy.1.uses xy.2.uses)) (fun _ => pure UVal.undef) := by
  intro h
  refine refute_pure (h (constArg 0, constArg 0)) (some 1) ⟨1, rfl⟩ ?_
  rintro a ⟨c, x, y, ⟨k, rfl⟩, rfl, rfl, rfl⟩
  simp only [IRLean.select]
  split <;> simp [ValLe]

/-- `%C = select %X, %Y, undef` to `%C = %Y`, "if `%Y` is provably not poison": safe. -/
theorem langref_select_undef_arm_safe (x : Arg 1) (y : Arg 8) (hy : ¬ y.uses none) :
    Run.le (pure (select x.uses y.uses UVal.undef)) (pure y.uses) := by
  rw [Run.le_pure]
  intro b hb
  obtain ⟨e, he⟩ := x.nonempty
  cases b with
  | none => exact absurd hb hy
  | some v =>
    cases e with
    | none => exact ⟨none, ⟨none, some v, some 0, he, hb, ⟨0, rfl⟩, rfl⟩, trivial⟩
    | some c =>
      by_cases hc : c = 1#1
      · exact ⟨some v, ⟨some c, some v, some 0, he, hb, ⟨0, rfl⟩, by simp [IRLean.select, hc]⟩, ValLe.refl _⟩
      · exact ⟨some v, ⟨some c, some v, some v, he, hb, ⟨v, rfl⟩, by simp [IRLean.select, hc]⟩, ValLe.refl _⟩

/-- The same, "unsafe otherwise": with `%X = 0` and `%Y` poison, the source is `undef`, which is never poison. -/
theorem langref_select_undef_arm_unsafe_for_poison :
    ¬ Refines (fun xy : Arg 1 × Arg 8 => pure (select xy.1.uses xy.2.uses UVal.undef)) (fun xy => pure xy.2.uses) := by
  intro h
  refine refute_pure (h (constArg 0, poisonArg)) none rfl ?_
  rintro a ⟨c, y, z, rfl, -, ⟨u, rfl⟩, rfl⟩
  simp [IRLean.select, ValLe]

/-! "Two `undef` operands are not necessarily the same", and a register holding `undef` isn't either: `%A` and `%C`
"need to have the same semantics or the core LLVM 'replace all uses with' concept would not hold". -/

/-- `%A = xor undef, undef` to `%A = undef`: safe. -/
theorem langref_xor_undef_undef_safe :
    Refines (fun _ : Unit => pure (xor (UVal.undef : UVal 8) UVal.undef)) (fun _ => pure UVal.undef) := by
  intro _
  rw [Run.le_pure]
  rintro b ⟨v, rfl⟩
  refine ⟨some v, ⟨some 0, some v, ⟨0, rfl⟩, ⟨v, rfl⟩, ?_⟩, ValLe.refl _⟩
  simp only [Val.xor, Val.map₂, Option.some.injEq]
  bv_decide

/-- `%B = undef`, `%C = xor %B, %B`: `%C` is what `%A` is, since a register without `freeze` is drawn at each use. -/
theorem langref_xor_register_same :
    (let b : UVal 8 := UVal.undef; xor b b) = xor (UVal.undef : UVal 8) UVal.undef := rfl

/-- `%D = undef`, `%E = icmp slt %D, 4` to `%E = undef`: safe. -/
theorem langref_icmp_undef_safe :
    Refines (fun _ : Unit => pure (icmpSlt (UVal.undef : UVal 8) (UVal.const 4))) (fun _ => pure UVal.undef) := by
  intro _
  rw [Run.le_pure]
  rintro b ⟨v, rfl⟩
  by_cases hv : v = 1#1
  · refine ⟨some 1, ⟨some 0, some 4, ⟨0, rfl⟩, rfl, by decide⟩, ?_⟩
    simp [ValLe, hv]
  · refine ⟨some 0, ⟨some 5, some 4, ⟨5, rfl⟩, rfl, by decide⟩, ?_⟩
    simp only [ValLe, Option.some.injEq]
    bv_decide

/-! The `freeze` instruction's example, at `i32`:

```llvm
%w = i32 undef
%x = freeze i32 %w
%y = add i32 %w, %w         ; undef
%z = add i32 %x, %x         ; even number because all uses of %x observe the same value
%x2 = freeze i32 %w
%cmp = icmp eq i32 %x, %x2  ; can be true or false
```
-/

/-- `%y = add i32 %w, %w`, "undef": it allows exactly what `undef` does, both ways. -/
theorem langref_freeze_y_is_undef :
    UVal.le (add (UVal.undef : UVal 32) UVal.undef) UVal.undef ∧
      UVal.le UVal.undef (add (UVal.undef : UVal 32) UVal.undef) := by
  constructor
  · rintro b ⟨v, rfl⟩
    refine ⟨some v, ⟨some 0, some v, ⟨0, rfl⟩, ⟨v, rfl⟩, ?_⟩, ValLe.refl _⟩
    simp only [Val.add, Bool.false_and, Bool.or_self, Bool.false_eq_true, ite_false, Option.some.injEq]
    bv_decide
  · rintro b ⟨x, y, ⟨u, rfl⟩, ⟨v, rfl⟩, rfl⟩
    exact ⟨_, ⟨u + v, rfl⟩, by simp [Val.add, ValLe]⟩

/-- So `%y` can be odd. -/
theorem langref_freeze_y_odd : (add (UVal.undef : UVal 32) UVal.undef) (some 1) :=
  ⟨some 0, some 1, ⟨0, rfl⟩, ⟨1, rfl⟩, rfl⟩

/-- `%x = freeze i32 %w`, `%z = add i32 %x, %x`: "even number because all uses of %x observe the same value". Every
run, and every use of its result. -/
theorem langref_freeze_z_even :
    ∀ r, (do let x ← freeze (UVal.undef : UVal 32); pure (add x x) : Run (UVal 32)) r →
      ∀ e, r e → ∃ z, e = some z ∧ z &&& 1 = 0 := by
  rintro r ⟨x, ⟨c, -, rfl⟩, hr⟩
  simp only [Run.pure_apply] at hr
  subst hr
  rintro e ⟨_, _, rfl, rfl, rfl⟩
  refine ⟨c + c, by simp [Val.add], ?_⟩
  bv_decide

/-- `%x2 = freeze i32 %w`, `%cmp = icmp eq i32 %x, %x2`: "can be true or false". -/
theorem langref_freeze_cmp_either :
    let prog : Run (UVal 1) := do
      let x ← freeze (UVal.undef : UVal 32)
      let x2 ← freeze (UVal.undef : UVal 32)
      pure (icmpEq x x2)
    prog (UVal.const 1) ∧ prog (UVal.const 0) := by
  constructor
  · refine ⟨UVal.const 0, ⟨0, Or.inl ⟨0, rfl⟩, rfl⟩, UVal.const 0, ⟨0, Or.inl ⟨0, rfl⟩, rfl⟩, ?_⟩
    simp only [Run.pure_apply, icmpEq, UVal.const, lift₂_of]
    rfl
  · refine ⟨UVal.const 0, ⟨0, Or.inl ⟨0, rfl⟩, rfl⟩, UVal.const 1, ⟨1, Or.inl ⟨1, rfl⟩, rfl⟩, ?_⟩
    simp only [Run.pure_apply, icmpEq, UVal.const, lift₂_of]
    rfl

/-- While the one `freeze`, compared with itself, is always true. -/
theorem freeze_cmp_self_true :
    ∀ r, (do let x ← freeze (UVal.undef : UVal 32); pure (icmpEq x x) : Run (UVal 1)) r → r = UVal.const 1 := by
  rintro r ⟨x, ⟨c, -, rfl⟩, hr⟩
  simp only [Run.pure_apply] at hr
  subst hr
  simp only [icmpEq, UVal.const, lift₂_of]
  congr
  simp [Val.icmpEq, Val.icmp]

/-- `%poison = add nsw i1 %k, undef`, which LangRef comments as poison. Here a use of it can see poison when `%k` is
true, as `-1 + -1` overflows. -/
theorem langref_add_nsw_undef_poison_if_true : (add (UVal.const 1#1) UVal.undef (nsw := true)) none :=
  ⟨some 1, some 1, rfl, ⟨1, rfl⟩, by decide⟩

/-- When `%k` is false nothing overflows, and no use sees poison: the comment is exact only for a true `%k`. -/
theorem langref_add_nsw_undef_no_poison_if_false : ¬ (add (UVal.const 0#1) UVal.undef (nsw := true)) none := by
  rintro ⟨x, y, rfl, ⟨u, rfl⟩, h⟩
  simp only [Val.add, Bool.false_and, Bool.true_and, Bool.false_or] at h
  split at h
  · bv_decide
  · cases h

/-- `%c = freeze i1 %poison`, `br i1 %c, ...`: "non-deterministic branch to `%foo` or `%bar`", for either `%k`. -/
theorem langref_freeze_branch_either (k : BitVec 1) :
    freeze (add (UVal.const k) UVal.undef (nsw := true)) (UVal.const 1) ∧
      freeze (add (UVal.const k) UVal.undef (nsw := true)) (UVal.const 0) := by
  obtain rfl | rfl : k = 0#1 ∨ k = 1#1 := by bv_decide
  · exact ⟨⟨1, Or.inl ⟨some 0, some 1, rfl, ⟨1, rfl⟩, by decide⟩, rfl⟩,
      ⟨0, Or.inl ⟨some 0, some 0, rfl, ⟨0, rfl⟩, by decide⟩, rfl⟩⟩
  · exact ⟨⟨1, Or.inr ⟨some 1, some 1, rfl, ⟨1, rfl⟩, by decide⟩, rfl⟩,
      ⟨0, Or.inr ⟨some 1, some 1, rfl, ⟨1, rfl⟩, by decide⟩, rfl⟩⟩

/-! ## 2. Rewrites with a known verdict -/

/-- `mul %x, 2` to `add %x, %x`: wrong. With `%x = undef`, the two uses of `%x` draw apart, so the target can be odd.
"Taming Undefined Behavior in LLVM", section 3. -/
theorem mul2_to_add_self_wrong :
    ¬ Refines (fun x : Arg 8 => pure (mul x.uses (UVal.const 2))) (fun x => pure (add x.uses x.uses)) := by
  intro h
  refine refute_pure (h undefArg) (some 1) ⟨some 0, some 1, ⟨0, rfl⟩, ⟨1, rfl⟩, rfl⟩ ?_
  rintro a ⟨x, y, ⟨u, rfl⟩, rfl, rfl⟩
  simp only [Val.mul, Bool.false_and, Bool.or_self, Bool.false_eq_true, ite_false, ValLe, Option.some.injEq]
  bv_decide

/-- `add %x, %x` to `mul %x, 2`: right. The target is one of the source's choices. -/
theorem add_self_to_mul2_right :
    Refines (fun x : Arg 8 => pure (add x.uses x.uses)) (fun x => pure (mul x.uses (UVal.const 2))) := by
  intro x
  rw [Run.le_pure]
  rintro b ⟨e, y, he, rfl, rfl⟩
  refine ⟨Val.add e e, ⟨e, e, he, he, rfl⟩, ?_⟩
  cases e with
  | none => trivial
  | some a =>
    simp only [Val.add, Val.mul, Bool.false_and, Bool.or_self, Bool.false_eq_true, ite_false, ValLe,
      Option.some.injEq]
    bv_decide

/-- `freeze_removed`: `freeze %x` to `%x`, wrong. With `%x` poison, the target is poison, which no frozen value
allows. -/
theorem freeze_removed_wrong : ¬ Refines (fun x : Arg 8 => freeze x.uses) (fun x => pure x.uses) := by
  intro h
  obtain ⟨S, ⟨c, -, rfl⟩, hle⟩ := h poisonArg poisonArg.uses rfl
  exact refute hle none rfl (by rintro a rfl; simp [ValLe])

/-- And with `%x = undef`: the target's uses can differ, and the frozen value can't. -/
theorem freeze_removed_wrong_for_undef : ¬ Run.le (freeze (UVal.undef : UVal 8)) (pure UVal.undef) := by
  intro h
  obtain ⟨S, ⟨c, -, rfl⟩, hle⟩ := h UVal.undef rfl
  refine refute hle (some (c + 1)) ⟨c + 1, rfl⟩ ?_
  rintro a rfl
  simp only [ValLe, Option.some.injEq]
  bv_decide

/-- `control_freeze_noundef_removed`: `freeze %x` to `%x` for a `noundef` `%x`, right: `freeze` of a value is it. -/
theorem freeze_noundef_removed_right :
    Refines (fun x : BitVec 8 => freeze (UVal.const x)) (fun x => pure (UVal.const x)) := by
  intro x
  show Run.le (freeze (UVal.of (some x))) (pure (UVal.of (some x)))
  rw [freeze_of_some]
  exact Run.le_refl _

/-- `freeze_added_unmodeled`: `%x` to `freeze %x`, right, for every input. The model can't certify this, since its
`freeze` stops on poison. -/
theorem freeze_added_right : Refines (fun x : Arg 8 => pure x.uses) (fun x => freeze x.uses) := by
  intro x
  rintro T ⟨c, hc, rfl⟩
  refine ⟨x.uses, rfl, ?_⟩
  rintro b rfl
  rcases hc with hc | hc
  · exact ⟨some c, hc, ValLe.refl _⟩
  · exact ⟨none, hc, trivial⟩

/-- `freeze_duplicated`'s source: one `freeze`, used twice. -/
def dupSrc (x : Arg 8) : Run (UVal 8) := do
  let a ← freeze x.uses
  pure (sub a a)

/-- And its target: two `freeze`s. -/
def dupTgt (x : Arg 8) : Run (UVal 8) := do
  let a ← freeze x.uses
  let b ← freeze x.uses
  pure (sub a b)

/-- The source always gives 0. -/
theorem dupSrc_zero (x : Arg 8) : ∀ S, dupSrc x S → S = UVal.const 0 := by
  rintro S ⟨_, ⟨c, -, rfl⟩, hS⟩
  simp only [Run.pure_apply] at hS
  subst hS
  simp only [sub, UVal.const, lift₂_of]
  congr
  simp [Val.sub]

/-- `freeze_duplicated`: wrong. With `%x` poison or `undef`, the two `freeze`s can choose 1 and 0. -/
theorem freeze_duplicated_wrong : ¬ Refines dupSrc dupTgt := by
  intro h
  have hT : dupTgt poisonArg (UVal.const 1) := by
    refine ⟨UVal.const 1, ⟨1, Or.inr rfl, rfl⟩, UVal.const 0, ⟨0, Or.inr rfl, rfl⟩, ?_⟩
    simp only [Run.pure_apply, sub, UVal.const, lift₂_of]
    rfl
  obtain ⟨S, hS, hle⟩ := h poisonArg _ hT
  rw [dupSrc_zero poisonArg S hS] at hle
  exact refute hle (some 1) rfl (by rintro a rfl; simp [ValLe])

/-- `sub %x, %x` to `0`: right. 0 is one of the source's choices, or the source is poison. -/
theorem sub_self_to_zero_right :
    Refines (fun x : Arg 8 => pure (sub x.uses x.uses)) (fun _ => pure (UVal.const 0)) := by
  intro x
  rw [Run.le_pure]
  rintro b rfl
  obtain ⟨e, he⟩ := x.nonempty
  refine ⟨Val.sub e e, ⟨e, e, he, he, rfl⟩, ?_⟩
  cases e with
  | none => trivial
  | some a => simp [Val.sub, ValLe]

/-- `0` to `sub %x, %x`: wrong. With `%x = undef`, the target can be 1. -/
theorem zero_to_sub_self_wrong :
    ¬ Refines (fun _ : Arg 8 => pure (UVal.const 0)) (fun x => pure (sub x.uses x.uses)) := by
  intro h
  refine refute_pure (h undefArg) (some 1) ⟨some 1, some 0, ⟨1, rfl⟩, ⟨0, rfl⟩, rfl⟩ ?_
  rintro a rfl
  simp [ValLe]

/-! Poison is stronger than `undef`: "It is correct to replace a poison value with an undef value or any value of the
type", and not the other way round. -/

theorem poison_to_undef_right : Refines (fun _ : Unit => pure (UVal.poison : UVal 8)) (fun _ => pure UVal.undef) :=
  fun _ => (Run.le_pure _ _).2 (UVal.le_of_poison (s := UVal.poison) rfl _)

theorem undef_to_value_right : Refines (fun _ : Unit => pure (UVal.undef : UVal 8)) (fun _ => pure (UVal.const 7)) := by
  intro _
  rw [Run.le_pure]
  rintro b rfl
  exact ⟨some 7, ⟨7, rfl⟩, ValLe.refl _⟩

theorem undef_to_poison_wrong : ¬ Refines (fun _ : Unit => pure (UVal.undef : UVal 8)) (fun _ => pure UVal.poison) := by
  intro h
  refine refute_pure (h ()) none rfl ?_
  rintro a ⟨x, rfl⟩
  simp [ValLe]

/-! ## 3. Shortcuts, each certifying a wrong rewrite -/

/-! ### Equality of the model's outcomes

The model stops at `freeze` of poison, in both functions of `freeze_duplicated`, so they're equal, though the rewrite
is wrong. `tests/verification_negative/cases/freeze_duplicated_equality_pin` is this case. -/

def dupSrcModel (x : Val 8) : Outcome (Val 8) :=
  andThen (Val.freeze x) fun a => Outcome.ok (Val.sub a a)

def dupTgtModel (x : Val 8) : Outcome (Val 8) :=
  andThen (Val.freeze x) fun a => andThen (Val.freeze x) fun b => Outcome.ok (Val.sub a b)

theorem shortcut_model_equality_accepts_freeze_duplicated : ∀ x, dupSrcModel x = dupTgtModel x := by
  intro x
  cases x <;> simp [dupSrcModel, dupTgtModel, Val.freeze, andThen, Outcome.ok, Outcome.stop]

/-! ### A target run, rather than every one

Matching one way the target's `freeze`s choose, as running it once would, certifies `0` to `freeze undef`: that run
chose 0. -/

def LeSomeRun (src tgt : Run (UVal w)) : Prop := ∃ T, tgt T ∧ ∃ S, src S ∧ UVal.le S T

theorem shortcut_some_run_accepts :
    LeSomeRun (pure (UVal.const 0)) (freeze (UVal.undef : UVal 8)) :=
  ⟨UVal.const 0, ⟨0, Or.inl ⟨0, rfl⟩, rfl⟩, UVal.const 0, rfl, UVal.le_refl _⟩

theorem zero_to_freeze_undef_wrong : ¬ Run.le (pure (UVal.const 0)) (freeze (UVal.undef : UVal 8)) := by
  intro h
  obtain ⟨S, hS, hle⟩ := h (UVal.const 1) ⟨1, Or.inl ⟨1, rfl⟩, rfl⟩
  simp only [Run.pure_apply] at hS
  subst hS
  exact refute hle (some 1) rfl (by rintro a rfl; simp [ValLe])

/-! ### Choosing the source's run for each use

Choosing how the source's `freeze`s go after seeing what one use of the target's result sees, as comparing one use of
each result would, certifies `freeze undef` to `undef`, though a second use of the target can differ. -/

def LePerUse (src tgt : Run (UVal w)) : Prop := ∀ T, tgt T → ∀ b, T b → ∃ S, src S ∧ ∃ a, S a ∧ ValLe a b

theorem shortcut_per_use_accepts : LePerUse (freeze (UVal.undef : UVal 8)) (pure UVal.undef) := by
  rintro T rfl b ⟨v, rfl⟩
  exact ⟨UVal.const v, ⟨v, Or.inl ⟨v, rfl⟩, rfl⟩, some v, rfl, ValLe.refl _⟩

/-- And it isn't preserved by a context: with the result used twice, as in `sub %r, %r`, the same shortcut rejects. -/
theorem shortcut_per_use_not_compositional :
    ¬ LePerUse (do let r ← freeze (UVal.undef : UVal 8); pure (sub r r))
        (do let r ← (pure UVal.undef : Run (UVal 8)); pure (sub r r)) := by
  intro h
  obtain ⟨S, ⟨_, ⟨c, -, rfl⟩, hS⟩, a, ha, hab⟩ :=
    h (sub UVal.undef UVal.undef) ⟨UVal.undef, rfl, rfl⟩ (some 1) ⟨some 1, some 0, ⟨1, rfl⟩, ⟨0, rfl⟩, rfl⟩
  simp only [Run.pure_apply] at hS
  subst hS
  obtain ⟨_, _, rfl, rfl, rfl⟩ := ha
  simp [Val.sub, ValLe] at hab

/-! ### A register keeps one value

Treating a register as fixed for all its uses, without `freeze`, is `pin`. It certifies `0` to `sub %a, %a` with
`%a = add %X, undef`, which LangRef rules out: it calls `%a = undef` a safe replacement, and then `sub undef, undef`
can be anything. -/

/-- Wrong: a register keeps one element, poison included, for all its uses. -/
def pin (a : UVal w) : Run (UVal w) := fun r => ∃ e, a e ∧ r = UVal.of e

def subSelfPinned (x : BitVec 8) : Run (UVal 8) := do
  let a ← pin (add (UVal.const x) UVal.undef)
  pure (sub a a)

def subSelfPerUse (x : BitVec 8) : Run (UVal 8) :=
  let a := add (UVal.const x) UVal.undef
  pure (sub a a)

theorem shortcut_pin_accepts : Refines (fun _ : BitVec 8 => pure (UVal.const 0)) subSelfPinned := by
  intro x
  rintro T ⟨_, ⟨e, ⟨_, _, rfl, ⟨u, rfl⟩, rfl⟩, rfl⟩, hT⟩
  simp only [Run.pure_apply] at hT
  subst hT
  refine ⟨UVal.const 0, rfl, ?_⟩
  rw [sub, lift₂_of]
  rintro b rfl
  exact ⟨some 0, rfl, by simp [Val.add, Val.sub, ValLe]⟩

theorem zero_to_sub_self_per_use_wrong : ¬ Refines (fun _ : BitVec 8 => pure (UVal.const 0)) subSelfPerUse := by
  intro h
  have hb : (sub (add (UVal.const 0) UVal.undef) (add (UVal.const 0) UVal.undef) : UVal 8) (some 1) :=
    ⟨some 1, some 0, ⟨_, _, rfl, ⟨1, rfl⟩, rfl⟩, ⟨_, _, rfl, ⟨0, rfl⟩, rfl⟩, rfl⟩
  exact refute_pure (h 0) (some 1) hb (by rintro a rfl; simp [ValLe])

/-- Why per use is LangRef's reading: its safe `%a = add %X, undef` to `%a = undef`, inside `sub %a, %a`, is a
refinement here, by the congruence lemmas alone, and `sub undef, undef` is 1 for some uses. A semantics where
`sub %a, %a` is always 0 would make that safe rewrite wrong. -/
theorem per_use_follows_langref (x : BitVec 8) :
    Run.le (subSelfPerUse x) (pure (sub UVal.undef UVal.undef)) ∧ (sub (UVal.undef : UVal 8) UVal.undef) (some 1) := by
  refine ⟨?_, some 1, some 0, ⟨1, rfl⟩, ⟨0, rfl⟩, rfl⟩
  have h := (Run.le_pure _ _).1 (langref_add_undef_safe (constArg x))
  exact pure_mono (lift₂_mono (sub_mono false false) h h)

end UndefFreezeTests
