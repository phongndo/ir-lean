import IRLean.Int

/-! # Experimental: `undef` and `freeze`

**A prototype, not the model.** `IRLean.lean` doesn't import this, the emitter never targets it, and no claim in status,
trust or a certificate rests on it. [`docs/undef-freeze.md`](../../docs/undef-freeze.md) says what it's for, what it
settles, and what it leaves open.

What LangRef 23.1.3 says, in "Undefined Values", "Poison Values" and "`freeze`":

- `undef`: "the user of the value may receive an unspecified bit-pattern", and "an `undef` 'variable' can arbitrarily
  change its value over its 'live range'". So `%C = xor %B, %B` with `%B = undef` is `undef`, and "to ensure all uses
  of a given register observe the same value (even if `undef`), the freeze instruction can be used".
- Poison: "Most instructions return `poison` when one of their arguments is `poison`", and "it is correct to replace a
  poison value with an undef value or any value of the type".
- `freeze`: "If the argument is `undef` or `poison`, `freeze` returns an arbitrary, but fixed, value of type `ty`.
  Otherwise, this instruction is a no-op and returns the input argument. All uses of a value returned by the same
  `freeze` instruction are guaranteed to always observe the same value, while different `freeze` instructions may
  yield different values."

So there are two kinds of choice here, made at different times:

- **Per use.** An SSA value is the set, `UVal`, of what a use of it may see. Each operand of each instruction is a use,
  and draws its own element. An instruction's result is what it gives over every draw of its operands, and each use of
  that result draws again. `undef` is every value, poison is `{none}`, and a value `x` is `{some x}`.
- **Per run.** `freeze` chooses once, when it runs, and gives that one value, which every use sees. A computation is
  the set, `Run`, of what it can give: one result for each way its `freeze`s can choose.

Instructions are the model's own operations on `Val`, applied to each draw, so on single values this is the model:
`lift₂_of`, `freeze_of_some`. Where the model stops, at `freeze` of poison, this chooses: `freeze_of_none`.

Refinement nests the two: for every input, for every way the target's `freeze`s choose, there's a way the source's can
choose, such that whatever a use of the target's result sees, a use of the source's could see something it refines.
`ValLe` is poison allowing anything and a value only itself, as in the model's `Val`. -/

namespace IRLean.Experimental.UndefFreeze

open IRLean

/-- What a use of an SSA value of width `w` may see: one element of this set, a value or poison (`none`). Each use
chooses again. -/
abbrev UVal (w : Nat) := Val w → Prop

namespace UVal

/-- A value of the model, or poison: a use sees it and nothing else. -/
def of (a : Val w) : UVal w := fun e => e = a

/-- A constant. -/
def const (x : BitVec w) : UVal w := of (some x)

/-- `poison`. -/
def poison : UVal w := of none

/-- `undef`: a use sees any value, never poison. -/
def undef : UVal w := fun e => ∃ x, e = some x

end UVal

/-! ### Instructions: the model's, applied to each draw -/

/-- One operand, drawn once for this use. -/
def lift₁ (f : Val w → Val v) (a : UVal w) : UVal v := fun r => ∃ x, a x ∧ r = f x

/-- Two operands, each a use of its own, so each draws its own element: `lift₂ f a a` draws from `a` twice. -/
def lift₂ (f : Val w → Val v → Val u) (a : UVal w) (b : UVal v) : UVal u :=
  fun r => ∃ x y, a x ∧ b y ∧ r = f x y

/-- Three operands, for `select`. -/
def lift₃ (f : Val k → Val w → Val v → Val u) (a : UVal k) (b : UVal w) (c : UVal v) : UVal u :=
  fun r => ∃ x y z, a x ∧ b y ∧ c z ∧ r = f x y z

def add (a b : UVal w) (nuw nsw : Bool := false) : UVal w := lift₂ (fun x y => Val.add x y nuw nsw) a b
def sub (a b : UVal w) (nuw nsw : Bool := false) : UVal w := lift₂ (fun x y => Val.sub x y nuw nsw) a b
def mul (a b : UVal w) (nuw nsw : Bool := false) : UVal w := lift₂ (fun x y => Val.mul x y nuw nsw) a b
def and (a b : UVal w) : UVal w := lift₂ Val.and a b
def or (a b : UVal w) (disjoint : Bool := false) : UVal w := lift₂ (fun x y => Val.or x y disjoint) a b
def xor (a b : UVal w) : UVal w := lift₂ Val.xor a b
def icmpEq (a b : UVal w) : UVal 1 := lift₂ (fun x y => Val.icmpEq x y) a b
def icmpSlt (a b : UVal w) : UVal 1 := lift₂ (fun x y => Val.icmpSlt x y) a b
def icmpSge (a b : UVal w) : UVal 1 := lift₂ (fun x y => Val.icmpSge x y) a b
/-- An `undef` condition draws either arm, as LangRef's `select undef, %X, %Y` examples say. -/
def select (c : UVal 1) (t e : UVal w) : UVal w := lift₃ (fun x y z => IRLean.select x y z) c t e

/-! ### Runs, and `freeze` -/

/-- What a computation can give: one result for each way its `freeze`s can choose. -/
def Run (α : Type) : Type := α → Prop

namespace Run

def pure (a : α) : Run α := fun r => r = a

def bind (m : Run α) (k : α → Run β) : Run β := fun r => ∃ a, m a ∧ k a r

instance : Monad Run where
  pure := Run.pure
  bind := Run.bind

@[simp] theorem pure_apply (a r : α) : (Pure.pure a : Run α) r ↔ r = a := Iff.rfl

@[simp] theorem bind_apply (m : Run α) (k : α → Run β) (r : β) : (m >>= k) r ↔ ∃ a, m a ∧ k a r := Iff.rfl

end Run

/-- `freeze`: one of the values a use of `a` could see, or any value if a use could see poison. It's chosen once, when
`freeze` runs, and its result is that one value, so every use of it sees the same thing. -/
def freeze (a : UVal w) : Run (UVal w) := fun r => ∃ x, (a (some x) ∨ a none) ∧ r = UVal.const x

/-! ### Refinement -/

/-- `b` refines `a`: poison allows anything, and a value only itself. The model's order on `Val`. -/
def ValLe : Val w → Val w → Prop
  | none, _ => True
  | some x, b => b = some x

/-- `t` refines `s` for every use: whatever a use of `t` sees, a use of `s` could see something it refines. -/
def UVal.le (s t : UVal w) : Prop := ∀ b, t b → ∃ a, s a ∧ ValLe a b

/-- `tgt` refines `src`: however `tgt`'s `freeze`s choose, `src`'s can choose so that its result refines `tgt`'s.
The source's choice is made once for the run, before any use of the result draws. -/
def Run.le (src tgt : Run (UVal w)) : Prop := ∀ T, tgt T → ∃ S, src S ∧ UVal.le S T

/-- An input: what each use of an argument may see. Any nonempty set, which is more than LLVM can pass, so a proof for
every `Arg` covers every input LLVM has, `undef` and partly `undef` ones included. -/
structure Arg (w : Nat) where
  uses : UVal w
  nonempty : ∃ e, uses e

/-- `tgt` is a correct replacement for `src`, on every input. Inputs are `Arg`s, or tuples of them. -/
def Refines (src tgt : ι → Run (UVal w)) : Prop := ∀ i, Run.le (src i) (tgt i)

/-! ### Refinement is a preorder -/

theorem ValLe.refl (a : Val w) : ValLe a a := by
  cases a <;> simp [ValLe]

theorem ValLe.trans {a b c : Val w} (h₁ : ValLe a b) (h₂ : ValLe b c) : ValLe a c := by
  cases a with
  | none => trivial
  | some x =>
    simp only [ValLe] at h₁
    subst h₁
    exact h₂

theorem UVal.le_refl (a : UVal w) : UVal.le a a := fun b hb => ⟨b, hb, ValLe.refl b⟩

theorem UVal.le_trans {a b c : UVal w} (h₁ : UVal.le a b) (h₂ : UVal.le b c) : UVal.le a c := by
  intro z hz
  obtain ⟨y, hy, hyz⟩ := h₂ z hz
  obtain ⟨x, hx, hxy⟩ := h₁ y hy
  exact ⟨x, hx, ValLe.trans hxy hyz⟩

theorem Run.le_refl (m : Run (UVal w)) : Run.le m m := fun T hT => ⟨T, hT, UVal.le_refl T⟩

theorem Run.le_trans {a b c : Run (UVal w)} (h₁ : Run.le a b) (h₂ : Run.le b c) : Run.le a c := by
  intro T hT
  obtain ⟨M, hM, hMT⟩ := h₂ T hT
  obtain ⟨S, hS, hSM⟩ := h₁ M hM
  exact ⟨S, hS, UVal.le_trans hSM hMT⟩

theorem Refines.refl (f : ι → Run (UVal w)) : Refines f f := fun i => Run.le_refl (f i)

theorem Refines.trans {f g h : ι → Run (UVal w)} (h₁ : Refines f g) (h₂ : Refines g h) : Refines f h :=
  fun i => Run.le_trans (h₁ i) (h₂ i)

/-! ### Refinement is preserved by every instruction, `freeze` and sequencing

So replacing part of a computation with a refinement of it refines the whole: a local rewrite is sound in any context
built from these. -/

/-- `f` takes refined operands to a refined result. -/
def Mono₂ (f : Val w → Val v → Val u) : Prop :=
  ∀ a a' b b', ValLe a a' → ValLe b b' → ValLe (f a b) (f a' b')

/-- An operation that gives poison for a poison operand respects refinement. -/
theorem Mono₂.of_strict (f : Val w → Val v → Val u) (h₁ : ∀ b, f none b = none) (h₂ : ∀ a, f a none = none) :
    Mono₂ f := by
  intro a a' b b' ha hb
  cases a with
  | none => simp [h₁, ValLe]
  | some x =>
    simp only [ValLe] at ha
    subst ha
    cases b with
    | none => simp [h₂, ValLe]
    | some y =>
      simp only [ValLe] at hb
      subst hb
      exact ValLe.refl _

theorem lift₂_mono {f : Val w → Val v → Val u} (hf : Mono₂ f) {a a' : UVal w} {b b' : UVal v}
    (ha : UVal.le a a') (hb : UVal.le b b') : UVal.le (lift₂ f a b) (lift₂ f a' b') := by
  rintro r ⟨x', y', hx', hy', rfl⟩
  obtain ⟨x, hx, hxx⟩ := ha x' hx'
  obtain ⟨y, hy, hyy⟩ := hb y' hy'
  exact ⟨f x y, ⟨x, y, hx, hy, rfl⟩, hf x x' y y' hxx hyy⟩

theorem add_mono (nuw nsw : Bool) : Mono₂ (fun x y : Val w => Val.add x y nuw nsw) :=
  Mono₂.of_strict _ (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
theorem sub_mono (nuw nsw : Bool) : Mono₂ (fun x y : Val w => Val.sub x y nuw nsw) :=
  Mono₂.of_strict _ (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
theorem mul_mono (nuw nsw : Bool) : Mono₂ (fun x y : Val w => Val.mul x y nuw nsw) :=
  Mono₂.of_strict _ (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
theorem and_mono : Mono₂ (Val.and : Val w → Val w → Val w) :=
  Mono₂.of_strict _ (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
theorem or_mono (disjoint : Bool) : Mono₂ (fun x y : Val w => Val.or x y disjoint) :=
  Mono₂.of_strict _ (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
theorem xor_mono : Mono₂ (Val.xor : Val w → Val w → Val w) :=
  Mono₂.of_strict _ (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)

/-- `select` isn't strict in its arms, since the other arm doesn't matter, but it still respects refinement. -/
theorem select_mono {c c' : UVal 1} {t t' e e' : UVal w} (hc : UVal.le c c') (ht : UVal.le t t')
    (he : UVal.le e e') : UVal.le (select c t e) (select c' t' e') := by
  rintro r ⟨x', y', z', hx', hy', hz', rfl⟩
  obtain ⟨x, hx, hxx⟩ := hc x' hx'
  obtain ⟨y, hy, hyy⟩ := ht y' hy'
  obtain ⟨z, hz, hzz⟩ := he z' hz'
  refine ⟨IRLean.select x y z, ⟨x, y, z, hx, hy, hz, rfl⟩, ?_⟩
  cases x with
  | none => simp [IRLean.select, HasPoison.poison, ValLe]
  | some b =>
    simp only [ValLe] at hxx
    subst hxx
    simp only [IRLean.select]
    split <;> assumption

theorem pure_mono {a a' : UVal w} (h : UVal.le a a') : Run.le (Pure.pure a) (Pure.pure a') := by
  intro T hT
  simp only [Run.pure_apply] at hT
  subst hT
  exact ⟨a, rfl, h⟩

/-- Without `freeze`, a computation has one result, and refinement is refinement of it. -/
theorem Run.le_pure (a b : UVal w) : Run.le (Pure.pure a) (Pure.pure b) ↔ UVal.le a b := by
  constructor
  · intro h
    obtain ⟨S, hS, hle⟩ := h b rfl
    simp only [Run.pure_apply] at hS
    subst hS
    exact hle
  · exact pure_mono

theorem freeze_mono {a a' : UVal w} (h : UVal.le a a') : Run.le (freeze a) (freeze a') := by
  rintro T ⟨x, hx, rfl⟩
  refine ⟨UVal.const x, ⟨x, ?_, rfl⟩, UVal.le_refl _⟩
  rcases hx with hx | hx
  · obtain ⟨e, he, hle⟩ := h _ hx
    cases e with
    | none => exact Or.inr he
    | some y =>
      simp only [ValLe, Option.some.injEq] at hle
      subst hle
      exact Or.inl he
  · obtain ⟨e, he, hle⟩ := h _ hx
    cases e with
    | none => exact Or.inr he
    | some y => simp [ValLe] at hle

/-- Sequencing: refined first steps, followed by steps that respect refinement, refine the whole. -/
theorem bind_mono {m m' : Run (UVal w)} {k k' : UVal w → Run (UVal v)} (hm : Run.le m m')
    (hk : ∀ a a', UVal.le a a' → Run.le (k a) (k' a')) : Run.le (m >>= k) (m' >>= k') := by
  rintro T ⟨a', ha', hT⟩
  obtain ⟨a, ha, haa⟩ := hm a' ha'
  obtain ⟨S, hS, hST⟩ := hk a a' haa T hT
  exact ⟨S, ⟨a, ha, hS⟩, hST⟩

/-! ### On single values this is the model -/

theorem lift₂_of (f : Val w → Val v → Val u) (a : Val w) (b : Val v) :
    lift₂ f (UVal.of a) (UVal.of b) = UVal.of (f a b) := by
  funext r
  apply propext
  constructor
  · rintro ⟨x, y, rfl, rfl, rfl⟩
    rfl
  · intro h
    exact ⟨a, b, rfl, rfl, h⟩

theorem UVal.le_of (a b : Val w) : UVal.le (UVal.of a) (UVal.of b) ↔ ValLe a b := by
  constructor
  · intro h
    obtain ⟨x, hx, hle⟩ := h b rfl
    cases hx
    exact hle
  · rintro h c rfl
    exact ⟨a, rfl, h⟩

/-- `freeze` of a value is that value, as `Val.freeze (some x) = Outcome.ok (some x)` in the model. -/
theorem freeze_of_some (x : BitVec w) : freeze (UVal.of (some x)) = Pure.pure (UVal.of (some x)) := by
  funext r
  apply propext
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with hy | hy
    · cases hy
      rfl
    · cases hy
  · intro h
    exact ⟨x, Or.inl rfl, h⟩

/-- `freeze` of poison can be any value, where the model stops with `ModelStop.freezePoison`. -/
theorem freeze_of_none (r : UVal w) : freeze (UVal.of none) r ↔ ∃ x, r = UVal.const x := by
  constructor
  · rintro ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, Or.inr rfl, rfl⟩

/-- The model's `freeze` gives a result exactly where this one has a single choice, and stops exactly where this one
chooses among every value. -/
theorem model_freeze (a : Val w) :
    (∃ x, a = some x ∧ Val.freeze a = Outcome.ok a ∧ freeze (UVal.of a) = Pure.pure (UVal.of a)) ∨
      (a = none ∧ Val.freeze a = Outcome.stop .freezePoison ∧ ∀ r, freeze (UVal.of a) r ↔ ∃ x, r = UVal.const x) := by
  cases a with
  | some x => exact Or.inl ⟨x, rfl, rfl, freeze_of_some x⟩
  | none => exact Or.inr ⟨rfl, rfl, freeze_of_none⟩

/-! ### Poison, and what a set holding it means -/

/-- If a use could see poison, any result refines it: a set holding poison is as weak as poison. -/
theorem UVal.le_of_poison {s : UVal w} (h : s none) (t : UVal w) : UVal.le s t :=
  fun _ _ => ⟨none, h, trivial⟩

/-- Poison refines a set exactly when a use of the set could see poison. -/
theorem UVal.le_poison (s : UVal w) : UVal.le s UVal.poison ↔ s none := by
  constructor
  · intro h
    obtain ⟨a, ha, hle⟩ := h none rfl
    cases a with
    | none => exact ha
    | some x => simp [ValLe] at hle
  · intro h b hb
    exact ⟨none, h, trivial⟩

/-! ### Every computation here gives a result

A target with no result at all would refine anything, since `Run.le` asks something of each of its results. Nothing
here has none: an `Arg` is nonempty, instructions keep that, `freeze` always has a choice, and so does sequencing.
This is the prototype's answer to the model's stop at `freeze` of poison, which gives no result. -/

/-- The set is nonempty: some use sees something. -/
def UVal.Nonempty (a : UVal w) : Prop := ∃ e, a e

/-- The computation gives at least one result, and each of its results is nonempty. -/
def Run.Total (m : Run (UVal w)) : Prop := (∃ r, m r) ∧ ∀ r, m r → UVal.Nonempty r

theorem lift₂_nonempty (f : Val w → Val v → Val u) {a : UVal w} {b : UVal v} (ha : UVal.Nonempty a)
    (hb : UVal.Nonempty b) : UVal.Nonempty (lift₂ f a b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  exact ⟨f x y, x, y, hx, hy, rfl⟩

theorem pure_total {a : UVal w} (h : UVal.Nonempty a) : Run.Total (Pure.pure a) :=
  ⟨⟨a, rfl⟩, fun r hr => by simp only [Run.pure_apply] at hr; subst hr; exact h⟩

theorem freeze_total {a : UVal w} (h : UVal.Nonempty a) : Run.Total (freeze a) := by
  obtain ⟨e, he⟩ := h
  refine ⟨?_, ?_⟩
  · cases e with
    | none => exact ⟨UVal.const 0, 0, Or.inr he, rfl⟩
    | some x => exact ⟨UVal.const x, x, Or.inl he, rfl⟩
  · rintro r ⟨x, -, rfl⟩
    exact ⟨some x, rfl⟩

theorem bind_total {m : Run (UVal w)} {k : UVal w → Run (UVal v)} (hm : Run.Total m)
    (hk : ∀ a, UVal.Nonempty a → Run.Total (k a)) : Run.Total (m >>= k) := by
  obtain ⟨⟨a, ha⟩, hne⟩ := hm
  obtain ⟨⟨r, hr⟩, -⟩ := hk a (hne a ha)
  refine ⟨⟨r, a, ha, hr⟩, ?_⟩
  rintro r ⟨a, ha, hr⟩
  exact (hk a (hne a ha)).2 r hr

end IRLean.Experimental.UndefFreeze
