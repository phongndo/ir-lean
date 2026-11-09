import IRLean.Basic

/-! # Refinement

What it means for one function to be a correct replacement for another, in IRLean's semantics, for the integer and
vector code the model covers without memory. `Refines src tgt` says `tgt` only does what `src` allows, on every input,
poison included. [`docs/refinement.md`](../docs/refinement.md) says what that does and doesn't say about LLVM.

For a value, poison allows any value, and a value allows only itself. Vectors and structs go lane by lane, field by
field. For a run:

- If `src` is undefined, any `tgt` is allowed.
- If `src` stops the model, nothing is: the model doesn't know what LLVM does there.
- If `src` never finishes, `tgt` mustn't either.
- If `src` returns, `tgt` returns a value that refines it.

For a function, both get the same input, for every input its type has. An argument is a value or poison, never `undef`.

Every relation here is transitive, so refinements compose. A value refines itself, and a run refines itself exactly when
it doesn't stop the model, so for `f` into `Outcome`, `Refines f f` says `f` never stops the model on any input. A run
that makes choices refines itself where no way of choosing stops the model, and also where some way is undefined, which
allows anything: `Refine.outcomes_le_self`.

There's deliberately no instance for `Mem`. The emitter gives every function that mentions a pointer or touches memory a
`Mem` argument and a `Mem` in its result, so such a function has no `Refines` claim at all. -/

namespace IRLean

/-- `Refine.le a b`: `b` is allowed wherever `a` is. Every instance is transitive. -/
class Refine (α : Type) where
  le : α → α → Prop
  trans : ∀ {a b c : α}, le a b → le b c → le a c

/-- Poison allows anything, and a value only itself. -/
instance : Refine (Val w) where
  le a b := match a with
    | none => True
    | some x => b = some x
  trans {a b c} hab hbc := by
    cases a with
    | none => trivial
    | some x => cases hab; exact hbc

/-- Lane by lane: each lane is its own value, and may be poison on its own. -/
instance [Refine α] : Refine (Vector α n) where
  le a b := ∀ i : Fin n, Refine.le a[i] b[i]
  trans hab hbc i := Refine.trans (hab i) (hbc i)

/-- Field by field, for a struct. -/
instance [Refine α] [Refine β] : Refine (α × β) where
  le a b := Refine.le a.1 b.1 ∧ Refine.le a.2 b.2
  trans hab hbc := ⟨Refine.trans hab.1 hbc.1, Refine.trans hab.2 hbc.2⟩

/-- What a function returning `void` returns. -/
instance : Refine Unit where
  le _ _ := True
  trans _ _ := trivial

/-- A run: undefined behavior allows anything, a model stop nothing, a run that never finishes only another, and a
result only a result that refines it. -/
instance [Refine α] : Refine (Outcome α) where
  le a b := match a with
    | some (.error (.undefined _)) => True
    | some (.error (.model _)) => False
    | none => b = none
    | some (.ok x) => ∃ y, b = some (.ok y) ∧ Refine.le x y
  trans {a b c} hab hbc := by
    match a, hab with
    | some (.error (.undefined _)), _ => trivial
    | some (.error (.model _)), h => exact h.elim
    | none, hab => cases hab; exact hbc
    | some (.ok _), ⟨_, hb, hxy⟩ =>
      cases hb
      obtain ⟨z, hc, hyz⟩ := hbc
      exact ⟨z, hc, Refine.trans hxy hyz⟩

/-- Runs that make choices: however the target's `freeze`s choose, the source's can choose so that its run allows the
target's. Each side's choices are made for the whole run, and the source's after the target's, as LLVM's own
refinement has them: the target's nondeterminism is for any execution, and the source's is the optimizer's to pick.
A source that's undefined for some way of choosing allows anything. -/
instance [Refine α] : Refine (Outcomes α) where
  le a b := ∀ ct, ∃ cs, Refine.le (a cs) (b ct)
  trans {a b c} hab hbc ct := by
    obtain ⟨cm, h₂⟩ := hbc ct
    obtain ⟨cs, h₁⟩ := hab cm
    exact ⟨cs, Refine.trans h₁ h₂⟩

/-- For every input, the same input to both. Inputs range over everything the type has: for `Val`, poison too. -/
instance {α β : Type} [Refine β] : Refine (α → β) where
  le f g := ∀ x, Refine.le (f x) (g x)
  trans hfg hgh x := Refine.trans (hfg x) (hgh x)

/-- `tgt` is a correct replacement for `src`, in IRLean's semantics. -/
def Refines {α : Type} [Refine α] (src tgt : α) : Prop := Refine.le src tgt

/-- Types whose refinement is reflexive: values, and vectors, structs and functions of them. Not runs, since a model
stop refines nothing, itself included. -/
class Refine.Reflexive (α : Type) [Refine α] : Prop where
  refl : ∀ a : α, Refine.le a a

namespace Refine

/-! ### Unfolding

What each instance says, under names that don't depend on how the instances are named. Each is `Iff.rfl` or `trivial`,
so a proof using them proves the same statement as one unfolding the instances. -/

theorem val_none (b : Val w) : Refine.le (none : Val w) b := trivial
theorem val_some (x : BitVec w) (b : Val w) : Refine.le (some x : Val w) b ↔ b = some x := Iff.rfl

theorem val_iff (a b : Val w) : Refine.le a b ↔ a = none ∨ b = a := by
  cases a with
  | none => exact iff_of_true trivial (Or.inl rfl)
  | some x => exact ⟨Or.inr, fun h => h.resolve_left nofun⟩

theorem vector_iff [Refine α] (a b : Vector α n) : Refine.le a b ↔ ∀ i : Fin n, Refine.le a[i] b[i] := Iff.rfl

theorem prod_iff [Refine α] [Refine β] (a b : α × β) :
    Refine.le a b ↔ Refine.le a.1 b.1 ∧ Refine.le a.2 b.2 := Iff.rfl

theorem unit (a b : Unit) : Refine.le a b := trivial

theorem outcome_ok [Refine α] (x : α) (b : Outcome α) :
    Refine.le (Outcome.ok x) b ↔ ∃ y, b = some (.ok y) ∧ Refine.le x y := Iff.rfl

theorem outcome_ok_ok [Refine α] (x y : α) : Refine.le (Outcome.ok x) (Outcome.ok y) ↔ Refine.le x y :=
  ⟨fun ⟨_, h, hxy⟩ => by cases h; exact hxy, fun h => ⟨y, rfl, h⟩⟩

theorem outcome_ub [Refine α] (r : UB) (b : Outcome α) : Refine.le (Outcome.ub r : Outcome α) b := trivial

theorem outcome_stop [Refine α] (s : ModelStop) (b : Outcome α) : ¬ Refine.le (Outcome.stop s : Outcome α) b := id

theorem outcome_none [Refine α] (b : Outcome α) : Refine.le (none : Outcome α) b ↔ b = none := Iff.rfl

theorem fn {α β : Type} [Refine β] (f g : α → β) : Refine.le f g ↔ ∀ x, Refine.le (f x) (g x) := Iff.rfl

theorem outcomes_iff [Refine α] (a b : Outcomes α) : Refine.le a b ↔ ∀ ct, ∃ cs, Refine.le (a cs) (b ct) := Iff.rfl

/-- Two runs that make no choices: refinement of their outcomes. -/
theorem outcomes_det [Refine α] (a b : Outcome α) :
    Refine.le (Outcomes.det a) (Outcomes.det b) ↔ Refine.le a b :=
  ⟨fun h => let ⟨_, hc⟩ := h default; hc, fun h _ => ⟨default, h⟩⟩

/-- A source that makes no choices: every way the target chooses has to be allowed. -/
theorem outcomes_det_left [Refine α] (a : Outcome α) (b : Outcomes α) :
    Refine.le (Outcomes.det a) b ↔ ∀ ct, Refine.le a (b ct) :=
  ⟨fun h ct => let ⟨_, hc⟩ := h ct; hc, fun h ct => ⟨default, h ct⟩⟩

/-- A target that makes no choices: some way the source chooses has to allow it. -/
theorem outcomes_det_right [Refine α] (a : Outcomes α) (b : Outcome α) :
    Refine.le a (Outcomes.det b) ↔ ∃ cs, Refine.le (a cs) b :=
  ⟨fun h => h default, fun h _ => h⟩

/-- Choosing the same on both sides is enough, and often how a proof goes. -/
theorem outcomes_of_same [Refine α] {a b : Outcomes α} (h : ∀ c, Refine.le (a c) (b c)) : Refine.le a b :=
  fun ct => ⟨ct, h ct⟩

/-! ### Reflexivity -/

instance : Reflexive (Val w) where
  refl
    | none => trivial
    | some _ => rfl

instance [Refine α] [Reflexive α] : Reflexive (Vector α n) where
  refl _ _ := Reflexive.refl _

instance [Refine α] [Refine β] [Reflexive α] [Reflexive β] : Reflexive (α × β) where
  refl _ := ⟨Reflexive.refl _, Reflexive.refl _⟩

instance : Reflexive Unit where
  refl _ := trivial

instance {α β : Type} [Refine β] [Reflexive β] : Reflexive (α → β) where
  refl _ _ := Reflexive.refl _

theorem refl_val (a : Val w) : Refine.le a a := Reflexive.refl a

/-- A run refines itself exactly when it doesn't stop the model. -/
theorem outcome_le_self_iff [Refine α] [Reflexive α] (o : Outcome α) :
    Refine.le o o ↔ ∀ s, o ≠ Outcome.stop s := by
  match o with
  | none => exact iff_of_true rfl nofun
  | some (.ok x) => exact iff_of_true ⟨x, rfl, Reflexive.refl x⟩ nofun
  | some (.error (.undefined _)) => exact iff_of_true trivial nofun
  | some (.error (.model s)) => exact iff_of_false id fun h => h s rfl

/-- Runs that make choices refine themselves where no way of choosing stops the model. Not the converse: a run
undefined for one way of choosing allows anything, its own stops included. -/
theorem outcomes_le_self [Refine α] [Reflexive α] {o : Outcomes α} (h : ∀ c s, o c ≠ Outcome.stop s) :
    Refine.le o o :=
  outcomes_of_same fun c => (outcome_le_self_iff (o c)).2 (h c)

/-! ### Composition -/

/-- Replacing a run by one that refines it, before a continuation that keeps refinement, gives a refinement. The
continuation has to keep it for every pair of results, since poison may have become a value. -/
theorem andThen_mono [Refine α] [Refine β] {x x' : Outcome α} {k k' : α → Outcome β}
    (hx : Refine.le x x') (hk : ∀ a b, Refine.le a b → Refine.le (k a) (k' b)) :
    Refine.le (andThen x k) (andThen x' k') := by
  match x, hx with
  | some (.error (.undefined _)), _ => trivial
  | some (.error (.model _)), h => exact h.elim
  | none, hx => cases hx; exact rfl
  | some (.ok a), ⟨b, hb, hab⟩ => cases hb; exact hk a b hab

/-- An operation giving poison for poison keeps refinement: `IRLean.Contract.Strict₁`. -/
theorem val_map_mono {f : Val w → Val v} (hf : f none = none) {a b : Val w} (h : Refine.le a b) :
    Refine.le (f a) (f b) := by
  cases a with
  | none => rw [hf]; trivial
  | some x => cases h; exact Reflexive.refl _

/-- The same, for two operands: `IRLean.Contract.Strict₂`. -/
theorem val_map₂_mono {f : Val w → Val u → Val v} (hl : ∀ b, f none b = none) (hr : ∀ a, f a none = none)
    {a a' : Val w} {b b' : Val u} (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (f a b) (f a' b') := by
  cases a with
  | none => rw [hl]; trivial
  | some x =>
    cases ha
    cases b with
    | none => rw [hr]; trivial
    | some y => cases hb; exact Reflexive.refl _

end Refine

namespace Refines

theorem trans [Refine α] {a b c : α} (hab : Refines a b) (hbc : Refines b c) : Refines a c := Refine.trans hab hbc

theorem refl [Refine α] [Refine.Reflexive α] (a : α) : Refines a a := Refine.Reflexive.refl a

/-- Equal functions refine each other where the source refines itself, which for a run means it never stops the model.
Equality alone isn't enough: two functions stopping the model at the same input are equal, and LLVM may still tell
them apart there. -/
theorem of_eq [Refine α] {src tgt : α} (h : src = tgt) (hs : Refines src src) : Refines src tgt := h ▸ hs

/-- A function of one argument refines itself exactly when it never stops the model. -/
theorem self_iff {α β : Type} [Refine β] [Refine.Reflexive β] (f : α → Outcome β) :
    Refines f f ↔ ∀ x s, f x ≠ Outcome.stop s :=
  forall_congr' fun x => Refine.outcome_le_self_iff (f x)

end Refines

end IRLean
