import IRLean.Refine

/-! # Counterexamples for refinement's laws

For each hypothesis of a lemma from `IRLean.Refine`, the lemma without it is false: `drop_<hypothesis>` gives one
instance where it fails, and `sat` gives one where its hypotheses all hold. A hypothesis that's an instance argument
has its position as its name: `[Refine.Reflexive α]` is needed because a run that stops the model refines nothing,
itself included. `tools/store/store.py check` checks each states exactly what it has to. -/

namespace LemmaStore.Counter

open IRLean

/-- A run that stops the model, which refines nothing. -/
abbrev stopped : Outcome (Val 1) := Outcome.stop .freezePoison

theorem stopped_not_le (b : Outcome (Val 1)) : ¬ Refine.le stopped b := Refine.outcome_stop _ _

/-- `some 0` and `some 1` in `i1`: a value allows only itself. -/
theorem zero_not_le_one : ¬ Refine.le (some 0#1 : Val 1) (some 1#1) := fun h => absurd ((Refine.val_some _ _).1 h)
  (by decide)

/-! ### Reflexivity needs `Refine.Reflexive` -/

theorem IRLean.Refine.outcome_le_self_iff.drop_2 :
    ¬ ∀ {α : Type} [Refine α] (o : Outcome α), Refine.le o o ↔ ∀ s, o ≠ Outcome.stop s := fun h =>
  have hs := (@h (Outcome (Val 1)) _ (Outcome.ok stopped)).2 (fun s e => by simp [Outcome.ok, Outcome.stop] at e)
  stopped_not_le _ ((Refine.outcome_ok_ok _ _).1 hs)

theorem IRLean.Refine.outcome_le_self_iff.sat :
    ∃ (α : Type) (_ : Refine α) (_ : Outcome α), Refine.Reflexive α := ⟨Val 1, inferInstance, none, inferInstance⟩

theorem IRLean.Refines.refl.drop_2 : ¬ ∀ {α : Type} [Refine α] (a : α), Refines a a :=
  fun h => stopped_not_le _ (@h (Outcome (Val 1)) _ stopped)

theorem IRLean.Refines.refl.sat : ∃ (α : Type) (_ : Refine α) (_ : α), Refine.Reflexive α :=
  ⟨Val 1, inferInstance, none, inferInstance⟩

theorem IRLean.Refines.self_iff.drop_3 :
    ¬ ∀ {α β : Type} [Refine β] (f : α → Outcome β), Refines f f ↔ ∀ x s, f x ≠ Outcome.stop s := fun h =>
  have hs := (@h Unit (Outcome (Val 1)) _ (fun _ => Outcome.ok stopped)).2
    (fun _ s e => by simp [Outcome.ok, Outcome.stop] at e)
  stopped_not_le _ ((Refine.outcome_ok_ok _ _).1 (hs ()))

theorem IRLean.Refines.self_iff.sat :
    ∃ (α β : Type) (_ : Refine β) (_ : α → Outcome β), Refine.Reflexive β :=
  ⟨Unit, Val 1, inferInstance, fun _ => none, inferInstance⟩

/-! ### Composition needs each step to refine -/

theorem IRLean.Refines.trans.drop_hab : ¬ ∀ {α : Type} [Refine α] {a b c : α}, Refines b c → Refines a c :=
  fun h => zero_not_le_one (@h (Val 1) _ (some 0#1) (some 1#1) (some 1#1) rfl)

theorem IRLean.Refines.trans.drop_hbc : ¬ ∀ {α : Type} [Refine α] {a b c : α}, Refines a b → Refines a c :=
  fun h => zero_not_le_one (@h (Val 1) _ (some 0#1) (some 0#1) (some 1#1) rfl)

theorem IRLean.Refines.trans.sat :
    ∃ (α : Type) (_ : Refine α) (a b c : α), Refines a b ∧ Refines b c :=
  ⟨Val 1, inferInstance, none, none, none, trivial, trivial⟩

/-- A run that returns `0` doesn't allow one that returns `1`. -/
theorem ok_zero_not_le_ok_one : ¬ Refine.le (Outcome.ok (some 0#1) : Outcome (Val 1)) (Outcome.ok (some 1#1)) :=
  fun h => zero_not_le_one ((Refine.outcome_ok_ok _ _).1 h)

theorem IRLean.Refine.andThen_mono.drop_hx :
    ¬ ∀ {α β : Type} [Refine α] [Refine β] {x x' : Outcome α} {k k' : α → Outcome β},
      (∀ a b, Refine.le a b → Refine.le (k a) (k' b)) → Refine.le (andThen x k) (andThen x' k') := fun h =>
  ok_zero_not_le_ok_one (@h (Val 1) (Val 1) _ _ (Outcome.ok (some 0#1)) (Outcome.ok (some 1#1)) Outcome.ok
    Outcome.ok (fun a b hab => (Refine.outcome_ok_ok a b).2 hab))

theorem IRLean.Refine.andThen_mono.drop_hk :
    ¬ ∀ {α β : Type} [Refine α] [Refine β] {x x' : Outcome α} {k k' : α → Outcome β},
      Refine.le x x' → Refine.le (andThen x k) (andThen x' k') := fun h =>
  ok_zero_not_le_ok_one (@h (Val 1) (Val 1) _ _ (Outcome.ok none) (Outcome.ok none)
    (fun _ => Outcome.ok (some 0#1)) (fun _ => Outcome.ok (some 1#1)) ((Refine.outcome_ok_ok _ _).2 trivial))

theorem IRLean.Refine.andThen_mono.sat :
    ∃ (α β : Type) (_ : Refine α) (_ : Refine β) (x x' : Outcome α) (k k' : α → Outcome β),
      Refine.le x x' ∧ ∀ a b, Refine.le a b → Refine.le (k a) (k' b) :=
  ⟨Val 1, Val 1, inferInstance, inferInstance, Outcome.ok none, Outcome.ok none, Outcome.ok, Outcome.ok,
    (Refine.outcome_ok_ok _ _).2 trivial, fun a b hab => (Refine.outcome_ok_ok a b).2 hab⟩

/-! ### Monotone operations need poison in to give poison out -/

/-- Poison to `0`, and any value to `1`: not strict. -/
def lift (a : Val 1) : Val 1 := if a.isSome then some 1#1 else some 0#1

theorem IRLean.Refine.val_map_mono.drop_hf :
    ¬ ∀ {w v : Nat} {f : Val w → Val v} {a b : Val w}, Refine.le a b → Refine.le (f a) (f b) :=
  fun h => absurd ((Refine.val_some _ _).1 (@h 1 1 lift none (some 0#1) trivial)) (by decide)

theorem IRLean.Refine.val_map_mono.drop_h :
    ¬ ∀ {w v : Nat} {f : Val w → Val v}, f none = none → ∀ {a b : Val w}, Refine.le (f a) (f b) :=
  fun h => zero_not_le_one (@h 1 1 id rfl (some 0#1) (some 1#1))

theorem IRLean.Refine.val_map_mono.sat :
    ∃ (w v : Nat) (f : Val w → Val v) (a b : Val w), f none = none ∧ Refine.le a b :=
  ⟨0, 0, id, none, none, rfl, trivial⟩

/-- The left operand where both are values, poison otherwise: strict in both. -/
def left : Val 1 → Val 1 → Val 1
  | some x, some _ => some x
  | _, _ => none

/-- The right operand where both are values, poison otherwise. -/
def right : Val 1 → Val 1 → Val 1
  | some _, some y => some y
  | _, _ => none

/-- Poison on the right gives poison, poison on the left `0`, and values `1`: strict on the right only. -/
def strictRight : Val 1 → Val 1 → Val 1
  | _, none => none
  | none, some _ => some 0#1
  | some _, some _ => some 1#1

/-- The same, the other way round. -/
def strictLeft (a b : Val 1) : Val 1 := strictRight b a

theorem IRLean.Refine.val_map₂_mono.drop_hl :
    ¬ ∀ {w u v : Nat} {f : Val w → Val u → Val v}, (∀ a, f a none = none) →
      ∀ {a a' : Val w} {b b' : Val u}, Refine.le a a' → Refine.le b b' → Refine.le (f a b) (f a' b') :=
  fun h => absurd ((Refine.val_some _ _).1
    (@h 1 1 1 strictRight (fun a => by cases a <;> rfl) none (some 0#1) (some 0#1) (some 0#1) trivial rfl))
    (by decide)

theorem IRLean.Refine.val_map₂_mono.drop_hr :
    ¬ ∀ {w u v : Nat} {f : Val w → Val u → Val v}, (∀ b, f none b = none) →
      ∀ {a a' : Val w} {b b' : Val u}, Refine.le a a' → Refine.le b b' → Refine.le (f a b) (f a' b') :=
  fun h => absurd ((Refine.val_some _ _).1
    (@h 1 1 1 strictLeft (fun b => by cases b <;> rfl) (some 0#1) (some 0#1) none (some 0#1) rfl trivial))
    (by decide)

theorem IRLean.Refine.val_map₂_mono.drop_ha :
    ¬ ∀ {w u v : Nat} {f : Val w → Val u → Val v}, (∀ b, f none b = none) → (∀ a, f a none = none) →
      ∀ {a a' : Val w} {b b' : Val u}, Refine.le b b' → Refine.le (f a b) (f a' b') :=
  fun h => zero_not_le_one
    (@h 1 1 1 left (fun _ => rfl) (fun a => by cases a <;> rfl) (some 0#1) (some 1#1) (some 0#1) (some 0#1) rfl)

theorem IRLean.Refine.val_map₂_mono.drop_hb :
    ¬ ∀ {w u v : Nat} {f : Val w → Val u → Val v}, (∀ b, f none b = none) → (∀ a, f a none = none) →
      ∀ {a a' : Val w} {b b' : Val u}, Refine.le a a' → Refine.le (f a b) (f a' b') :=
  fun h => zero_not_le_one
    (@h 1 1 1 right (fun _ => rfl) (fun a => by cases a <;> rfl) (some 0#1) (some 0#1) (some 0#1) (some 1#1) rfl)

theorem IRLean.Refine.val_map₂_mono.sat :
    ∃ (w u v : Nat) (f : Val w → Val u → Val v) (a a' : Val w) (b b' : Val u),
      (∀ b, f none b = none) ∧ (∀ a, f a none = none) ∧ Refine.le a a' ∧ Refine.le b b' :=
  ⟨0, 0, 0, fun _ _ => none, none, none, none, none, fun _ => rfl, fun _ => rfl, trivial, trivial⟩

end LemmaStore.Counter
