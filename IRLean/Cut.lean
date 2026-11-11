import IRLean.Promise
import IRLean.Refine

/-! # A refined cut gives a refined function

A cut of a function is a slice of its instructions, with the values that go in and come out. This is the lemma that
turns a proof about a cut into a theorem about the function: if the cut is refined by its replacement, the function
with the cut replaced refines the original. [`docs/refinement.md`](../docs/refinement.md#the-cut-lemma) says what it
covers.

It's stated over what the emitter emits, which has two levels, so it has two halves:

- **Inside a block,** instructions are chained with `andThen` and `let`. `Outcome.Sim.andThen`: a run replaced by one
  that refines it, before a continuation that keeps refinement, gives a refinement.
- **Between blocks,** `run` drives a `step` function over the function's `Block` type, and the source and the target
  each have their own. `Outcome.Sim.run`: if blocks related by `R` step to blocks related by `R`, or return results
  that refine, then the runs refine. The blocks run in lockstep, so the cut can sit in a loop, but can't change which
  blocks run.

Both are about `Outcome.Sim`, which is `IRLean.Refine`'s rule for a run with one change: a source that stops the model
allows anything, where `Refine.le` has it allow nothing. That's what makes it compose: the code after a cut is the same
on both sides, and where it stops the model on the source's values there's no claim to keep. The stop is accounted for
once, at the end: `Refine.le a b` is `Outcome.Sim Refine.le a b` and `a` not stopping the model
(`Refine.le_iff_sim`). `Outcome.answered` says the same in a statement: `Refine.le a.answered b` is
`Outcome.Sim Refine.le a b`.

The code after the cut has to keep refinement, and the same code on both sides isn't enough for that: it's given a
value where the source had poison. `IRLean/Mono.lean` proves it of the model's operations, one by one. -/

namespace IRLean

/-- `o`, with a model stop read as undefined behavior: where the model has no answer for the source, a claim about
`o.answered` makes none. A statement that uses it says so, where one that doesn't claims the source never stops the
model. -/
@[llvm] def Outcome.answered (o : Outcome α) : Outcome α :=
  match o with
  | some (.error (.model _)) => Outcome.ub .assumeFailed
  | o => o

/-- `a` allows `b`, wherever the model has an answer for `a`: `IRLean.Refine`'s rule for a run, for results related
by `r`, with a source that stops the model allowing anything. The two runs can be of different types, as two
functions' blocks are. -/
def Outcome.Sim (r : α → β → Prop) (a : Outcome α) (b : Outcome β) : Prop :=
  match a with
  | some (.error _) => True
  | none => b = none
  | some (.ok x) => ∃ y, b = some (.ok y) ∧ r x y

/-- What two blocks do last, related: both jump, to blocks related by `R`, or both return, results related by `r`. -/
def Next.Rel (R : β → β' → Prop) (r : ρ → ρ' → Prop) : Next β ρ → Next β' ρ' → Prop
  | .jump b, .jump b' => R b b'
  | .ret x, .ret y => r x y
  | _, _ => False

namespace Outcome.Sim

variable {α α' β β' γ γ' : Type}

theorem ok {r : α → β → Prop} {x : α} {y : β} (h : r x y) : Sim r (Outcome.ok x) (Outcome.ok y) := ⟨y, rfl, h⟩

theorem ok_iff {r : α → β → Prop} {x : α} {y : β} : Sim r (Outcome.ok x) (Outcome.ok y) ↔ r x y :=
  ⟨fun ⟨_, h, hxy⟩ => by cases h; exact hxy, ok⟩

/-- A source that's undefined allows anything. -/
theorem ub {r : α → β → Prop} (u : UB) (b : Outcome β) : Sim r (Outcome.ub u : Outcome α) b := trivial

/-- So does one that stops the model: there's no claim there to keep. -/
theorem stop {r : α → β → Prop} (s : ModelStop) (b : Outcome β) : Sim r (Outcome.stop s : Outcome α) b := trivial

/-- The same run on both sides. -/
theorem refl {r : α → α → Prop} (hr : ∀ x, r x x) (a : Outcome α) : Sim r a a := by
  match a with
  | none => exact rfl
  | some (.error _) => trivial
  | some (.ok x) => exact ⟨x, rfl, hr x⟩

/-- Results related more loosely. -/
theorem mono {r s : α → β → Prop} {a : Outcome α} {b : Outcome β} (h : Sim r a b) (hrs : ∀ x y, r x y → s x y) :
    Sim s a b := by
  match a, h with
  | none, h => exact h
  | some (.error _), _ => trivial
  | some (.ok _), ⟨y, hb, hxy⟩ => exact ⟨y, hb, hrs _ _ hxy⟩

theorem trans {r : α → β → Prop} {s : β → γ → Prop} {t : α → γ → Prop} {a : Outcome α} {b : Outcome β}
    {c : Outcome γ} (hab : Sim r a b) (hbc : Sim s b c) (ht : ∀ x y z, r x y → s y z → t x z) : Sim t a c := by
  match a, hab with
  | none, hab => cases hab; exact hbc
  | some (.error _), _ => trivial
  | some (.ok _), ⟨y, hb, hxy⟩ =>
    cases hb
    obtain ⟨z, hc, hyz⟩ := hbc
    exact ⟨z, hc, ht _ _ _ hxy hyz⟩

/-- **The cut lemma, inside a block.** A run replaced by one it allows, before a continuation that keeps the relation,
gives runs that are related. `x` and `x'` are the cut and its replacement, and `k` and `k'` the instructions after
them. The continuation has to keep the relation for every pair of related results, since the replacement may give a
value where the cut gave poison. -/
theorem andThen {r : α → α' → Prop} {s : β → β' → Prop} {x : Outcome α} {x' : Outcome α'} {k : α → Outcome β}
    {k' : α' → Outcome β'} (hx : Sim r x x') (hk : ∀ a b, r a b → Sim s (k a) (k' b)) :
    Sim s (IRLean.andThen x k) (IRLean.andThen x' k') := by
  match x, hx with
  | none, hx => cases hx; exact rfl
  | some (.error _), _ => trivial
  | some (.ok a), ⟨b, hb, hab⟩ => cases hb; exact hk a b hab

/-- Two blocks that jump to related blocks. -/
theorem jump {R : β → β' → Prop} {r : γ → γ' → Prop} {b : β} {b' : β'} (h : R b b') :
    Sim (Next.Rel R r) (IRLean.jump b) (IRLean.jump b') := ok h

/-- Two blocks that return related results. -/
theorem ret {R : β → β' → Prop} {r : γ → γ' → Prop} {x : γ} {y : γ'} (h : r x y) :
    Sim (Next.Rel R r) (IRLean.ret x) (IRLean.ret y) := ok h

/-- A branch on a condition the target's refines, to blocks related either way. A poison condition is undefined in
the source, so it allows anything. -/
theorem br {R : β → β' → Prop} {r : γ → γ' → Prop} {c c' : Val 1} {t e : β} {t' e' : β'} (hc : Refine.le c c')
    (ht : R t t') (he : R e e') : Sim (Next.Rel R r) (IRLean.br c t e) (IRLean.br c' t' e') := by
  cases c with
  | none => trivial
  | some x =>
    cases hc
    simp only [IRLean.br]
    split
    · exact jump ht
    · exact jump he

end Outcome.Sim

/-! ### What doesn't stop the model

A whole function's claim needs its source never to stop the model, `Refines.of_sim`, and `run_ne_stop` reduces that to
its blocks. -/

theorem jump_ne_stop {β ρ : Type} (b : β) (s : ModelStop) : (jump b : Outcome (Next β ρ)) ≠ Outcome.stop s := nofun

theorem ret_ne_stop {β ρ : Type} (x : ρ) (s : ModelStop) : (ret x : Outcome (Next β ρ)) ≠ Outcome.stop s := nofun

theorem br_ne_stop {β ρ : Type} (c : Val 1) (t e : β) (s : ModelStop) :
    (br c t e : Outcome (Next β ρ)) ≠ Outcome.stop s := by
  cases c with
  | none => nofun
  | some x => simp only [br]; split <;> nofun

theorem andThen_ne_stop {α β : Type} {x : Outcome α} {k : α → Outcome β} {s : ModelStop}
    (hx : x ≠ Outcome.stop s) (hk : ∀ a, k a ≠ Outcome.stop s) : andThen x k ≠ Outcome.stop s := by
  match x, hx with
  | none, _ => nofun
  | some (.ok a), _ => exact hk a
  | some (.error (.undefined _)), _ => nofun
  | some (.error (.model t)), hx =>
    intro h
    simp only [andThen, Outcome.stop, Option.some.injEq, Except.error.injEq, Stop.model.injEq] at h
    exact hx (h ▸ rfl)

/-- The same, where the continuation is only known not to stop the model on what `x` returned. -/
theorem andThen_ne_stop_of {α β : Type} {x : Outcome α} {k : α → Outcome β} {s : ModelStop}
    (hx : x ≠ Outcome.stop s) (hk : ∀ a, x = Outcome.ok a → k a ≠ Outcome.stop s) :
    andThen x k ≠ Outcome.stop s := by
  match x, hx, hk with
  | none, _, _ => nofun
  | some (.ok a), _, hk => exact hk a rfl
  | some (.error (.undefined _)), _, _ => nofun
  | some (.error (.model t)), hx, _ =>
    intro h
    simp only [andThen, Outcome.stop, Option.some.injEq, Except.error.injEq, Stop.model.injEq] at h
    exact hx (h ▸ rfl)

/-! ### `Sim` and `Refine.le` -/

namespace Refine

/-- `Refine.le` on runs is `Outcome.Sim`, and the source not stopping the model. -/
theorem le_iff_sim [Refine α] (a b : Outcome α) :
    Refine.le a b ↔ Outcome.Sim Refine.le a b ∧ ∀ s, a ≠ Outcome.stop s := by
  match a with
  | none => exact ⟨fun h => ⟨h, nofun⟩, fun h => h.1⟩
  | some (.ok x) => exact ⟨fun h => ⟨h, nofun⟩, fun h => h.1⟩
  | some (.error (.undefined _)) => exact ⟨fun _ => ⟨trivial, nofun⟩, fun _ => trivial⟩
  | some (.error (.model s)) => exact ⟨fun h => h.elim, fun h => h.2 s rfl⟩

theorem sim_of_le [Refine α] {a b : Outcome α} (h : Refine.le a b) : Outcome.Sim Refine.le a b :=
  ((le_iff_sim a b).1 h).1

theorem le_of_sim [Refine α] {a b : Outcome α} (h : Outcome.Sim Refine.le a b) (ha : ∀ s, a ≠ Outcome.stop s) :
    Refine.le a b :=
  (le_iff_sim a b).2 ⟨h, ha⟩

/-- A claim about `a.answered` is `Outcome.Sim`: `b` is allowed wherever the model has an answer for `a`. -/
theorem answered_iff [Refine α] (a b : Outcome α) : Refine.le a.answered b ↔ Outcome.Sim Refine.le a b := by
  match a with
  | none => exact Iff.rfl
  | some (.ok _) => exact Iff.rfl
  | some (.error (.undefined _)) => exact Iff.rfl
  | some (.error (.model _)) => exact Iff.rfl

/-- A run that doesn't stop the model is its own `answered`. -/
theorem answered_of_ne_stop {a : Outcome α} (h : ∀ s, a ≠ Outcome.stop s) : a.answered = a := by
  match a, h with
  | none, _ => rfl
  | some (.ok _), _ => rfl
  | some (.error (.undefined _)), _ => rfl
  | some (.error (.model s)), h => exact absurd rfl (h s)

/-- A claim with the guard follows from one without: the guard only takes inputs out. -/
theorem answered_of_le [Refine α] {a b : Outcome α} (h : Refine.le a b) : Refine.le a.answered b :=
  (answered_iff a b).2 (sim_of_le h)

end Refine

/-! ### Blocks under `run` -/

section Run

variable {β β' ρ ρ' : Type}

/-- What a run does after a block: it returns the block's result, or goes on from the block it jumps to. -/
def Next.run (step : β → Outcome (Next β ρ)) : Next β ρ → Outcome ρ
  | .ret r => Outcome.ok r
  | .jump next => IRLean.run step next

/-- A run is its first block, and then the rest: for a function that's one block, its instructions and its
result. -/
theorem run_eq (step : β → Outcome (Next β ρ)) (b : β) : run step b = andThen (step b) (Next.run step) := by
  rw [run]
  match step b with
  | none => rfl
  | some (.error _) => rfl
  | some (.ok (.ret _)) => rfl
  | some (.ok (.jump _)) => rfl

theorem andThen_ret_run (step : β → Outcome (Next β ρ)) (r : ρ) : andThen (ret r) (Next.run step) = Outcome.ok r :=
  rfl

theorem andThen_assoc {α γ δ : Type} (x : Outcome α) (k : α → Outcome γ) (k' : γ → Outcome δ) :
    andThen (andThen x k) k' = andThen x fun a => andThen (k a) k' := by
  match x with
  | none => rfl
  | some (.error _) => rfl
  | some (.ok _) => rfl

/-- `run`, for at most `n` blocks: `none` if it needs more. -/
def runFuel (step : β → Outcome (Next β ρ)) : Nat → β → Option (Outcome ρ)
  | 0, _ => none
  | n + 1, b =>
    match step b with
    | none => some none
    | some (.error e) => some (some (.error e))
    | some (.ok (.ret r)) => some (Outcome.ok r)
    | some (.ok (.jump next)) => runFuel step n next

/-- A run that ends within `n` blocks, or waits for good on one of them, is what `run` gives. -/
theorem run_of_runFuel {step : β → Outcome (Next β ρ)} {n : Nat} {b : β} {o : Outcome ρ}
    (h : runFuel step n b = some o) : run step b = o := by
  induction n generalizing b with
  | zero => cases h
  | succ n ih =>
    rw [run]
    simp only [runFuel] at h
    split at h
    · rename_i hs; rw [hs]; cases h; rfl
    · rename_i hs; rw [hs]; cases h; rfl
    · rename_i hs; rw [hs]; cases h; rfl
    · rename_i hs; rw [hs]; exact ih h

/-- A run that ends does so within some number of blocks. -/
theorem runFuel_of_run {step : β → Outcome (Next β ρ)} {b : β} {x : Except Stop ρ} (h : run step b = some x) :
    ∃ n, runFuel step n b = some (some x) := by
  have := run.fixpoint_induct step (fun f => ∀ b x, f b = some x → ∃ n, runFuel step n b = some (some x))
    (Lean.Order.admissible_pi_apply _ fun _ =>
      Lean.Order.admissible_pi _ fun _ => Lean.Order.Option.admissible_eq_some _ _)
    (fun f hf b x h => by
      simp only at h
      split at h
      · cases h
      · rename_i e he; cases h; exact ⟨1, by simp only [runFuel, he]⟩
      · rename_i v hv; cases h; exact ⟨1, by simp only [runFuel, hv]; rfl⟩
      · rename_i n hn
        obtain ⟨k, hk⟩ := hf n x h
        exact ⟨k + 1, by simp only [runFuel, hn]; exact hk⟩)
  exact this b x h

/-- A run stops the model only where one of its blocks does. -/
theorem run_ne_stop {step : β → Outcome (Next β ρ)} (h : ∀ b s, step b ≠ Outcome.stop s) (b : β) (s : ModelStop) :
    run step b ≠ Outcome.stop s := by
  intro hr
  obtain ⟨n, hn⟩ := runFuel_of_run hr
  induction n generalizing b with
  | zero => cases hn
  | succ n ih =>
    simp only [runFuel] at hn
    split at hn
    · cases hn
    · rename_i e he; cases hn; exact h b s he
    · cases hn
    · rename_i nx _; exact ih nx (run_of_runFuel hn) hn

/-- Two functions' blocks in lockstep, for `n` blocks. -/
private theorem runFuel_sim {R : β → β' → Prop} {r : ρ → ρ' → Prop} {step : β → Outcome (Next β ρ)}
    {step' : β' → Outcome (Next β' ρ')} (h : ∀ b b', R b b' → Outcome.Sim (Next.Rel R r) (step b) (step' b'))
    (n : Nat) {b : β} {b' : β'} (hb : R b b') :
    match runFuel step n b with
    | none => runFuel step' n b' = none
    | some none => runFuel step' n b' = some none
    | some (some (.error _)) => True
    | some (some (.ok x)) => ∃ y, runFuel step' n b' = some (Outcome.ok y) ∧ r x y := by
  induction n generalizing b b' with
  | zero => rfl
  | succ n ih =>
    have hs := h b b' hb
    simp only [runFuel]
    match hsb : step b, hs with
    | none, hs =>
      have hs' : step' b' = none := hs
      simp only [hs']
    | some (.error _), _ => trivial
    | some (.ok (.ret x)), ⟨y, hy, hxy⟩ =>
      match y, hxy with
      | .ret y, hxy => simp only [hy]; exact ⟨y, rfl, hxy⟩
    | some (.ok (.jump nx)), ⟨y, hy, hxy⟩ =>
      match y, hxy with
      | .jump ny, hxy => simp only [hy]; exact ih hxy

/-- **The cut lemma, between blocks.** Two functions whose blocks, where related by `R`, step to blocks related by `R`
or return results related by `r`, have runs related by `r`, from any two related blocks. The functions are the one
with the cut and the one with its replacement, `R` says which of their blocks correspond and how their live values
are related, and the hypothesis is checked block by block: `Outcome.Sim.andThen` for the block holding the cut, and
the same code on related values for the rest. -/
theorem Outcome.Sim.run {R : β → β' → Prop} {r : ρ → ρ' → Prop} {step : β → Outcome (Next β ρ)}
    {step' : β' → Outcome (Next β' ρ')} (h : ∀ b b', R b b' → Outcome.Sim (Next.Rel R r) (step b) (step' b'))
    {b : β} {b' : β'} (hb : R b b') : Outcome.Sim r (IRLean.run step b) (IRLean.run step' b') := by
  match hr : IRLean.run step b with
  | some (.error _) => trivial
  | some (.ok x) =>
    obtain ⟨n, hn⟩ := runFuel_of_run hr
    have hsim := runFuel_sim h n hb
    rw [hn] at hsim
    obtain ⟨y, hy, hxy⟩ := hsim
    exact ⟨y, run_of_runFuel hy, hxy⟩
  | none =>
    show IRLean.run step' b' = none
    match hr' : IRLean.run step' b' with
    | none => rfl
    | some x' =>
      obtain ⟨n, hn⟩ := runFuel_of_run hr'
      have hsim := runFuel_sim h n hb
      match hf : runFuel step n b, hsim with
      | none, hsim => rw [hn] at hsim; cases hsim
      | some none, hsim => rw [hn] at hsim; cases hsim
      | some (some y), _ => rw [run_of_runFuel hf] at hr; cases hr

end Run

/-! ### What a refined cut gives -/

namespace Refines

/-- What a proof about a cut says at one input: where the cut returns, its replacement returns a result it allows.
A cut is emitted as a function of its own, so its proof is a `Refines`, and this is how it's used in the block that
holds the cut. -/
theorem ok_of_fn {α β : Type} [Refine β] {f g : α → Outcome β} (h : Refines f g) {x : α} {a : β}
    (hf : f x = Outcome.ok a) : ∃ b, g x = Outcome.ok b ∧ Refine.le a b := by
  have := h x
  rw [hf] at this
  exact this

/-- What a proof about a cut gives the block that holds it: the cut on the source's values allows its replacement on
the target's. A cut is emitted as a function of its own, of the values that go in, so its proof is a `Refines`, at one
input for both. In the function the two get different inputs, the target's refining the source's, since code before
the cut may already have run its replacement: in a loop, the round before. So the replacement has to keep refinement
of its inputs too, which `refine_mono` proves of integer and vector code. -/
theorem sim_cut {ι γ : Type} [Refine ι] [Refine γ] {c c' : ι → Outcome γ} (h : Refines c c')
    (hc' : ∀ x y, Refine.le x y → Outcome.Sim Refine.le (c' x) (c' y)) {x y : ι} (hxy : Refine.le x y) :
    Outcome.Sim Refine.le (c x) (c' y) :=
  (Refine.sim_of_le (h x)).trans (hc' x y hxy) fun _ _ _ => Refine.trans

/-- A whole function from `Outcome.Sim`, which the cut lemma gives, where the source never stops the model. -/
theorem of_sim {α β : Type} [Refine β] {f g : α → Outcome β} (h : ∀ x, Outcome.Sim Refine.le (f x) (g x))
    (hf : ∀ x s, f x ≠ Outcome.stop s) : Refines f g :=
  fun x => Refine.le_of_sim (h x) (hf x)

end Refines

end IRLean
