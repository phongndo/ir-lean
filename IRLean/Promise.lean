import IRLean.Basic

/-! # Promises to progress

LangRef's `mustprogress` and `willreturn` function attributes, and its `llvm.loop.mustprogress` loop metadata, as the
model checks them. `docs/trust.md` says what's covered, and the emitter in `src/Emitter.cpp` says which drivers a
function gets.

In the model nothing a run does is observable from outside apart from its result: there's no I/O, `volatile`, atomics
or synchronization. So a run that never finishes under a promise breaks it, unless it's waiting on a call that never
returns. LangRef allows that of a callee without the promise: "If a mustprogress function calls a function not marked
mustprogress, and that function never returns, the program is well-defined". `willreturn` allows nothing: "If an
invocation of an annotated function does not return control back to a point in the call stack, the behavior is
undefined."

`run` gives `none` for both a loop that spins and a call that never returns, so it can't tell them apart. These do:

- `stay p step b` runs `b`, then each next block while `p` holds of it. It's `none` exactly when that never ends,
  which is when the run stays among blocks `p` holds of for good. A block that never finishes, which is a call that
  never returned, ends it, as `some none`.
- `runPromised p step b` runs blocks as `run` does, a `stay` at a time. A `stay` that never ends is
  `UB.noProgress`. A call that never returns is `none`, and so is a run that keeps coming back to blocks `p` doesn't
  hold of.

The emitter makes `p` true of every block of a function marked `mustprogress`, and of the blocks of each loop marked
`llvm.loop.mustprogress` otherwise. A loop's blocks are its natural loop's. A run that never leaves one loop's blocks
for good is one where that loop never terminates, and the emitter refuses a function where a cycle through these
blocks could leave every such loop, which only irreducible control flow can do, so staying among them means staying
in one loop.

Emitted code gives a function `promised (run f.step b) fun _ => runPromised f.promise f.step b`, so a proof about a
run that finishes is a proof about `run`, as before. `promised_run` says that's `runPromised f.promise f.step b`. -/

namespace IRLean

/-- What a run under a promise does: `r` if it finishes, and `diverged ()` if it doesn't. -/
@[llvm] def promised (r : Outcome α) (diverged : Unit → Outcome α) : Outcome α :=
  match r with
  | none => diverged ()
  | some x => some x

@[simp, llvm_val] theorem promised_some (x : Except Stop α) (d : Unit → Outcome α) :
    promised (some x) d = some x := rfl

@[llvm_val] theorem promised_ok (x : α) (d : Unit → Outcome α) : promised (Outcome.ok x) d = Outcome.ok x := rfl

@[llvm_val] theorem promised_ub (r : UB) (d : Unit → Outcome α) : promised (Outcome.ub r) d = Outcome.ub r := rfl

theorem promised_none (d : Unit → Outcome α) : promised (none : Outcome α) d = d () := rfl

/-- A run under a promise that finishes is that run: a proof that a function returns sets the promise aside with
this, and goes on about `run`. -/
theorem promised_of_eq {r : Outcome α} {d : Unit → Outcome α} {x : Except Stop α} (h : r = some x) :
    promised r d = some x := by
  rw [h]; rfl

/-- Runs `b`, and then each next block while `p` holds of it. `none` if that never ends. Otherwise how it ended: the
first next block `p` doesn't hold of, as a `jump`, a result, a stop, or `none` for a block that never finished,
which is a call that never returned. -/
def stay (p : β → Bool) (step : β → Outcome (Next β ρ)) (b : β) : Option (Outcome (Next β ρ)) :=
  match step b with
  | some (.ok (.jump n)) => if p n then stay p step n else some (jump n)
  | r => some r
partial_fixpoint

/-- Runs blocks from `b`, as `run` does, where `p` holds of the blocks under a promise to progress. A run that stays
among those blocks for good breaks the promise. A run waiting on a call that never returns doesn't, and nor does one
that keeps coming back to blocks `p` doesn't hold of. -/
def runPromised (p : β → Bool) (step : β → Outcome (Next β ρ)) (b : β) : Outcome ρ :=
  match stay p step b with
  | none => Outcome.ub .noProgress
  | some none => none
  | some (some (.error e)) => some (.error e)
  | some (some (.ok (.ret r))) => Outcome.ok r
  | some (some (.ok (.jump n))) => runPromised p step n
partial_fixpoint

/-! ### Running blocks -/

section Lemmas
variable {β ρ : Type} {p : β → Bool} {step : β → Outcome (Next β ρ)}

theorem stay_jump {b n : β} (h : step b = jump n) :
    stay p step b = if p n then stay p step n else some (jump n) := by
  rw [stay, h]; rfl

theorem stay_of_not_jump {b : β} (h : ∀ n, step b ≠ jump n) : stay p step b = some (step b) := by
  rw [stay]
  split
  · rename_i n hn; exact absurd hn (h n)
  · rfl

theorem runPromised_jump {b n : β} (h : step b = jump n) : runPromised p step b = runPromised p step n := by
  conv => lhs; rw [runPromised, stay_jump h]
  by_cases hp : p n
  · simp only [hp, ↓reduceIte]
    rw [runPromised]
  · simp only [hp]; rfl

theorem runPromised_ret {b : β} {r : ρ} (h : step b = ret r) : runPromised p step b = Outcome.ok r := by
  rw [runPromised, stay_of_not_jump (by rw [h]; nofun), h]; rfl

theorem runPromised_error {b : β} {e : Stop} (h : step b = some (.error e)) :
    runPromised p step b = some (.error e) := by
  rw [runPromised, stay_of_not_jump (by rw [h]; nofun), h]

/-- A block that never finishes, waiting on a call, isn't a broken promise. -/
theorem runPromised_stuck {b : β} (h : step b = none) : runPromised p step b = none := by
  rw [runPromised, stay_of_not_jump (by rw [h]; nofun), h]

/-- From any block in `I`, the next one is in `I` too. Then a run from one never finishes. -/
theorem run_forever (I : β → Prop) (hI : ∀ b, I b → ∃ n, step b = jump n ∧ I n) {b : β} (hb : I b) :
    run step b = none := by
  have := run.fixpoint_induct step (fun f => ∀ b, I b → f b = none)
    (Lean.Order.admissible_pi_apply (fun b (r : Outcome _) => I b → r = none) fun _ =>
      Lean.Order.admissible_flatOrder _ fun _ => rfl)
    (fun f hf b hb => by
      obtain ⟨n, hn, hIn⟩ := hI b hb
      simp only [hn, jump, Outcome.ok]
      exact hf n hIn)
  exact this b hb

/-- From any block in `I`, the next one is in `I` too, and `p` holds of it. Then a run from one stays among blocks `p`
holds of for good. -/
theorem stay_forever (I : β → Prop) (hI : ∀ b, I b → ∃ n, step b = jump n ∧ p n ∧ I n) {b : β} (hb : I b) :
    stay p step b = none := by
  have := stay.fixpoint_induct p step (fun f => ∀ b, I b → f b = none)
    (Lean.Order.admissible_pi_apply (fun b (r : Option (Outcome _)) => I b → r = none) fun _ =>
      Lean.Order.admissible_flatOrder _ fun _ => rfl)
    (fun f hf b hb => by
      obtain ⟨n, hn, hp, hIn⟩ := hI b hb
      simp only [hn, jump, Outcome.ok, hp, ↓reduceIte]
      exact hf n hIn)
  exact this b hb

/-! ### `runPromised` is `run`, apart from runs that never finish -/

/-- A run that finishes under `run` finishes the same way under `runPromised`. -/
theorem runPromised_of_run {b : β} {x : Except Stop ρ} (h : run step b = some x) :
    runPromised p step b = some x := by
  have := run.fixpoint_induct step (fun f => ∀ b x, f b = some x → runPromised p step b = some x)
    (Lean.Order.admissible_pi_apply _ fun _ =>
      Lean.Order.admissible_pi _ fun _ => Lean.Order.Option.admissible_eq_some _ _)
    (fun f hf b x h => by
      simp only at h
      split at h
      · cases h
      · rename_i e he; cases h; exact runPromised_error he
      · rename_i v hv; cases h; exact runPromised_ret hv
      · rename_i n hn; rw [runPromised_jump hn]; exact hf n x h)
  exact this b x h

/-- What `stay` ending says of `run`. -/
private def StayRun (step : β → Outcome (Next β ρ)) (b : β) : Outcome (Next β ρ) → Prop
  | none => run step b = none
  | some (.error e) => run step b = some (.error e)
  | some (.ok (.ret v)) => run step b = Outcome.ok v
  | some (.ok (.jump n)) => run step b = run step n

private theorem stayRun_of_jump {b n : β} {r : Outcome (Next β ρ)} (hb : run step b = run step n)
    (h : StayRun step n r) : StayRun step b r := by
  match r, h with
  | none, h => exact hb.trans h
  | some (.error _), h => exact hb.trans h
  | some (.ok (.ret _)), h => exact hb.trans h
  | some (.ok (.jump _)), h => exact hb.trans h

private theorem run_jump' {b n : β} (h : step b = jump n) : run step b = run step n := by
  rw [run, h]; rfl

private theorem stay_run {b : β} {r : Outcome (Next β ρ)} (h : stay p step b = some r) : StayRun step b r := by
  have := stay.fixpoint_induct p step (fun f => ∀ b r, f b = some r → StayRun step b r)
    (Lean.Order.admissible_pi_apply _ fun _ =>
      Lean.Order.admissible_pi _ fun _ => Lean.Order.Option.admissible_eq_some _ _)
    (fun f hf b r h => by
      simp only at h
      cases hs : step b with
      | none => rw [hs] at h; cases h; show run step b = none; rw [run, hs]
      | some s =>
        cases s with
        | error e => rw [hs] at h; cases h; show run step b = some (.error e); rw [run, hs]
        | ok nx =>
          cases nx with
          | ret v => rw [hs] at h; cases h; show run step b = Outcome.ok v; rw [run, hs]; rfl
          | jump n =>
            rw [hs] at h
            have hb := run_jump' (step := step) hs
            simp only at h
            split at h
            · exact stayRun_of_jump hb (hf n r h)
            · cases h; exact hb)
  exact this b r h

/-- A run that finishes doesn't stay among blocks `p` holds of for good. -/
private theorem stay_ne_none {b : β} {x : Except Stop ρ} (h : run step b = some x) : stay p step b ≠ none := by
  have := run.fixpoint_induct step (fun f => ∀ b x, f b = some x → stay p step b ≠ none)
    (Lean.Order.admissible_pi_apply _ fun _ =>
      Lean.Order.admissible_pi _ fun _ => Lean.Order.Option.admissible_eq_some _ _)
    (fun f hf b x h => by
      simp only at h
      split at h
      · cases h
      · rename_i e he
        rw [stay_of_not_jump (by intro n hn; rw [he] at hn; cases hn)]; nofun
      · rename_i v hv
        rw [stay_of_not_jump (by intro n hn; rw [hv] at hn; cases hn)]; nofun
      · rename_i n hn
        rw [stay_jump hn]
        split
        · exact hf n x h
        · nofun)
  exact this b x h

/-- Emitted code's form of a run under a promise is `runPromised`. -/
theorem promised_run (b : β) :
    promised (run step b) (fun _ => runPromised p step b) = runPromised p step b := by
  cases h : run step b with
  | none => rfl
  | some x => exact (runPromised_of_run h).symm

end Lemmas

/-! ### Laws

What a run under a promise is undefined for, and nothing else. These pin the choice `runPromised` makes for a run that
stays among promised blocks for good, so a change to it fails here first. `tests/refine.sh` drops this section from
the copy it mutates, so its mutant can show the cases it guards stop too. -/

section Laws
variable {β ρ : Type} {p : β → Bool} {step : β → Outcome (Next β ρ)}

/-- The same, under a promise: the run breaks it. -/
theorem runPromised_forever (I : β → Prop) (hI : ∀ b, I b → ∃ n, step b = jump n ∧ p n ∧ I n) {b : β}
    (hb : I b) : runPromised p step b = Outcome.ub .noProgress := by
  rw [runPromised, stay_forever I hI hb]

/-- A run that finishes under `runPromised` finishes the same way under `run`, unless it broke the promise. -/
theorem run_of_runPromised {b : β} {x : Except Stop ρ} (h : runPromised p step b = some x) :
    run step b = some x ∨ (run step b = none ∧ x = .error (.undefined .noProgress)) := by
  have := runPromised.fixpoint_induct p step
    (fun f => ∀ b x, f b = some x → run step b = some x ∨ (run step b = none ∧ x = .error (.undefined .noProgress)))
    (Lean.Order.admissible_pi_apply _ fun _ =>
      Lean.Order.admissible_pi _ fun _ => Lean.Order.Option.admissible_eq_some _ _)
    (fun f hf b x h => by
      simp only at h
      split at h
      · rename_i hs
        cases h
        right
        refine ⟨?_, rfl⟩
        cases hr : run step b with
        | none => rfl
        | some y => exact absurd hs (stay_ne_none hr)
      · cases h
      · rename_i e hs; cases h; exact .inl (stay_run hs)
      · rename_i v hs; cases h; exact .inl (stay_run hs)
      · rename_i n hs
        have hb : run step b = run step n := stay_run hs
        rw [hb]
        exact hf n x h)
  exact this b x h

/-- A run that never finishes under a promise either breaks it, or waits on a call LangRef allows never to return, or
keeps coming back to blocks `p` doesn't hold of. Nothing else. -/
theorem runPromised_of_run_none {b : β} (h : run step b = none) :
    runPromised p step b = none ∨ runPromised p step b = Outcome.ub .noProgress := by
  cases hr : runPromised p step b with
  | none => exact .inl rfl
  | some x =>
    rcases run_of_runPromised hr with h' | ⟨_, hx⟩
    · rw [h] at h'; cases h'
    · exact .inr (by rw [hx]; rfl)

end Laws

end IRLean
