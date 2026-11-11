import IRLean.Cut

/-! # The cut lemma, under a promise to progress

`IRLean/Cut.lean`'s `Outcome.Sim.run` is for a function the emitter runs with `run`. A function marked `mustprogress`,
or with a loop marked `llvm.loop.mustprogress`, which is what clang makes of a C loop, runs as
`promised (run step b) fun _ => runPromised p step b`: a run that stays for good among the blocks `p` holds of breaks
the promise, and is undefined. `Outcome.Sim.promised` is the lemma for two such functions: related blocks step to
related blocks, and are under the promise on both sides or on neither.

It needs that second fact because of the one run a promise changes. A source that never finishes without breaking
its promise allows only a target that never finishes, and a target that broke its promise there would be undefined
instead. In step, and under the promise together, it can't: `runPromised_noProgress`.

`Outcome.Sim.promised_dropped` is for a target without the promise, which needs nothing more than `run`'s lemma. A
target that adds one isn't covered, and isn't right.

This is its own module because it uses `IRLean/Promise.lean`'s laws, which `tests/refine.sh` leaves out of the copy of
the model it changes, and that copy has `IRLean/Cut.lean`. -/

namespace IRLean

section Promised

variable {β β' ρ ρ' : Type}

/-- `stay`, for at most `n` blocks: `none` if it needs more. -/
def stayFuel (p : β → Bool) (step : β → Outcome (Next β ρ)) : Nat → β → Option (Outcome (Next β ρ))
  | 0, _ => none
  | k + 1, b =>
    match step b with
    | some (.ok (.jump n)) => if p n then stayFuel p step k n else some (jump n)
    | r => some r

theorem stay_of_stayFuel {p : β → Bool} {step : β → Outcome (Next β ρ)} {k : Nat} {b : β}
    {o : Outcome (Next β ρ)} (h : stayFuel p step k b = some o) : stay p step b = some o := by
  induction k generalizing b with
  | zero => cases h
  | succ k ih =>
    rw [stay]
    simp only [stayFuel] at h
    split at h
    · rename_i n hn
      rw [hn]
      simp only
      split at h
      · rename_i hp; simp only [hp, ite_true]; exact ih h
      · rename_i hp; simp only [hp]; exact h
    · rename_i hne
      split
      · rename_i n hn; exact absurd hn (hne n)
      · exact h

theorem stayFuel_of_stay {p : β → Bool} {step : β → Outcome (Next β ρ)} {b : β} {o : Outcome (Next β ρ)}
    (h : stay p step b = some o) : ∃ k, stayFuel p step k b = some o := by
  have := stay.fixpoint_induct p step (fun f => ∀ b o, f b = some o → ∃ k, stayFuel p step k b = some o)
    (Lean.Order.admissible_pi_apply _ fun _ =>
      Lean.Order.admissible_pi _ fun _ => Lean.Order.Option.admissible_eq_some _ _)
    (fun f hf b o h => by
      simp only at h
      split at h
      · rename_i n hn
        split at h
        · rename_i hp
          obtain ⟨k, hk⟩ := hf n o h
          exact ⟨k + 1, by simp only [stayFuel, hn, hp, ite_true]; exact hk⟩
        · rename_i hp
          exact ⟨1, by simp only [stayFuel, hn, hp]; exact h⟩
      · rename_i hne
        refine ⟨1, ?_⟩
        simp only [stayFuel]
        exact h)
  exact this b o h

/-- Two functions' blocks in lockstep while they stay among promised blocks, for `k` blocks. -/
private theorem stayFuel_sim {R : β → β' → Prop} {r : ρ → ρ' → Prop} {p : β → Bool} {p' : β' → Bool}
    {step : β → Outcome (Next β ρ)} {step' : β' → Outcome (Next β' ρ')}
    (h : ∀ b b', R b b' → Outcome.Sim (Next.Rel R r) (step b) (step' b')) (hp : ∀ b b', R b b' → p' b' = p b)
    (k : Nat) {b : β} {b' : β'} (hb : R b b') :
    match stayFuel p step k b with
    | none => stayFuel p' step' k b' = none
    | some none => stayFuel p' step' k b' = some none
    | some (some (.error _)) => True
    | some (some (.ok nx)) => ∃ nx', stayFuel p' step' k b' = some (Outcome.ok nx') ∧ Next.Rel R r nx nx' := by
  induction k generalizing b b' with
  | zero => rfl
  | succ k ih =>
    have hs := h b b' hb
    simp only [stayFuel]
    match hsb : step b, hs with
    | none, hs =>
      have hs' : step' b' = none := hs
      simp only [hs']
    | some (.error _), _ => trivial
    | some (.ok (.ret x)), ⟨y, hy, hxy⟩ =>
      match y, hxy with
      | .ret y, hxy => simp only [hy]; exact ⟨.ret y, rfl, hxy⟩
    | some (.ok (.jump nx)), ⟨y, hy, hxy⟩ =>
      match y, hxy with
      | .jump ny, hxy =>
        have hxy : R nx ny := hxy
        simp only [hy, hp nx ny hxy]
        by_cases hpn : p nx = true
        · simp only [hpn, ite_true]; exact ih hxy
        · simp only [hpn, Bool.false_eq_true, ite_false]; exact ⟨.jump ny, rfl, hxy⟩

/-- The same, for `stay`: where the source stays among promised blocks for good, so does the target. -/
theorem stay_sim {R : β → β' → Prop} {r : ρ → ρ' → Prop} {p : β → Bool} {p' : β' → Bool}
    {step : β → Outcome (Next β ρ)} {step' : β' → Outcome (Next β' ρ')}
    (h : ∀ b b', R b b' → Outcome.Sim (Next.Rel R r) (step b) (step' b')) (hp : ∀ b b', R b b' → p' b' = p b)
    {b : β} {b' : β'} (hb : R b b') :
    match stay p step b with
    | none => stay p' step' b' = none
    | some none => stay p' step' b' = some none
    | some (some (.error _)) => True
    | some (some (.ok nx)) => ∃ nx', stay p' step' b' = some (Outcome.ok nx') ∧ Next.Rel R r nx nx' := by
  match hst : stay p step b with
  | some o =>
    obtain ⟨k, hk⟩ := stayFuel_of_stay hst
    have hsim := stayFuel_sim h hp k hb
    rw [hk] at hsim
    match o, hsim with
    | none, hsim => exact stay_of_stayFuel hsim
    | some (.error _), _ => trivial
    | some (.ok nx), ⟨nx', hnx, hrel⟩ => exact ⟨nx', stay_of_stayFuel hnx, hrel⟩
  | none =>
    show stay p' step' b' = none
    match hst' : stay p' step' b' with
    | none => rfl
    | some o' =>
      obtain ⟨k, hk⟩ := stayFuel_of_stay hst'
      have hsim := stayFuel_sim h hp k hb
      match hf : stayFuel p step k b, hsim with
      | none, hsim => rw [hk] at hsim; cases hsim
      | some o, _ => rw [stay_of_stayFuel hf] at hst; cases hst

/-- A target that breaks its promise is in step only with a source that has no result. -/
private theorem runPromised_noProgress {R : β → β' → Prop} {r : ρ → ρ' → Prop} {p : β → Bool} {p' : β' → Bool}
    {step : β → Outcome (Next β ρ)} {step' : β' → Outcome (Next β' ρ')}
    (h : ∀ b b', R b b' → Outcome.Sim (Next.Rel R r) (step b) (step' b')) (hp : ∀ b b', R b b' → p' b' = p b)
    {b' : β'} (hrp : runPromised p' step' b' = Outcome.ub .noProgress) {b : β} (hb : R b b') :
    ∃ e, runPromised p step b = some (.error e) := by
  have := runPromised.fixpoint_induct p' step'
    (fun f => ∀ b' x, f b' = some x → x = .error (.undefined .noProgress) →
      ∀ b, R b b' → ∃ e, runPromised p step b = some (.error e))
    (Lean.Order.admissible_pi_apply _ fun _ =>
      Lean.Order.admissible_pi _ fun _ => Lean.Order.Option.admissible_eq_some _ _)
    (fun f hf b' x hx hnp b hb => by
      have hsim := stay_sim h hp hb
      simp only at hx
      match hs : stay p step b, hsim with
      | none, _ => exact ⟨_, by rw [runPromised, hs]; rfl⟩
      | some none, hsim => rw [hsim] at hx; cases hx
      | some (some (.error e)), _ => exact ⟨e, by rw [runPromised, hs]⟩
      | some (some (.ok (.ret v))), ⟨nx', hnx, hrel⟩ =>
        match nx', hrel with
        | .ret v', _ =>
          rw [hnx] at hx
          subst hnp
          cases hx
      | some (some (.ok (.jump n))), ⟨nx', hnx, hrel⟩ =>
        match nx', hrel with
        | .jump n', hrel =>
          rw [hnx] at hx
          obtain ⟨e, he⟩ := hf n' x hx hnp n hrel
          exact ⟨e, by rw [runPromised, hs]; exact he⟩)
  exact this b' _ hrp rfl b hb

/-- **The cut lemma, between blocks, under a promise to progress.** As `Outcome.Sim.run`, for two functions whose
runs are under a promise: related blocks step to related blocks, and are under the promise on both sides or on
neither. A source that stays among promised blocks for good is undefined, and allows anything. One that never
finishes without breaking its promise allows only a target that does the same. -/
theorem Outcome.Sim.runPromised {R : β → β' → Prop} {r : ρ → ρ' → Prop} {p : β → Bool} {p' : β' → Bool}
    {step : β → Outcome (Next β ρ)} {step' : β' → Outcome (Next β' ρ')}
    (h : ∀ b b', R b b' → Outcome.Sim (Next.Rel R r) (step b) (step' b')) (hp : ∀ b b', R b b' → p' b' = p b)
    {b : β} {b' : β'} (hb : R b b') :
    Outcome.Sim r (IRLean.runPromised p step b) (IRLean.runPromised p' step' b') := by
  match hrp : IRLean.runPromised p step b with
  | some (.error _) => trivial
  | some (.ok x) =>
    rcases run_of_runPromised hrp with hr | ⟨_, hx⟩
    · have hsim := Outcome.Sim.run h hb
      rw [hr] at hsim
      obtain ⟨y, hy, hxy⟩ := hsim
      exact ⟨y, runPromised_of_run hy, hxy⟩
    · cases hx
  | none =>
    show IRLean.runPromised p' step' b' = none
    have hr : IRLean.run step b = none := by
      cases hr : IRLean.run step b with
      | none => rfl
      | some x => rw [runPromised_of_run hr] at hrp; cases hrp
    have hr' : IRLean.run step' b' = none := by
      have hsim := Outcome.Sim.run h hb
      rw [hr] at hsim
      exact hsim
    rcases runPromised_of_run_none (p := p') hr' with h' | h'
    · exact h'
    · obtain ⟨e, he⟩ := runPromised_noProgress h hp h' hb
      rw [hrp] at he
      cases he

/-- The same, as the emitter prints a run under a promise. -/
theorem Outcome.Sim.promised {R : β → β' → Prop} {r : ρ → ρ' → Prop} {p : β → Bool} {p' : β' → Bool}
    {step : β → Outcome (Next β ρ)} {step' : β' → Outcome (Next β' ρ')}
    (h : ∀ b b', R b b' → Outcome.Sim (Next.Rel R r) (step b) (step' b')) (hp : ∀ b b', R b b' → p' b' = p b)
    {b : β} {b' : β'} (hb : R b b') :
    Outcome.Sim r (IRLean.promised (IRLean.run step b) fun _ => IRLean.runPromised p step b)
      (IRLean.promised (IRLean.run step' b') fun _ => IRLean.runPromised p' step' b') := by
  rw [promised_run, promised_run]
  exact Outcome.Sim.runPromised h hp hb

/-- A target that drops the promise: where the source's run under it is undefined, anything is allowed, and
otherwise the two are `run`'s. Adding a promise isn't here, and isn't right: a target that stays in a loop for good
would be undefined where its source never finishes. -/
theorem Outcome.Sim.promised_dropped {R : β → β' → Prop} {r : ρ → ρ' → Prop} {p : β → Bool}
    {step : β → Outcome (Next β ρ)} {step' : β' → Outcome (Next β' ρ')}
    (h : ∀ b b', R b b' → Outcome.Sim (Next.Rel R r) (step b) (step' b')) {b : β} {b' : β'} (hb : R b b') :
    Outcome.Sim r (IRLean.promised (IRLean.run step b) fun _ => IRLean.runPromised p step b)
      (IRLean.run step' b') := by
  rw [promised_run]
  have hsim := Outcome.Sim.run h hb
  match hrp : IRLean.runPromised p step b with
  | some (.error _) => trivial
  | some (.ok x) =>
    rcases run_of_runPromised hrp with hr | ⟨_, hx⟩
    · rw [hr] at hsim; exact hsim
    · cases hx
  | none =>
    have hr : IRLean.run step b = none := by
      cases hr : IRLean.run step b with
      | none => rfl
      | some x => rw [runPromised_of_run hr] at hrp; cases hrp
    rw [hr] at hsim
    exact hsim

/-- A run under a promise stops the model only where one of its blocks does. -/
theorem runPromised_ne_stop {p : β → Bool} {step : β → Outcome (Next β ρ)} (h : ∀ b s, step b ≠ Outcome.stop s)
    (b : β) (s : ModelStop) :
    IRLean.promised (IRLean.run step b) (fun _ => IRLean.runPromised p step b) ≠ Outcome.stop s := by
  rw [promised_run]
  intro hrp
  rcases run_of_runPromised hrp with hr | ⟨_, hx⟩
  · exact run_ne_stop h b s hr
  · cases hx

end Promised
end IRLean
