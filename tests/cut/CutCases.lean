import drop_nuw_loop_ir

/-! The cut lemma, `IRLean/Cut.lean`, on what ir-lean emits, and what it needs.

`drop_nuw_loop` is a cut that's refined and not equal, `add nuw` to `add`, inside a loop. `Q5Kernel.lean` is the other
use, where the cut's replacement is equal to it. The rest are the lemma's hypotheses, each with a case where the
conclusion is false without it, so none can be dropped.

`tests/cut.sh` builds this with warnings as errors, checks it rests on the standard axioms, replays it, and has Alive2
give `drop_nuw_loop`'s verdict too. -/

open IRLean

namespace CutCases

open drop_nuw_loop_ir

/-! ### A cut that's refined, in a loop -/

/-- The proof about the cut alone: `add nuw %x, 3` to `add %x, 3`. Where the sum wraps, the source's is poison. -/
theorem drop_nuw_cut : Refines cut_src cut_tgt := fun x => by
  rw [show cut_src x = Outcome.ok _ from run_ret _ rfl, show cut_tgt x = Outcome.ok _ from run_ret _ rfl,
    Refine.outcome_ok_ok]
  cases x with
  | none => exact Refine.val_none _
  | some x =>
    simp only [Val.add]
    split
    · exact Refine.val_none _
    · simp [Refine.val_some]

/-- The replacement keeps refinement of what it's given. -/
theorem cut_tgt_mono (x y : Val 8) (h : Refine.le x y) : Outcome.Sim Refine.le (cut_tgt x) (cut_tgt y) := by
  rw [show cut_tgt x = Outcome.ok _ from run_ret _ rfl, show cut_tgt y = Outcome.ok _ from run_ret _ rfl]
  refine Outcome.Sim.ok ?_
  refine_mono

/-- The source's loop body is the cut and then the rest of the round, as written. -/
theorem src_body (n i acc : Val 8) :
    src.step (.body n i acc) =
      andThen (cut_src acc) fun y =>
        andThen (Val.udiv y (some 3#8)) fun d => jump (.head (Val.add i (some 1#8)) (Val.xor d i) n) := by
  rw [show cut_src acc = Outcome.ok _ from run_ret _ rfl]
  simp only [src.step, andThen_ok]

theorem tgt_body (n i acc : Val 8) :
    tgt.step (.body n i acc) =
      andThen (cut_tgt acc) fun y =>
        andThen (Val.udiv y (some 3#8)) fun d => jump (.head (Val.add i (some 1#8)) (Val.xor d i) n) := by
  rw [show cut_tgt acc = Outcome.ok _ from run_ret _ rfl]
  simp only [tgt.step, andThen_ok]

/-- Blocks of the same name, with each live value in the target refining the source's. -/
def R : src.Block → tgt.Block → Prop
  | .entry a n, .entry a' n' => Refine.le a a' ∧ Refine.le n n'
  | .head i acc n, .head i' acc' n' => Refine.le i i' ∧ Refine.le acc acc' ∧ Refine.le n n'
  | .body n i acc, .body n' i' acc' => Refine.le n n' ∧ Refine.le i i' ∧ Refine.le acc acc'
  | .exit acc, .exit acc' => Refine.le acc acc'
  | _, _ => False

theorem step_sim (b : src.Block) (b' : tgt.Block) (h : R b b') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step b) (tgt.step b') := by
  match b, b', h with
  | .entry a n, .entry a' n', ⟨ha, hn⟩ => exact Outcome.Sim.jump ⟨Refine.refl_val _, ha, hn⟩
  | .head i acc n, .head i' acc' n', ⟨hi, hacc, hn⟩ =>
    exact Outcome.Sim.br (Mono.icmpUlt hi hn) ⟨hn, hi, hacc⟩ hacc
  | .body n i acc, .body n' i' acc', ⟨hn, hi, hacc⟩ =>
    rw [src_body, tgt_body]
    refine Outcome.Sim.andThen (Refines.sim_cut drop_nuw_cut cut_tgt_mono hacc) fun y y' hy => ?_
    refine Outcome.Sim.andThen (Refine.sim_of_le (Mono.udiv hy (Refine.refl_val _))) fun d d' hd => ?_
    refine Outcome.Sim.jump ⟨?_, ?_, hn⟩ <;> refine_mono
  | .exit acc, .exit acc', hacc => exact Outcome.Sim.ret hacc

theorem src_answers (a n : Val 8) (s : ModelStop) : src a n ≠ Outcome.stop s := by
  refine run_ne_stop (fun b s => ?_) _ s
  match b with
  | .entry .. => exact jump_ne_stop _ s
  | .head .. => exact br_ne_stop _ _ _ s
  | .body n i acc =>
    rw [src_body]
    refine andThen_ne_stop ?_ fun y => andThen_ne_stop ?_ fun _ => jump_ne_stop _ s
    · rw [show cut_src acc = Outcome.ok _ from run_ret _ rfl]; nofun
    · exact fun h => Refine.outcome_stop s _ (h ▸ Mono.udiv (Refine.refl_val y) (Refine.refl_val _))
  | .exit .. => exact ret_ne_stop _ s

/-- The loop with `add` refines the loop with `add nuw`: the cut's proof, and the cut lemma. -/
theorem drop_nuw_loop : Refines src tgt := fun a n =>
  Refine.le_of_sim (Outcome.Sim.run step_sim ⟨Refine.refl_val a, Refine.refl_val n⟩) (src_answers a n)

/-- And not the other way: from 253, one round wraps, so the loop with `add nuw` returns poison where the one with
`add` returns 0. The lemma is one-way, as the cut's proof is. -/
theorem drop_nuw_loop_converse : ¬ Refines tgt src := fun h => by
  have h := h (some 253#8) (some 1#8)
  have ht : tgt (some 253#8) (some 1#8) = Outcome.ok (some 0#8) := by
    unfold tgt
    rw [run_jump _ (by rfl), run_jump _ (b' := .body (some 1#8) (some 0#8) (some 253#8)) (by rfl),
      run_jump _ (b' := .head (some 1#8) (some 0#8) (some 1#8)) (by rfl),
      run_jump _ (b' := .exit (some 0#8)) (by rfl), run_ret _ (by rfl)]
  have hs : src (some 253#8) (some 1#8) = Outcome.ok none := by
    unfold src
    rw [run_jump _ (by rfl), run_jump _ (b' := .body (some 1#8) (some 0#8) (some 253#8)) (by rfl),
      run_jump _ (b' := .head (some 1#8) none (some 1#8)) (by rfl),
      run_jump _ (b' := .exit none) (by rfl), run_ret _ (by rfl)]
  rw [ht, hs, Refine.outcome_ok_ok, Refine.val_some] at h
  cases h

/-! ### What the lemma needs

Each hypothesis, with a case where the conclusion fails without it. -/

/-- **The rest of the function has to keep refinement,** and the same code on both sides doesn't always. Here it's
what the emitter prints for `returned` on an integer argument, which stops the model when the result isn't that
argument: the cut gives poison, its replacement gives 1, which refines it, and the argument is poison. The source
returns, and the target stops the model. -/
theorem rest_has_to_keep_refinement :
    ∃ (c c' : Outcome (Val 8)) (k : Val 8 → Outcome (Val 8)),
      Refine.le c c' ∧ ¬ Outcome.Sim Refine.le (andThen c k) (andThen c' k) :=
  ⟨Outcome.ok none, Outcome.ok (some 1#8), fun y => Mem.returnedInt (none : Val 8) y (Outcome.ok y),
    (Refine.outcome_ok_ok _ _).2 (Refine.val_none _), fun ⟨_, h, _⟩ => by cases h⟩

/-- A cut that's poison on poison, and undefined on a value. -/
def undefinedOnValue (x : Val 8) : Outcome (Val 8) :=
  match x with
  | none => Outcome.ok none
  | some _ => Outcome.ub .unreachable

/-- A replacement that's poison on poison, and stops the model on a value: `returned`, as above. -/
def stopsOnValue (y : Val 8) : Outcome (Val 8) := Mem.returnedInt (none : Val 8) y (Outcome.ok y)

/-- **The replacement has to keep refinement of its inputs,** `Refines.sim_cut`'s second hypothesis. A cut's proof is
at one input for both, and in the function the replacement gets a value where the cut got poison. Here the
replacement refines the cut at every input, and still isn't allowed at 1 where the cut got poison. -/
theorem replacement_has_to_keep_refinement :
    Refines undefinedOnValue stopsOnValue ∧ Refine.le (none : Val 8) (some 1#8) ∧
      ¬ Outcome.Sim Refine.le (undefinedOnValue none) (stopsOnValue (some 1#8)) := by
  refine ⟨fun x => ?_, Refine.val_none _, fun ⟨_, h, _⟩ => ?_⟩
  · cases x with
    | none => exact (Refine.outcome_ok_ok _ _).2 (Refine.val_none _)
    | some _ => exact Refine.outcome_ub _ _
  · cases h

/-- **The source has to have an answer.** `Outcome.Sim` lets a source that stops the model allow anything, and
`Refine.le` lets it allow nothing, so a whole function's claim needs `Refines.of_sim`'s second hypothesis, or says
`Outcome.answered`. -/
theorem source_has_to_answer :
    Outcome.Sim Refine.le (Outcome.stop .unknownCallee : Outcome (Val 8)) (Outcome.ok (some 1#8)) ∧
      ¬ Refine.le (Outcome.stop .unknownCallee : Outcome (Val 8)) (Outcome.ok (some 1#8)) ∧
      Refine.le (Outcome.answered (Outcome.stop .unknownCallee : Outcome (Val 8))) (Outcome.ok (some 1#8)) :=
  ⟨trivial, id, trivial⟩

/-- `Outcome.Sim` is `Refine.le` everywhere else: a result allows only a result that refines it, a run that never
finishes only another, and a target that stops the model is allowed only by a source with no answer. -/
theorem sim_is_strict :
    ¬ Outcome.Sim Refine.le (Outcome.ok (some 1#8)) (Outcome.ok (some 2#8)) ∧
      ¬ Outcome.Sim Refine.le (Outcome.ok (some 1#8)) (Outcome.ub .unreachable : Outcome (Val 8)) ∧
      ¬ Outcome.Sim Refine.le (none : Outcome (Val 8)) (Outcome.ok (some 1#8)) ∧
      ¬ Outcome.Sim Refine.le (Outcome.ok (some 1#8)) (none : Outcome (Val 8)) ∧
      ¬ Outcome.Sim Refine.le (Outcome.ok (none : Val 8)) (Outcome.stop .unknownCallee) := by
  refine ⟨fun ⟨_, h, hxy⟩ => ?_, fun ⟨_, h, _⟩ => ?_, fun h => ?_, fun ⟨_, h, _⟩ => ?_, fun ⟨_, h, _⟩ => ?_⟩
  · cases h; cases hxy
  · cases h
  · cases h
  · cases h
  · cases h

/-- The guard takes out only the inputs where the source stops the model: undefined behavior, a run that never
finishes and a result are what they were. -/
theorem answered_keeps_answers (x : Val 8) (u : UB) :
    Outcome.answered (Outcome.ok x) = Outcome.ok x ∧
      Outcome.answered (Outcome.ub u : Outcome (Val 8)) = Outcome.ub u ∧
      Outcome.answered (none : Outcome (Val 8)) = none :=
  ⟨rfl, rfl, rfl⟩

/-- **Blocks have to stay in step.** A target that takes a block more isn't related to the source block by block,
and needn't refine it: here every block of both returns or jumps, the source returns 0, and the target, which goes
through one more block, returns 1. -/
theorem blocks_have_to_stay_related :
    ∃ (step step' : Bool → Outcome (Next Bool (Val 8))),
      (∀ b, ∃ nx nx', step b = Outcome.ok nx ∧ step' b = Outcome.ok nx') ∧
        ¬ Outcome.Sim Refine.le (run step true) (run step' true) := by
  refine ⟨fun _ => ret (some 0#8), fun b => if b then jump false else ret (some 1#8), fun b => ?_, fun h => ?_⟩
  · cases b <;> exact ⟨_, _, rfl, rfl⟩
  · rw [run_ret _ (by rfl), run_jump _ (b' := false) (by rfl), run_ret _ (by rfl), Outcome.Sim.ok_iff] at h
    cases h

end CutCases
