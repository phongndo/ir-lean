import drop_nuw_promised_ir

/-! The cut lemma under a promise to progress, `IRLean/CutPromised.lean`, on what ir-lean emits:
`tests/cut/drop_nuw_promised.ll` is `drop_nuw_loop.ll` with each loop marked `llvm.loop.mustprogress`, as clang marks
a C loop, so the emitter runs both under `runPromised`. The proof is `CutCases.drop_nuw_loop`'s, and one fact more:
the two loops' blocks are under the promise together. -/

open IRLean

namespace CutPromisedCases

open drop_nuw_promised_ir

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

theorem cut_tgt_mono (x y : Val 8) (h : Refine.le x y) : Outcome.Sim Refine.le (cut_tgt x) (cut_tgt y) := by
  rw [show cut_tgt x = Outcome.ok _ from run_ret _ rfl, show cut_tgt y = Outcome.ok _ from run_ret _ rfl]
  refine Outcome.Sim.ok ?_
  refine_mono

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

/-- Related blocks are under the promise together: the same blocks of the same loop. -/
theorem promise_eq (b : src.Block) (b' : tgt.Block) (h : R b b') : tgt.promise b' = src.promise b := by
  match b, b', h with
  | .entry .., .entry .., _ => rfl
  | .head .., .head .., _ => rfl
  | .body .., .body .., _ => rfl
  | .exit .., .exit .., _ => rfl

theorem src_answers (a n : Val 8) (s : ModelStop) : src a n ≠ Outcome.stop s := by
  refine runPromised_ne_stop (fun b s => ?_) _ s
  match b with
  | .entry .. => exact jump_ne_stop _ s
  | .head .. => exact br_ne_stop _ _ _ s
  | .body n i acc =>
    rw [src_body]
    refine andThen_ne_stop ?_ fun y => andThen_ne_stop ?_ fun _ => jump_ne_stop _ s
    · rw [show cut_src acc = Outcome.ok _ from run_ret _ rfl]; nofun
    · exact fun h => Refine.outcome_stop s _ (h ▸ Mono.udiv (Refine.refl_val y) (Refine.refl_val _))
  | .exit .. => exact ret_ne_stop _ s

/-- The loop with `add` refines the loop with `add nuw`, both under `llvm.loop.mustprogress`. -/
theorem drop_nuw_promised : Refines src tgt := fun a n =>
  Refine.le_of_sim (Outcome.Sim.promised step_sim promise_eq ⟨Refine.refl_val a, Refine.refl_val n⟩)
    (src_answers a n)

/-! ### What the lemma needs -/

/-- A loop that never ends: one block, which jumps to itself. -/
def spin : Unit → Outcome (Next Unit (Val 8)) := fun _ => jump ()

/-- **The two sides have to be under the promise together,** `Outcome.Sim.promised`'s second hypothesis. The same
loop, in step with itself, under no promise in the source and under one in the target: the source never finishes,
which allows only a run that never finishes, and the target breaks its promise, which is undefined. So adding a
promise isn't a refinement, and the lemma doesn't let it through. -/
theorem promise_has_to_agree :
    ¬ Outcome.Sim Refine.le (runPromised (fun _ => false) spin ()) (runPromised (fun _ => true) spin ()) := by
  have hs : runPromised (fun _ => false) spin () = none := by
    have := runPromised.fixpoint_induct (fun _ => false) spin (fun f => ∀ b, f b = none)
      (Lean.Order.admissible_pi_apply (fun _ (r : Outcome (Val 8)) => r = none) fun _ =>
        Lean.Order.admissible_flatOrder _ rfl)
      (fun f hf b => by
        have hst : stay (fun _ => false) spin b = some (jump ()) :=
          stay_jump (p := fun _ => false) (step := spin) (b := b) (n := ()) rfl
        simp only [hst, jump, Outcome.ok]
        exact hf ())
    exact this ()
  have ht : runPromised (fun _ => true) spin () = Outcome.ub .noProgress :=
    runPromised_forever (fun _ => True) (fun _ _ => ⟨(), rfl, rfl, trivial⟩) trivial
  rw [hs, ht]
  intro h
  cases h

end CutPromisedCases
