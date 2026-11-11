import LlamaBitspread
import q5_kernel_ir

/-! The cut lemma, used once: a proof about a slice becomes a theorem about the function that holds it.

`tests/cut/q5_kernel.ll` is a loop whose body holds llama.cpp's q5_0 bit-spreading slice, word for word, and the same
loop with the slice's replacement. `LlamaBitspread.same`, in `tests/proofs/LlamaBitspread.lean`, is the proof about the
slice alone. `q5_kernel` is about the loops: the one with the replacement refines the one with the slice, on every
input, poison included. Nothing here looks inside the slice: `slice` is all it knows of it, so the kernel's proof is
the slice's proof and the cut lemma, `IRLean/Cut.lean`.

`tests/cut.sh` builds this against freshly generated modules, checks its axioms, replays it, and checks that a loop
whose replacement reads the wrong bit, and one that drops a round, stop it. -/

open IRLean

namespace Q5Kernel

open q5_kernel_ir

/-- What's proved of the cut: its replacement refines it. From `same`, which says more, that they're equal. -/
theorem slice : Refines LlamaBitspreadIR.src LlamaBitspreadIR.tgt := fun x => by
  obtain ⟨r, hs, ht⟩ := LlamaBitspread.same_successful x
  rw [hs, ht]
  exact (Refine.outcome_ok_ok r r).2 (Refine.Reflexive.refl r)

/-- The replacement keeps refinement of the word it's given. -/
theorem slice_mono (x y : Val 32) (h : Refine.le x y) :
    Outcome.Sim Refine.le (LlamaBitspreadIR.tgt x) (LlamaBitspreadIR.tgt y) := by
  rw [show LlamaBitspreadIR.tgt x = Outcome.ok _ from run_ret _ rfl,
    show LlamaBitspreadIR.tgt y = Outcome.ok _ from run_ret _ rfl]
  refine Outcome.Sim.ok ?_
  refine_mono

/-- The source's loop body is the cut, on the round's word, and then the rest of the round. The two sides are
compared as written, after unfolding the block and the slice, and not by computing them: a body that isn't the slice
and then this rest fails here, with an error and not a time limit. -/
theorem src_body (qh n : Val 32) (q : Vec 32 8) (i : Val 32) (acc : Vec 32 8) :
    src.step (.body qh n q i acc) =
      andThen (LlamaBitspreadIR.src (Val.add qh i)) fun out =>
        jump (.head (Val.add i (some 1#32))
          (Vec.map2 (fun a b => Val.add a b) acc (Vec.map2 (fun a b => Val.or a b) out q)) qh n q) := by
  rw [show LlamaBitspreadIR.src (Val.add qh i) = Outcome.ok _ from run_ret _ rfl]
  simp only [src.step, andThen_ok]

/-- The target's is the replacement, and then the same rest. -/
theorem tgt_body (qh n : Val 32) (q : Vec 32 8) (i : Val 32) (acc : Vec 32 8) :
    tgt.step (.body qh n q i acc) =
      andThen (LlamaBitspreadIR.tgt (Val.add qh i)) fun out =>
        jump (.head (Val.add i (some 1#32))
          (Vec.map2 (fun a b => Val.add a b) acc (Vec.map2 (fun a b => Val.or a b) out q)) qh n q) := by
  rw [show LlamaBitspreadIR.tgt (Val.add qh i) = Outcome.ok _ from run_ret _ rfl]
  simp only [tgt.step, andThen_ok]

/-- Which blocks of the two loops correspond: the ones of the same name, with each live value in the target refining
the source's. Not equal: from the second round on, the target's values come from the replacement. -/
def R : src.Block → tgt.Block → Prop
  | .entry qh n q, .entry qh' n' q' => Refine.le qh qh' ∧ Refine.le n n' ∧ Refine.le q q'
  | .head i acc qh n q, .head i' acc' qh' n' q' =>
    Refine.le i i' ∧ Refine.le acc acc' ∧ Refine.le qh qh' ∧ Refine.le n n' ∧ Refine.le q q'
  | .body qh n q i acc, .body qh' n' q' i' acc' =>
    Refine.le qh qh' ∧ Refine.le n n' ∧ Refine.le q q' ∧ Refine.le i i' ∧ Refine.le acc acc'
  | .exit acc, .exit acc' => Refine.le acc acc'
  | _, _ => False

/-- Related blocks step to related blocks. The body is the cut lemma inside a block: the cut, by `slice`, and the
instructions after it, which keep refinement. Every other block is the same code on both sides. -/
theorem step_sim (b : src.Block) (b' : tgt.Block) (h : R b b') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step b) (tgt.step b') := by
  match b, b', h with
  | .entry qh n q, .entry qh' n' q', ⟨hqh, hn, hq⟩ =>
    exact Outcome.Sim.jump ⟨Refine.refl_val _, Refine.Reflexive.refl _, hqh, hn, hq⟩
  | .head i acc qh n q, .head i' acc' qh' n' q', ⟨hi, hacc, hqh, hn, hq⟩ =>
    exact Outcome.Sim.br (Mono.icmpUlt hi hn) ⟨hqh, hn, hq, hi, hacc⟩ hacc
  | .body qh n q i acc, .body qh' n' q' i' acc', ⟨hqh, hn, hq, hi, hacc⟩ =>
    rw [src_body, tgt_body]
    refine Outcome.Sim.andThen (Refines.sim_cut slice slice_mono (Mono.add hqh hi)) fun out out' hout => ?_
    refine Outcome.Sim.jump ⟨?_, ?_, hqh, hn, hq⟩ <;> refine_mono
  | .exit acc, .exit acc', hacc => exact Outcome.Sim.ret hacc

/-- No block of the source stops the model, so its run doesn't. -/
theorem src_answers (qh n : Val 32) (q : Vec 32 8) (s : ModelStop) : src qh n q ≠ Outcome.stop s := by
  refine run_ne_stop (fun b s => ?_) _ s
  match b with
  | .entry .. => exact jump_ne_stop _ s
  | .head .. => exact br_ne_stop _ _ _ s
  | .body qh n q i acc =>
    rw [src_body]
    refine andThen_ne_stop ?_ fun _ => jump_ne_stop _ s
    rw [show LlamaBitspreadIR.src (Val.add qh i) = Outcome.ok _ from run_ret _ rfl]
    nofun
  | .exit .. => exact ret_ne_stop _ s

/-- **The loop with the replacement refines the loop with the slice,** on every input, poison included. -/
theorem q5_kernel : Refines src tgt := fun qh n q =>
  Refine.le_of_sim
    (Outcome.Sim.run step_sim ⟨Refine.refl_val qh, Refine.refl_val n, Refine.Reflexive.refl q⟩)
    (src_answers qh n q)

end Q5Kernel
