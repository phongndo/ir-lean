import Q5Kernel
import q5_kernel_memory_ir

/-! The cut lemma on a function with memory. `tests/cut/q5_kernel_memory.ll` is `q5_kernel.ll`'s loop with memory: it
loads each round's word through a pointer, runs llama.cpp's q5_0 bit-spreading slice on it, and stores what it adds
up through another. `q5_kernel_memory` proves the loop with the slice's replacement refines it, on every memory the
model has an answer for, from the slice's proof, `Q5Kernel.slice`, and nothing else about the slice.

The cut doesn't touch memory, so the two loops run on the same memory until the store at the end, and the blocks are
related with the memory equal: a load is then the same load on both sides. The store is of what the rounds added up,
which the target's refines, so the memories the two leave are related by `Mem.le`, and needn't be equal. -/

open IRLean

namespace Q5KernelMemory

open q5_kernel_memory_ir

/-- The source's loop body: the round's word is loaded, then the cut, then the rest of the round. As written, so a
body that isn't this fails here. -/
theorem src_body (m : Mem) (dst qh : PtrVal) (n i : Val 32) (acc : Vec 32 8) :
    src.step (.body m dst qh n i acc) =
      andThen (Mem.loadInt 32 m (Mem.gep m qh (Val.mul (Val.zext 64 i) (some 4#64) (nsw := true)) (inbounds := true))
        4) fun x =>
      andThen (LlamaBitspreadIR.src x) fun out =>
        jump (.head m (Val.add i (some 1#32)) (Vec.map2 (fun a b => Val.add a b) acc out) dst qh n) := by
  have hs : ∀ x, LlamaBitspreadIR.src x = Outcome.ok _ := fun x => run_ret _ rfl
  simp only [src.step, hs, andThen_ok]

theorem tgt_body (m : Mem) (dst qh : PtrVal) (n i : Val 32) (acc : Vec 32 8) :
    tgt.step (.body m dst qh n i acc) =
      andThen (Mem.loadInt 32 m (Mem.gep m qh (Val.mul (Val.zext 64 i) (some 4#64) (nsw := true)) (inbounds := true))
        4) fun x =>
      andThen (LlamaBitspreadIR.tgt x) fun out =>
        jump (.head m (Val.add i (some 1#32)) (Vec.map2 (fun a b => Val.add a b) acc out) dst qh n) := by
  have ht : ∀ x, LlamaBitspreadIR.tgt x = Outcome.ok _ := fun x => run_ret _ rfl
  simp only [tgt.step, ht, andThen_ok]

/-- Blocks of the same name, on the same memory, with each live value in the target refining the source's. -/
def R : src.Block → tgt.Block → Prop
  | .entry m dst qh n, .entry m' dst' qh' n' => m' = m ∧ Refine.le dst dst' ∧ Refine.le qh qh' ∧ Refine.le n n'
  | .head m i acc dst qh n, .head m' i' acc' dst' qh' n' =>
    m' = m ∧ Refine.le i i' ∧ Refine.le acc acc' ∧ Refine.le dst dst' ∧ Refine.le qh qh' ∧ Refine.le n n'
  | .body m dst qh n i acc, .body m' dst' qh' n' i' acc' =>
    m' = m ∧ Refine.le dst dst' ∧ Refine.le qh qh' ∧ Refine.le n n' ∧ Refine.le i i' ∧ Refine.le acc acc'
  | .exit m dst acc, .exit m' dst' acc' => m' = m ∧ Refine.le dst dst' ∧ Refine.le acc acc'
  | _, _ => False

/-- Related blocks step to related blocks, or return related results. The body is the cut lemma inside a block: the
load, on the same memory, the cut, by `Q5Kernel.slice`, and the instructions after it. The last block's store keeps
`Mem.le`. -/
theorem step_sim (b : src.Block) (b' : tgt.Block) (h : R b b') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step b) (tgt.step b') := by
  match b, b', h with
  | .entry m dst qh n, .entry _ dst' qh' n', ⟨rfl, hdst, hqh, hn⟩ =>
    exact Outcome.Sim.jump ⟨rfl, Refine.refl_val _, Refine.Reflexive.refl _, hdst, hqh, hn⟩
  | .head m i acc dst qh n, .head _ i' acc' dst' qh' n', ⟨rfl, hi, hacc, hdst, hqh, hn⟩ =>
    exact Outcome.Sim.br (Mono.icmpUlt hi hn) ⟨rfl, hdst, hqh, hn, hi, hacc⟩ ⟨rfl, hdst, hacc⟩
  | .body m dst qh n i acc, .body _ dst' qh' n' i' acc', ⟨rfl, hdst, hqh, hn, hi, hacc⟩ =>
    rw [src_body, tgt_body]
    refine Outcome.Sim.andThen (Mono.loadInt m (Mono.gep m hqh (by refine_mono)) 32 4) fun x x' hx => ?_
    refine Outcome.Sim.andThen (Refines.sim_cut Q5Kernel.slice Q5Kernel.slice_mono hx) fun out out' hout => ?_
    refine Outcome.Sim.jump ⟨rfl, ?_, ?_, hdst, hqh, hn⟩ <;> refine_mono
  | .exit m dst acc, .exit _ dst' acc', ⟨rfl, hdst, hacc⟩ =>
    simp only [src.step, tgt.step]
    exact Outcome.Sim.andThen ((Mem.le.refl m).storeVec hdst hacc 1) fun m₁ m₂ hm => Outcome.Sim.ret ⟨trivial, hm⟩

/-- **The loop with the replacement refines the loop with the slice,** for every pointer and count, poison included,
on every memory the model has an answer for. -/
theorem q5_kernel_memory : Refines (fun dst qh n m => (src dst qh n m).answered) tgt := fun dst qh n _ =>
  (Refine.answered_iff _ _).2
    (Outcome.Sim.run step_sim ⟨rfl, Refine.Reflexive.refl dst, Refine.Reflexive.refl qh, Refine.refl_val n⟩)

end Q5KernelMemory
