import MemoryC
import MemoryCExec

/-! Two functions of `tests/real/memory.c` agree whole with their copies on `ExecMem`: what
`docs/memory.md#why-a-test-on-execmem-is-a-test-of-mem` argues for every function, proved for these. `MemoryC` is what
`ir-lean` prints for it, and `MemoryCExec` what `ir-lean --executable-memory` prints, from clang's `-O2
-fno-strict-aliasing` output, as `tests/exec_memory.sh` makes them.

`sum_bytes` loads in a loop and `fill` stores in one, each under a call with promises, and each block's equation is
proved by the same `simp`, so the emitter could print these for any function like them. A function that binds a pair,
as a call, `alloca` or `malloc` does, or that switches, needs more than this `simp`. -/

open IRLean

namespace Link

/-- What the `simp` takes a block's equation apart with. -/
macro "agree_step" : tactic => `(tactic| (
  simp only [ExecMem.gep, ExecMem.loadInt, ExecMem.storeInt_agrees, Outcome.andThen_map, Outcome.map_andThen,
    map_br, map_jump, map_ret, map_assume]))

def sumBlock : MemoryCExec.sum_bytes.Block → MemoryC.sum_bytes.Block
  | .entry m p n => .entry m.toMem p n
  | .for_body_preheader m p n => .for_body_preheader m.toMem p n
  | .for_body_preheader_new m p n x => .for_body_preheader_new m.toMem p n x
  | .for_cond_cleanup_loopexit_unr_lcssa m p x a i => .for_cond_cleanup_loopexit_unr_lcssa m.toMem p x a i
  | .for_body_epil_preheader m i s p x => .for_body_epil_preheader m.toMem i s p x
  | .for_body_epil m i s e p x => .for_body_epil m.toMem i s e p x
  | .for_cond_cleanup m s => .for_cond_cleanup m.toMem s
  | .for_body m i s n p x u => .for_body m.toMem i s n p x u

theorem sum_bytes_step (b : MemoryCExec.sum_bytes.Block) :
    MemoryC.sum_bytes.step (sumBlock b) =
      Outcome.map (Next.map sumBlock ExecMem.out) (MemoryCExec.sum_bytes.step b) := by
  cases b <;> simp only [sumBlock, MemoryC.sum_bytes.step, MemoryCExec.sum_bytes.step] <;> agree_step <;> rfl

theorem sum_bytes_agrees (p : PtrVal) (n : Val 64) (x : ExecMem) :
    MemoryC.sum_bytes p n x.toMem = Outcome.map ExecMem.out (MemoryCExec.sum_bytes p n x) := by
  simp only [MemoryC.sum_bytes, MemoryCExec.sum_bytes, map_noundef]
  rcases p with _ | p
  · rfl
  rcases n with _ | n
  · rfl
  simp only [noundef]
  refine ExecMem.call_agrees _ _ _ _ _ fun y c => ?_
  exact promised_map (fun b => by cases b <;> rfl) sum_bytes_step (.entry y _ _)

def fillBlock : MemoryCExec.fill.Block → MemoryC.fill.Block
  | .entry m p n s => .entry m.toMem p n s
  | .for_body_preheader m p n s => .for_body_preheader m.toMem p n s
  | .for_body_preheader_new m p n s x => .for_body_preheader_new m.toMem p n s x
  | .for_cond_cleanup_loopexit_unr_lcssa m p x a i => .for_cond_cleanup_loopexit_unr_lcssa m.toMem p x a i
  | .for_body_epil_preheader m i s p x => .for_body_epil_preheader m.toMem i s p x
  | .for_body_epil m i s e p x => .for_body_epil m.toMem i s e p x
  | .for_cond_cleanup m => .for_cond_cleanup m.toMem
  | .for_body m i s n p x u => .for_body m.toMem i s n p x u

theorem fill_step (b : MemoryCExec.fill.Block) :
    MemoryC.fill.step (fillBlock b) = Outcome.map (Next.map fillBlock ExecMem.out) (MemoryCExec.fill.step b) := by
  cases b <;> simp only [fillBlock, MemoryC.fill.step, MemoryCExec.fill.step] <;> agree_step <;> rfl

theorem fill_agrees (p : PtrVal) (n : Val 64) (seed : Val 32) (x : ExecMem) :
    MemoryC.fill p n seed x.toMem = Outcome.map ExecMem.out (MemoryCExec.fill p n seed x) := by
  simp only [MemoryC.fill, MemoryCExec.fill, map_noundef]
  rcases p with _ | p
  · rfl
  rcases n with _ | n
  · rfl
  rcases seed with _ | seed
  · rfl
  simp only [noundef]
  refine ExecMem.call_agrees _ _ _ _ _ fun y c => ?_
  exact promised_map (fun b => by cases b <;> rfl) fill_step (.entry y _ _ _)

end Link
