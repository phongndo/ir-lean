import clang_sum_ir

/-! The cut lemma on a function as clang compiled it. `tests/cut/clang_sum.ll`'s `@src` is clang's IR, at `-O1`, for
a C loop that adds up three times each word it loads: a function with `memory(argmem: read)`, a pointer argument
that's `readonly`, `nofree` and `captures(none)`, and a loop marked `llvm.loop.mustprogress`. `@tgt` is that function
with `mul %x, 3` replaced by `add (shl %x, 1), %x`. `clang_sum` proves it refines `@src`, on every memory the model
has an answer for, from the cut's proof, `cut`.

So this goes through everything the emitter wraps a compiled function in: `noundef` on the arguments, `Mem.call` for
the function's promises about memory, the tag on its pointer, and a run under a promise to progress. -/

open IRLean

namespace ClangSum

open clang_sum_ir

/-- The proof about the cut alone: three times a word is twice it, and it. -/
theorem cut : Refines cut_src cut_tgt := fun x => by
  rw [show cut_src x = Outcome.ok _ from run_ret _ rfl, show cut_tgt x = Outcome.ok _ from run_ret _ rfl,
    Refine.outcome_ok_ok]
  cases x with
  | none => exact Refine.val_none _
  | some x =>
    have h : x * 3#32 = (x <<< 1#32) + x := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq, Nat.reduceMod, Nat.reducePow]
      omega
    simp [Val.mul, Val.shl, Val.shiftOk, Val.add, Refine.val_some, h]

theorem cut_tgt_mono (x y : Val 32) (h : Refine.le x y) : Outcome.Sim Refine.le (cut_tgt x) (cut_tgt y) := by
  rw [show cut_tgt x = Outcome.ok _ from run_ret _ rfl, show cut_tgt y = Outcome.ok _ from run_ret _ rfl]
  refine Outcome.Sim.ok ?_
  refine_mono

/-- The loop's block is the load, the cut, and the rest of the round, as written. -/
theorem src_body (m : Mem) (v5 : Val 64) (v6 : Val 32) (a0 : PtrVal) (v3 : Val 64) :
    src.step (.bb4 m v5 v6 a0 v3) =
      andThen (Mem.loadInt 32 m
        (Mem.gep m a0 (Val.mul v5 (some 4#64) (nuw := true) (nsw := true)) (inbounds := true) (nuw := true)) 4)
        fun v8 =>
      andThen (cut_src v8) fun y =>
        br (Val.icmpEq (Val.add v5 (some 1#64) (nuw := true) (nsw := true)) v3) (.bb3 m (Val.add y v6))
          (.bb4 m (Val.add v5 (some 1#64) (nuw := true) (nsw := true)) (Val.add y v6) a0 v3) := by
  have hs : ∀ x, cut_src x = Outcome.ok _ := fun x => run_ret _ rfl
  simp only [src.step, hs, andThen_ok]

theorem tgt_body (m : Mem) (v5 : Val 64) (v6 : Val 32) (a0 : PtrVal) (v3 : Val 64) :
    tgt.step (.bb4 m v5 v6 a0 v3) =
      andThen (Mem.loadInt 32 m
        (Mem.gep m a0 (Val.mul v5 (some 4#64) (nuw := true) (nsw := true)) (inbounds := true) (nuw := true)) 4)
        fun v8 =>
      andThen (cut_tgt v8) fun y =>
        br (Val.icmpEq (Val.add v5 (some 1#64) (nuw := true) (nsw := true)) v3) (.bb3 m (Val.add y v6))
          (.bb4 m (Val.add v5 (some 1#64) (nuw := true) (nsw := true)) (Val.add y v6) a0 v3) := by
  have ht : ∀ x, cut_tgt x = Outcome.ok _ := fun x => run_ret _ rfl
  simp only [tgt.step, ht, andThen_ok]

/-- Blocks of the same number, on the same memory, with each live value in the target refining the source's. -/
def R : src.Block → tgt.Block → Prop
  | .bb1 m a0 a1, .bb1 m' a0' a1' => m' = m ∧ Refine.le a0 a0' ∧ Refine.le a1 a1'
  | .bb2 m a0 a1, .bb2 m' a0' a1' => m' = m ∧ Refine.le a0 a0' ∧ Refine.le a1 a1'
  | .bb3 m v4, .bb3 m' v4' => m' = m ∧ Refine.le v4 v4'
  | .bb4 m v5 v6 a0 v3, .bb4 m' v5' v6' a0' v3' =>
    m' = m ∧ Refine.le v5 v5' ∧ Refine.le v6 v6' ∧ Refine.le a0 a0' ∧ Refine.le v3 v3'
  | _, _ => False

theorem step_sim (b : src.Block) (b' : tgt.Block) (h : R b b') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step b) (tgt.step b') := by
  match b, b', h with
  | .bb1 m a0 a1, .bb1 _ a0' a1', ⟨rfl, h0, h1⟩ =>
    exact Outcome.Sim.br (Mono.icmpEq h1 (Refine.refl_val _)) ⟨rfl, Refine.refl_val _⟩ ⟨rfl, h0, h1⟩
  | .bb2 m a0 a1, .bb2 _ a0' a1', ⟨rfl, h0, h1⟩ =>
    exact Outcome.Sim.jump ⟨rfl, Refine.refl_val _, Refine.refl_val _, h0, Mono.zext h1⟩
  | .bb3 m v4, .bb3 _ v4', ⟨rfl, h4⟩ => exact Outcome.Sim.ret ⟨h4, Mem.le.refl m⟩
  | .bb4 m v5 v6 a0 v3, .bb4 _ v5' v6' a0' v3', ⟨rfl, h5, h6, h0, h3⟩ =>
    rw [src_body, tgt_body]
    refine Outcome.Sim.andThen (Mono.loadInt m (Mono.gep m h0 (by refine_mono)) 32 4) fun v8 v8' h8 => ?_
    refine Outcome.Sim.andThen (Refines.sim_cut cut cut_tgt_mono h8) fun y y' hy => ?_
    refine Outcome.Sim.br (by refine_mono) ⟨rfl, ?_⟩ ⟨rfl, ?_, ?_, h0, h3⟩ <;> refine_mono

/-- Related blocks are under the loop's promise together. -/
theorem promise_eq (b : src.Block) (b' : tgt.Block) (h : R b b') : tgt.promise b' = src.promise b := by
  match b, b', h with
  | .bb1 .., .bb1 .., _ => rfl
  | .bb2 .., .bb2 .., _ => rfl
  | .bb3 .., .bb3 .., _ => rfl
  | .bb4 .., .bb4 .., _ => rfl

/-- **clang's loop with the multiply replaced refines clang's loop,** for every pointer and count, on every memory
the model has an answer for. -/
theorem clang_sum : Refines (fun p n m => (src p n m).answered) tgt := fun p n m => by
  rw [Refine.answered_iff]
  simp only [src, tgt]
  refine Mono.noundefPtr (Refine.Reflexive.refl p) (Mono.noundef (Refine.refl_val n) ?_)
  refine (Mono.call m _ _ (r := Refine.le) ?_).mono fun _ _ h => h
  refine (Outcome.Sim.promised step_sim promise_eq ?_).mono fun _ _ h => h
  exact ⟨rfl, Refine.Reflexive.refl _, Refine.refl_val n⟩

end ClangSum
