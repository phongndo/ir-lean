import gh_ad_blocks_ir

/-! The cut lemma on a kernel of the corpus, as clang compiled it. `tests/cut/gh_ad_blocks.ll`'s `@src` is libsodium's
`gh_ad_blocks`, AES-GCM's GHASH over the associated data: four loops, each loading the hash key's powers and 16-byte
blocks as vectors, multiplying them with PCLMULQDQ, reducing the product and storing the accumulator, which the next
loop loads again. `@tgt` is that function with the bound check before the 112-byte loop, `add nuw i64 %23, 112`,
replaced by `add i64 %23, 112`. `gh_ad_blocks` proves it refines `@src`, on every memory the model has an answer for,
from the cut's proof, `cut`.

So the code around the cut is a SIMD kernel's: vector loads, x86's PCLMULQDQ, shuffles, `bitcast`s between vectors,
and a vector accumulator stored to memory in one loop and loaded back in the next. The two memories are related by
`Mem.leData`, under which a load of what was stored keeps refinement, and every block but the cut's is the same code on
both sides, which `sim_mono` and `refine_mono_simd` walk with the library's lemmas: nothing here is about one of the
kernel's operations. `R`, the block lemmas and `promise_eq` follow the emitted blocks one for one. -/

open IRLean

namespace GhAdBlocks

open gh_ad_blocks_ir

/-- The proof about the cut alone: `add nuw %x, 112` to `add %x, 112`. Where the sum wraps, the source's is poison. -/
theorem cut : Refines cut_src cut_tgt := fun x => by
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
theorem cut_tgt_mono (x y : Val 64) (h : Refine.le x y) : Outcome.Sim Refine.le (cut_tgt x) (cut_tgt y) := by
  rw [show cut_tgt x = Outcome.ok _ from run_ret _ rfl, show cut_tgt y = Outcome.ok _ from run_ret _ rfl]
  refine Outcome.Sim.ok ?_
  refine_mono

/-- The block before the 112-byte loop is the cut and then its bound check, as written. -/
theorem src_body (m : Mem) (v20 : Val 64) (a0 a1 a2 : PtrVal) (a3 : Val 64) :
    src.step (.bb3 m v20 a0 a1 a2 a3) =
      andThen (cut_src v20) fun v21 =>
        br (Val.icmpUgt v21 a3) (.bb6 m v20 a0 a1 a2 a3) (.bb4 m a0 a1 a2 a3 v20 v21) := by
  rw [show cut_src v20 = Outcome.ok _ from run_ret _ rfl]
  simp only [src.step, andThen_ok]

theorem tgt_body (m : Mem) (v20 : Val 64) (a0 a1 a2 : PtrVal) (a3 : Val 64) :
    tgt.step (.bb3 m v20 a0 a1 a2 a3) =
      andThen (cut_tgt v20) fun v21 =>
        br (Val.icmpUgt v21 a3) (.bb6 m v20 a0 a1 a2 a3) (.bb4 m a0 a1 a2 a3 v20 v21) := by
  rw [show cut_tgt v20 = Outcome.ok _ from run_ret _ rfl]
  simp only [tgt.step, andThen_ok]

/-- Blocks of the same name, with memories related by their data and each live value in the target refining the
source's. -/
inductive R : src.Block → tgt.Block → Prop
  | bb1 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} :
     Mem.leData m m' → Refine.le a0 a0' → Refine.le a1 a1' → Refine.le a2 a2' → Refine.le a3 a3' →
      R (.bb1 m a0 a1 a2 a3) (.bb1 m' a0' a1' a2' a3')
  | bb2 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} :
     Mem.leData m m' → Refine.le a0 a0' → Refine.le a1 a1' → Refine.le a2 a2' → Refine.le a3 a3' →
      R (.bb2 m a0 a1 a2 a3) (.bb2 m' a0' a1' a2' a3')
  | bb3 {m m' : Mem} {v20 v20' : Val 64} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} :
     Mem.leData m m' → Refine.le v20 v20' → Refine.le a0 a0' → Refine.le a1 a1' → Refine.le a2 a2' →
      Refine.le a3 a3' → R (.bb3 m v20 a0 a1 a2 a3) (.bb3 m' v20' a0' a1' a2' a3')
  | bb4 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} {v20 v20' : Val 64}
      {v21 v21' : Val 64} :
     Mem.leData m m' → Refine.le a0 a0' → Refine.le a1 a1' → Refine.le a2 a2' → Refine.le a3 a3' →
      Refine.le v20 v20' → Refine.le v21 v21' → R (.bb4 m a0 a1 a2 a3 v20 v21) (.bb4 m' a0' a1' a2' a3' v20' v21')
  | bb5 {m m' : Mem} {v31 v31' : (Vec 2 64)} {v32 v32' : Val 64} {v33 v33' : Val 64} {a0 a0' : PtrVal}
      {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} {v5 v5' : PtrVal} {v6 v6' : PtrVal} {v8 v8' : PtrVal}
      {v9 v9' : PtrVal} {v10 v10' : PtrVal} {v11 v11' : PtrVal} {v12 v12' : PtrVal} {v13 v13' : PtrVal}
      {v14 v14' : PtrVal} {v15 v15' : PtrVal} {v16 v16' : PtrVal} {v17 v17' : PtrVal} {v18 v18' : PtrVal}
      {v19 v19' : PtrVal} :
     Mem.leData m m' → Refine.le v31 v31' → Refine.le v32 v32' → Refine.le v33 v33' → Refine.le a0 a0' →
      Refine.le a1 a1' → Refine.le a2 a2' → Refine.le a3 a3' → Refine.le v5 v5' → Refine.le v6 v6' →
      Refine.le v8 v8' → Refine.le v9 v9' → Refine.le v10 v10' → Refine.le v11 v11' → Refine.le v12 v12' →
      Refine.le v13 v13' → Refine.le v14 v14' → Refine.le v15 v15' → Refine.le v16 v16' → Refine.le v17 v17' →
      Refine.le v18 v18' → Refine.le v19 v19' →
      R (.bb5 m v31 v32 v33 a0 a1 a2 a3 v5 v6 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19)
      (.bb5 m' v31' v32' v33' a0' a1' a2' a3' v5' v6' v8' v9' v10' v11' v12' v13' v14' v15' v16' v17' v18' v19')
  | bb6 {m m' : Mem} {v227 v227' : Val 64} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} :
     Mem.leData m m' → Refine.le v227 v227' → Refine.le a0 a0' → Refine.le a1 a1' → Refine.le a2 a2' →
      Refine.le a3 a3' → R (.bb6 m v227 a0 a1 a2 a3) (.bb6 m' v227' a0' a1' a2' a3')
  | bb7 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} {v227 v227' : Val 64}
      {v228 v228' : Val 64} :
     Mem.leData m m' → Refine.le a0 a0' → Refine.le a1 a1' → Refine.le a2 a2' → Refine.le a3 a3' →
      Refine.le v227 v227' → Refine.le v228 v228' → R (.bb7 m a0 a1 a2 a3 v227 v228)
      (.bb7 m' a0' a1' a2' a3' v227' v228')
  | bb8 {m m' : Mem} {v235 v235' : (Vec 2 64)} {v236 v236' : Val 64} {v237 v237' : Val 64} {a0 a0' : PtrVal}
      {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} {v23 v23' : PtrVal} {v24 v24' : PtrVal}
      {v26 v26' : PtrVal} {v27 v27' : PtrVal} {v28 v28' : PtrVal} {v29 v29' : PtrVal} {v30 v30' : PtrVal} :
     Mem.leData m m' → Refine.le v235 v235' → Refine.le v236 v236' → Refine.le v237 v237' → Refine.le a0 a0' →
      Refine.le a1 a1' → Refine.le a2 a2' → Refine.le a3 a3' → Refine.le v23 v23' → Refine.le v24 v24' →
      Refine.le v26 v26' → Refine.le v27 v27' → Refine.le v28 v28' → Refine.le v29 v29' → Refine.le v30 v30' →
      R (.bb8 m v235 v236 v237 a0 a1 a2 a3 v23 v24 v26 v27 v28 v29 v30)
      (.bb8 m' v235' v236' v237' a0' a1' a2' a3' v23' v24' v26' v27' v28' v29' v30')
  | bb9 {m m' : Mem} {v340 v340' : Val 64} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} :
     Mem.leData m m' → Refine.le v340 v340' → Refine.le a0 a0' → Refine.le a1 a1' → Refine.le a2 a2' →
      Refine.le a3 a3' → R (.bb9 m v340 a0 a1 a2 a3) (.bb9 m' v340' a0' a1' a2' a3')
  | bb10 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} {v340 v340' : Val 64}
      {v341 v341' : Val 64} :
     Mem.leData m m' → Refine.le a0 a0' → Refine.le a1 a1' → Refine.le a2 a2' → Refine.le a3 a3' →
      Refine.le v340 v340' → Refine.le v341 v341' → R (.bb10 m a0 a1 a2 a3 v340 v341)
      (.bb10 m' a0' a1' a2' a3' v340' v341')
  | bb11 {m m' : Mem} {v346 v346' : (Vec 2 64)} {v347 v347' : Val 64} {v348 v348' : Val 64} {a0 a0' : PtrVal}
      {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} {v230 v230' : PtrVal} {v231 v231' : PtrVal}
      {v233 v233' : PtrVal} {v234 v234' : PtrVal} :
     Mem.leData m m' → Refine.le v346 v346' → Refine.le v347 v347' → Refine.le v348 v348' → Refine.le a0 a0' →
      Refine.le a1 a1' → Refine.le a2 a2' → Refine.le a3 a3' → Refine.le v230 v230' → Refine.le v231 v231' →
      Refine.le v233 v233' → Refine.le v234 v234' → R (.bb11 m v346 v347 v348 a0 a1 a2 a3 v230 v231 v233 v234)
      (.bb11 m' v346' v347' v348' a0' a1' a2' a3' v230' v231' v233' v234')
  | bb12 {m m' : Mem} {v412 v412' : (Vec 2 64)} {v413 v413' : Val 64} {v414 v414' : Val 64} {a0 a0' : PtrVal}
      {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} {v343 v343' : PtrVal} {v344 v344' : PtrVal} :
     Mem.leData m m' → Refine.le v412 v412' → Refine.le v413 v413' → Refine.le v414 v414' → Refine.le a0 a0' →
      Refine.le a1 a1' → Refine.le a2 a2' → Refine.le a3 a3' → Refine.le v343 v343' → Refine.le v344 v344' →
      R (.bb12 m v412 v413 v414 a0 a1 a2 a3 v343 v344) (.bb12 m' v412' v413' v414' a0' a1' a2' a3' v343' v344')
  | bb13 {m m' : Mem} {v452 v452' : Val 64} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} :
     Mem.leData m m' → Refine.le v452 v452' → Refine.le a0 a0' → Refine.le a1 a1' → Refine.le a2 a2' →
      Refine.le a3 a3' → R (.bb13 m v452 a0 a1 a2 a3) (.bb13 m' v452' a0' a1' a2' a3')
  | bb14 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {v452 v452' : Val 64} :
     Mem.leData m m' → Refine.le a0 a0' → Refine.le a1 a1' → Refine.le a2 a2' → Refine.le v452 v452' →
      R (.bb14 m a0 a1 a2 v452) (.bb14 m' a0' a1' a2' v452')
  | bb15 {m m' : Mem} :
     Mem.leData m m' → R (.bb15 m) (.bb15 m')

/-- Two blocks' code, the same on both sides: `sim_mono` walks it, the blocks it goes to are related by `R`'s
constructor for them, and what's left is values, for `refine_mono_simd`. -/
local macro "sim_block" : tactic =>
  `(tactic| (sim_mono <;>
    (repeat' (first | assumption | exact Mem.leData.toLe (by assumption) | apply And.intro | constructor)) <;>
    refine_mono_simd))

/-! Each block's two steps are related. All but the cut's are the same code on both sides, walked by `sim_block`: the
vector loads and the stores of the accumulator by `Mem.leData`'s lemmas, and PCLMULQDQ, the shuffles, `bitcast`s and
`xor`s by `refine_mono_simd`. -/

set_option maxHeartbeats 4000000 in
theorem step_bb1 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64}
    (h0 : Mem.leData m m') (h1 : Refine.le a0 a0') (h2 : Refine.le a1 a1') (h3 : Refine.le a2 a2')
    (h4 : Refine.le a3 a3') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb1 m a0 a1 a2 a3)) (tgt.step (.bb1 m' a0' a1' a2' a3')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb2 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64}
    (h0 : Mem.leData m m') (h1 : Refine.le a0 a0') (h2 : Refine.le a1 a1') (h3 : Refine.le a2 a2')
    (h4 : Refine.le a3 a3') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb2 m a0 a1 a2 a3)) (tgt.step (.bb2 m' a0' a1' a2' a3')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb3 {m m' : Mem} {v20 v20' : Val 64} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal}
    {a3 a3' : Val 64} (h0 : Mem.leData m m') (h1 : Refine.le v20 v20') (h2 : Refine.le a0 a0') (h3 : Refine.le a1 a1')
    (h4 : Refine.le a2 a2') (h5 : Refine.le a3 a3') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb3 m v20 a0 a1 a2 a3)) (tgt.step (.bb3 m' v20' a0' a1' a2'
      a3')) := by
  rw [src_body, tgt_body]
  refine Outcome.Sim.andThen (Refines.sim_cut cut cut_tgt_mono h1) fun _ _ _ => ?_
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb4 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64}
    {v20 v20' : Val 64} {v21 v21' : Val 64} (h0 : Mem.leData m m') (h1 : Refine.le a0 a0') (h2 : Refine.le a1 a1')
    (h3 : Refine.le a2 a2') (h4 : Refine.le a3 a3') (h5 : Refine.le v20 v20') (h6 : Refine.le v21 v21') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb4 m a0 a1 a2 a3 v20 v21)) (tgt.step (.bb4 m' a0' a1' a2' a3' v20'
      v21')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb5 {m m' : Mem} {v31 v31' : (Vec 2 64)} {v32 v32' : Val 64} {v33 v33' : Val 64} {a0 a0' : PtrVal}
    {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} {v5 v5' : PtrVal} {v6 v6' : PtrVal} {v8 v8' : PtrVal}
    {v9 v9' : PtrVal} {v10 v10' : PtrVal} {v11 v11' : PtrVal} {v12 v12' : PtrVal} {v13 v13' : PtrVal}
    {v14 v14' : PtrVal} {v15 v15' : PtrVal} {v16 v16' : PtrVal} {v17 v17' : PtrVal} {v18 v18' : PtrVal}
    {v19 v19' : PtrVal} (h0 : Mem.leData m m') (h1 : Refine.le v31 v31') (h2 : Refine.le v32 v32')
    (h3 : Refine.le v33 v33') (h4 : Refine.le a0 a0') (h5 : Refine.le a1 a1') (h6 : Refine.le a2 a2')
    (h7 : Refine.le a3 a3') (h8 : Refine.le v5 v5') (h9 : Refine.le v6 v6') (h10 : Refine.le v8 v8')
    (h11 : Refine.le v9 v9') (h12 : Refine.le v10 v10') (h13 : Refine.le v11 v11') (h14 : Refine.le v12 v12')
    (h15 : Refine.le v13 v13') (h16 : Refine.le v14 v14') (h17 : Refine.le v15 v15') (h18 : Refine.le v16 v16')
    (h19 : Refine.le v17 v17') (h20 : Refine.le v18 v18') (h21 : Refine.le v19 v19') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb5 m v31 v32 v33 a0 a1 a2 a3 v5 v6 v8 v9 v10 v11 v12 v13 v14 v15
      v16 v17 v18 v19)) (tgt.step (.bb5 m' v31' v32' v33' a0' a1' a2' a3' v5' v6' v8' v9' v10' v11' v12' v13' v14'
      v15' v16' v17' v18' v19')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb6 {m m' : Mem} {v227 v227' : Val 64} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal}
    {a3 a3' : Val 64} (h0 : Mem.leData m m') (h1 : Refine.le v227 v227') (h2 : Refine.le a0 a0')
    (h3 : Refine.le a1 a1') (h4 : Refine.le a2 a2') (h5 : Refine.le a3 a3') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb6 m v227 a0 a1 a2 a3)) (tgt.step (.bb6 m' v227' a0' a1' a2'
      a3')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb7 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64}
    {v227 v227' : Val 64} {v228 v228' : Val 64} (h0 : Mem.leData m m') (h1 : Refine.le a0 a0') (h2 : Refine.le a1 a1')
    (h3 : Refine.le a2 a2') (h4 : Refine.le a3 a3') (h5 : Refine.le v227 v227') (h6 : Refine.le v228 v228') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb7 m a0 a1 a2 a3 v227 v228)) (tgt.step (.bb7 m' a0' a1' a2' a3'
      v227' v228')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb8 {m m' : Mem} {v235 v235' : (Vec 2 64)} {v236 v236' : Val 64} {v237 v237' : Val 64} {a0 a0' : PtrVal}
    {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} {v23 v23' : PtrVal} {v24 v24' : PtrVal} {v26 v26' : PtrVal}
    {v27 v27' : PtrVal} {v28 v28' : PtrVal} {v29 v29' : PtrVal} {v30 v30' : PtrVal} (h0 : Mem.leData m m')
    (h1 : Refine.le v235 v235') (h2 : Refine.le v236 v236') (h3 : Refine.le v237 v237') (h4 : Refine.le a0 a0')
    (h5 : Refine.le a1 a1') (h6 : Refine.le a2 a2') (h7 : Refine.le a3 a3') (h8 : Refine.le v23 v23')
    (h9 : Refine.le v24 v24') (h10 : Refine.le v26 v26') (h11 : Refine.le v27 v27') (h12 : Refine.le v28 v28')
    (h13 : Refine.le v29 v29') (h14 : Refine.le v30 v30') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb8 m v235 v236 v237 a0 a1 a2 a3 v23 v24 v26 v27 v28 v29 v30))
      (tgt.step (.bb8 m' v235' v236' v237' a0' a1' a2' a3' v23' v24' v26' v27' v28' v29' v30')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb9 {m m' : Mem} {v340 v340' : Val 64} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal}
    {a3 a3' : Val 64} (h0 : Mem.leData m m') (h1 : Refine.le v340 v340') (h2 : Refine.le a0 a0')
    (h3 : Refine.le a1 a1') (h4 : Refine.le a2 a2') (h5 : Refine.le a3 a3') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb9 m v340 a0 a1 a2 a3)) (tgt.step (.bb9 m' v340' a0' a1' a2'
      a3')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb10 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64}
    {v340 v340' : Val 64} {v341 v341' : Val 64} (h0 : Mem.leData m m') (h1 : Refine.le a0 a0') (h2 : Refine.le a1 a1')
    (h3 : Refine.le a2 a2') (h4 : Refine.le a3 a3') (h5 : Refine.le v340 v340') (h6 : Refine.le v341 v341') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb10 m a0 a1 a2 a3 v340 v341)) (tgt.step (.bb10 m' a0' a1' a2' a3'
      v340' v341')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb11 {m m' : Mem} {v346 v346' : (Vec 2 64)} {v347 v347' : Val 64} {v348 v348' : Val 64} {a0 a0' : PtrVal}
    {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} {v230 v230' : PtrVal} {v231 v231' : PtrVal}
    {v233 v233' : PtrVal} {v234 v234' : PtrVal} (h0 : Mem.leData m m') (h1 : Refine.le v346 v346')
    (h2 : Refine.le v347 v347') (h3 : Refine.le v348 v348') (h4 : Refine.le a0 a0') (h5 : Refine.le a1 a1')
    (h6 : Refine.le a2 a2') (h7 : Refine.le a3 a3') (h8 : Refine.le v230 v230') (h9 : Refine.le v231 v231')
    (h10 : Refine.le v233 v233') (h11 : Refine.le v234 v234') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb11 m v346 v347 v348 a0 a1 a2 a3 v230 v231 v233 v234))
      (tgt.step (.bb11 m' v346' v347' v348' a0' a1' a2' a3' v230' v231' v233' v234')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb12 {m m' : Mem} {v412 v412' : (Vec 2 64)} {v413 v413' : Val 64} {v414 v414' : Val 64} {a0 a0' : PtrVal}
    {a1 a1' : PtrVal} {a2 a2' : PtrVal} {a3 a3' : Val 64} {v343 v343' : PtrVal} {v344 v344' : PtrVal}
    (h0 : Mem.leData m m') (h1 : Refine.le v412 v412') (h2 : Refine.le v413 v413') (h3 : Refine.le v414 v414')
    (h4 : Refine.le a0 a0') (h5 : Refine.le a1 a1') (h6 : Refine.le a2 a2') (h7 : Refine.le a3 a3')
    (h8 : Refine.le v343 v343') (h9 : Refine.le v344 v344') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb12 m v412 v413 v414 a0 a1 a2 a3 v343 v344)) (tgt.step (.bb12 m'
      v412' v413' v414' a0' a1' a2' a3' v343' v344')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb13 {m m' : Mem} {v452 v452' : Val 64} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal}
    {a3 a3' : Val 64} (h0 : Mem.leData m m') (h1 : Refine.le v452 v452') (h2 : Refine.le a0 a0')
    (h3 : Refine.le a1 a1') (h4 : Refine.le a2 a2') (h5 : Refine.le a3 a3') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb13 m v452 a0 a1 a2 a3)) (tgt.step (.bb13 m' v452' a0' a1' a2'
      a3')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb14 {m m' : Mem} {a0 a0' : PtrVal} {a1 a1' : PtrVal} {a2 a2' : PtrVal} {v452 v452' : Val 64}
    (h0 : Mem.leData m m') (h1 : Refine.le a0 a0') (h2 : Refine.le a1 a1') (h3 : Refine.le a2 a2')
    (h4 : Refine.le v452 v452') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb14 m a0 a1 a2 v452)) (tgt.step (.bb14 m' a0' a1' a2'
      v452')) := by
  sim_block

set_option maxHeartbeats 4000000 in
theorem step_bb15 {m m' : Mem} (h0 : Mem.leData m m') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step (.bb15 m)) (tgt.step (.bb15 m')) := by
  sim_block

/-- Related blocks step to related blocks, or return related results. -/
theorem step_sim (b : src.Block) (b' : tgt.Block) (h : R b b') :
    Outcome.Sim (Next.Rel R Refine.le) (src.step b) (tgt.step b') := by
  cases h
  case bb1 => apply step_bb1 <;> assumption
  case bb2 => apply step_bb2 <;> assumption
  case bb3 => apply step_bb3 <;> assumption
  case bb4 => apply step_bb4 <;> assumption
  case bb5 => apply step_bb5 <;> assumption
  case bb6 => apply step_bb6 <;> assumption
  case bb7 => apply step_bb7 <;> assumption
  case bb8 => apply step_bb8 <;> assumption
  case bb9 => apply step_bb9 <;> assumption
  case bb10 => apply step_bb10 <;> assumption
  case bb11 => apply step_bb11 <;> assumption
  case bb12 => apply step_bb12 <;> assumption
  case bb13 => apply step_bb13 <;> assumption
  case bb14 => apply step_bb14 <;> assumption
  case bb15 => apply step_bb15 <;> assumption

/-- Related blocks are under the loops' promise together. -/
theorem promise_eq (b : src.Block) (b' : tgt.Block) (h : R b b') : tgt.promise b' = src.promise b := by
  cases h <;> rfl

/-- **libsodium's `gh_ad_blocks` with the cut's replacement refines `gh_ad_blocks`, as clang compiled it,** for every
pointer and length, on every memory the model has an answer for. -/
theorem gh_ad_blocks : Refines (fun a0 a1 a2 a3 m => (src a0 a1 a2 a3 m).answered) tgt := fun a0 a1 a2 a3 m => by
  rw [Refine.answered_iff]
  simp only [src, tgt]
  refine Mono.noundefPtr (Refine.Reflexive.refl _) (Mono.noundefPtr (Refine.Reflexive.refl _)
    (Mono.noundefPtr (Refine.Reflexive.refl _) (Mono.noundef (Refine.refl_val _) ?_)))
  refine (Mono.call m _ _ (r := Refine.le) ?_).mono fun _ _ h => h
  refine (Outcome.Sim.promised step_sim promise_eq ?_).mono fun _ _ h => h
  exact .bb1 (Mem.leData.refl _) (Refine.Reflexive.refl _) (Refine.Reflexive.refl _) (Refine.Reflexive.refl _)
    (Refine.refl_val _)

end GhAdBlocks
