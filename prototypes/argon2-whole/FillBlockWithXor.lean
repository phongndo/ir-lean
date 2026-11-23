import Whole
import Base
import Cand
import T2
import T3

open IRLean IRLean.Whole

set_option maxRecDepth 100000

namespace FillBlockWithXor

/-- The candidate's block of the same name, with the same fields and the same memory. -/
def same : Base.fill_block_with_xor.Block → Cand.fill_block_with_xor.Block
  | (.bb1 m a0 a1 a2) => (.bb1 m a0 a1 a2)
  | (.bb2 m v112 v113 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111) => (.bb2 m v112 v113 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111)
  | (.bb3 m v280 v281 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111) => (.bb3 m v280 v281 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111)
  | (.bb4 m a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111) => (.bb4 m a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111)

set_option maxHeartbeats 4000000 in
theorem step_bb1 (m : Mem) (a0 a1 a2 : PtrVal) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.fill_block_with_xor.step (.bb1 m a0 a1 a2))
      (Cand.fill_block_with_xor.step (.bb1 m a0 a1 a2)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb2 (m : Mem) (v112 : Val 1) (v113 : Val 64) (a0 a2 : PtrVal) (v5 v6 : (Vec 8 64)) (v7 : PtrVal) (v11 : (Vec 8 64)) (v12 : PtrVal) (v13 : (Vec 8 64)) (v14 : PtrVal) (v18 : (Vec 8 64)) (v19 : PtrVal) (v20 : (Vec 8 64)) (v21 : PtrVal) (v25 : (Vec 8 64)) (v26 : PtrVal) (v27 : (Vec 8 64)) (v28 : PtrVal) (v32 : (Vec 8 64)) (v33 : PtrVal) (v34 : (Vec 8 64)) (v35 : PtrVal) (v39 : (Vec 8 64)) (v40 : PtrVal) (v41 : (Vec 8 64)) (v42 : PtrVal) (v46 : (Vec 8 64)) (v47 : PtrVal) (v48 : (Vec 8 64)) (v49 : PtrVal) (v53 : (Vec 8 64)) (v54 : PtrVal) (v55 : (Vec 8 64)) (v56 : PtrVal) (v60 : (Vec 8 64)) (v61 : PtrVal) (v62 : (Vec 8 64)) (v63 : PtrVal) (v67 : (Vec 8 64)) (v68 : PtrVal) (v69 : (Vec 8 64)) (v70 : PtrVal) (v74 : (Vec 8 64)) (v75 : PtrVal) (v76 : (Vec 8 64)) (v77 : PtrVal) (v81 : (Vec 8 64)) (v82 : PtrVal) (v83 : (Vec 8 64)) (v84 : PtrVal) (v88 : (Vec 8 64)) (v89 : PtrVal) (v90 : (Vec 8 64)) (v91 : PtrVal) (v95 : (Vec 8 64)) (v96 : PtrVal) (v97 : (Vec 8 64)) (v98 : PtrVal) (v102 : (Vec 8 64)) (v103 : PtrVal) (v104 : (Vec 8 64)) (v105 : PtrVal) (v109 : (Vec 8 64)) (v110 : PtrVal) (v111 : (Vec 8 64)) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.fill_block_with_xor.step (.bb2 m v112 v113 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111))
      (Cand.fill_block_with_xor.step (.bb2 m v112 v113 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111)) := by
  sim_unfold
  sim_same
  sim_at v202
  cut_store (r2_o0_same v175 v181 v184 v185 v191 v197 v200 v201) (R2Src.r2_o0_src.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201)) (R2Tgt.r2_o0_tgt.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201))
  cut_store (r2_o1_same v175 v181 v184 v185 v191 v197 v200 v201) (R2Src.r2_o1_src.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201)) (R2Tgt.r2_o1_tgt.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201))
  cut_store (r2_o2_same v175 v181 v184 v185 v191 v197 v200 v201) (R2Src.r2_o2_src.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201)) (R2Tgt.r2_o2_tgt.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201))
  cut_store (r2_o3_same v175 v181 v184 v185 v191 v197 v200 v201) (R2Src.r2_o3_src.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201)) (R2Tgt.r2_o3_tgt.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201))
  cut_store (r2_o4_same v175 v181 v184 v185 v191 v197 v200 v201) (R2Src.r2_o4_src.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201)) (R2Tgt.r2_o4_tgt.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201))
  cut_store (r2_o5_same v175 v181 v184 v185 v191 v197 v200 v201) (R2Src.r2_o5_src.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201)) (R2Tgt.r2_o5_tgt.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201))
  cut_store (r2_o6_same v175 v181 v184 v185 v191 v197 v200 v201) (R2Src.r2_o6_src.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201)) (R2Tgt.r2_o6_tgt.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201))
  cut_store (r2_o7_same v175 v181 v184 v185 v191 v197 v200 v201) (R2Src.r2_o7_src.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201)) (R2Tgt.r2_o7_tgt.step (.bb1 v175 v181 v184 v185 v191 v197 v200 v201))
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb3 (m : Mem) (v280 : Val 1) (v281 : Val 64) (a0 a2 : PtrVal) (v5 v6 : (Vec 8 64)) (v7 : PtrVal) (v11 : (Vec 8 64)) (v12 : PtrVal) (v13 : (Vec 8 64)) (v14 : PtrVal) (v18 : (Vec 8 64)) (v19 : PtrVal) (v20 : (Vec 8 64)) (v21 : PtrVal) (v25 : (Vec 8 64)) (v26 : PtrVal) (v27 : (Vec 8 64)) (v28 : PtrVal) (v32 : (Vec 8 64)) (v33 : PtrVal) (v34 : (Vec 8 64)) (v35 : PtrVal) (v39 : (Vec 8 64)) (v40 : PtrVal) (v41 : (Vec 8 64)) (v42 : PtrVal) (v46 : (Vec 8 64)) (v47 : PtrVal) (v48 : (Vec 8 64)) (v49 : PtrVal) (v53 : (Vec 8 64)) (v54 : PtrVal) (v55 : (Vec 8 64)) (v56 : PtrVal) (v60 : (Vec 8 64)) (v61 : PtrVal) (v62 : (Vec 8 64)) (v63 : PtrVal) (v67 : (Vec 8 64)) (v68 : PtrVal) (v69 : (Vec 8 64)) (v70 : PtrVal) (v74 : (Vec 8 64)) (v75 : PtrVal) (v76 : (Vec 8 64)) (v77 : PtrVal) (v81 : (Vec 8 64)) (v82 : PtrVal) (v83 : (Vec 8 64)) (v84 : PtrVal) (v88 : (Vec 8 64)) (v89 : PtrVal) (v90 : (Vec 8 64)) (v91 : PtrVal) (v95 : (Vec 8 64)) (v96 : PtrVal) (v97 : (Vec 8 64)) (v98 : PtrVal) (v102 : (Vec 8 64)) (v103 : PtrVal) (v104 : (Vec 8 64)) (v105 : PtrVal) (v109 : (Vec 8 64)) (v110 : PtrVal) (v111 : (Vec 8 64)) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.fill_block_with_xor.step (.bb3 m v280 v281 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111))
      (Cand.fill_block_with_xor.step (.bb3 m v280 v281 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111)) := by
  sim_unfold
  sim_same
  sim_at v370
  cut_store (r3_o0_same v343 v349 v352 v353 v359 v365 v368 v369) (R3Src.r3_o0_src.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369)) (R3Tgt.r3_o0_tgt.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369))
  cut_store (r3_o1_same v343 v349 v352 v353 v359 v365 v368 v369) (R3Src.r3_o1_src.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369)) (R3Tgt.r3_o1_tgt.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369))
  cut_store (r3_o2_same v343 v349 v352 v353 v359 v365 v368 v369) (R3Src.r3_o2_src.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369)) (R3Tgt.r3_o2_tgt.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369))
  cut_store (r3_o3_same v343 v349 v352 v353 v359 v365 v368 v369) (R3Src.r3_o3_src.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369)) (R3Tgt.r3_o3_tgt.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369))
  cut_store (r3_o4_same v343 v349 v352 v353 v359 v365 v368 v369) (R3Src.r3_o4_src.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369)) (R3Tgt.r3_o4_tgt.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369))
  cut_store (r3_o5_same v343 v349 v352 v353 v359 v365 v368 v369) (R3Src.r3_o5_src.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369)) (R3Tgt.r3_o5_tgt.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369))
  cut_store (r3_o6_same v343 v349 v352 v353 v359 v365 v368 v369) (R3Src.r3_o6_src.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369)) (R3Tgt.r3_o6_tgt.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369))
  cut_store (r3_o7_same v343 v349 v352 v353 v359 v365 v368 v369) (R3Src.r3_o7_src.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369)) (R3Tgt.r3_o7_tgt.step (.bb1 v343 v349 v352 v353 v359 v365 v368 v369))
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb4 (m : Mem) (a0 a2 : PtrVal) (v5 v6 : (Vec 8 64)) (v7 : PtrVal) (v11 : (Vec 8 64)) (v12 : PtrVal) (v13 : (Vec 8 64)) (v14 : PtrVal) (v18 : (Vec 8 64)) (v19 : PtrVal) (v20 : (Vec 8 64)) (v21 : PtrVal) (v25 : (Vec 8 64)) (v26 : PtrVal) (v27 : (Vec 8 64)) (v28 : PtrVal) (v32 : (Vec 8 64)) (v33 : PtrVal) (v34 : (Vec 8 64)) (v35 : PtrVal) (v39 : (Vec 8 64)) (v40 : PtrVal) (v41 : (Vec 8 64)) (v42 : PtrVal) (v46 : (Vec 8 64)) (v47 : PtrVal) (v48 : (Vec 8 64)) (v49 : PtrVal) (v53 : (Vec 8 64)) (v54 : PtrVal) (v55 : (Vec 8 64)) (v56 : PtrVal) (v60 : (Vec 8 64)) (v61 : PtrVal) (v62 : (Vec 8 64)) (v63 : PtrVal) (v67 : (Vec 8 64)) (v68 : PtrVal) (v69 : (Vec 8 64)) (v70 : PtrVal) (v74 : (Vec 8 64)) (v75 : PtrVal) (v76 : (Vec 8 64)) (v77 : PtrVal) (v81 : (Vec 8 64)) (v82 : PtrVal) (v83 : (Vec 8 64)) (v84 : PtrVal) (v88 : (Vec 8 64)) (v89 : PtrVal) (v90 : (Vec 8 64)) (v91 : PtrVal) (v95 : (Vec 8 64)) (v96 : PtrVal) (v97 : (Vec 8 64)) (v98 : PtrVal) (v102 : (Vec 8 64)) (v103 : PtrVal) (v104 : (Vec 8 64)) (v105 : PtrVal) (v109 : (Vec 8 64)) (v110 : PtrVal) (v111 : (Vec 8 64)) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.fill_block_with_xor.step (.bb4 m a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111))
      (Cand.fill_block_with_xor.step (.bb4 m a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111)) := by
  sim_unfold
  sim_same
  sim_end

/-- Blocks that are the same block step to the same block, or return the same result and memory. -/
theorem step_sim (b : Base.fill_block_with_xor.Block) (b' : Cand.fill_block_with_xor.Block) (h : same b = b') :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.fill_block_with_xor.step b) (Cand.fill_block_with_xor.step b') := by
  subst h
  cases b with
  | bb1 m a0 a1 a2 => exact step_bb1 m a0 a1 a2
  | bb2 m v112 v113 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111 => exact step_bb2 m v112 v113 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111
  | bb3 m v280 v281 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111 => exact step_bb3 m v280 v281 a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111
  | bb4 m a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111 => exact step_bb4 m a0 a2 v5 v6 v7 v11 v12 v13 v14 v18 v19 v20 v21 v25 v26 v27 v28 v32 v33 v34 v35 v39 v40 v41 v42 v46 v47 v48 v49 v53 v54 v55 v56 v60 v61 v62 v63 v67 v68 v69 v70 v74 v75 v76 v77 v81 v82 v83 v84 v88 v89 v90 v91 v95 v96 v97 v98 v102 v103 v104 v105 v109 v110 v111

/-- They're under the loops' promise together. -/
theorem promise_eq (b : Base.fill_block_with_xor.Block) (b' : Cand.fill_block_with_xor.Block) (h : same b = b') :
    Cand.fill_block_with_xor.promise b' = Base.fill_block_with_xor.promise b := by
  subst h
  cases b <;> rfl

/-- **The candidate's `fill_block_with_xor` does what the baseline's does,** for every pointer and memory: where the
baseline's returns, the candidate's returns with the same memory, and where the baseline's never finishes, neither
does the candidate's. Where the baseline's is undefined or the model has no answer for it, there's no claim. -/
theorem fill_block_with_xor_same (a0 a1 a2 : PtrVal) (m : Mem) :
    Outcome.Sim Eq (Base.fill_block_with_xor a0 a1 a2 m) (Cand.fill_block_with_xor a0 a1 a2 m) := by
  simp only [Base.fill_block_with_xor, Cand.fill_block_with_xor]
  refine Mono.noundefPtr (Refine.Reflexive.refl _) (Mono.noundefPtr (Refine.Reflexive.refl _)
    (Mono.noundefPtr (Refine.Reflexive.refl _) ?_))
  rw [Mem.call_eq, Mem.call_eq]
  refine Outcome.Sim.andThen (r := Eq) ?_ fun x y h => by subst h; exact Outcome.Sim.refl (fun _ => rfl) _
  exact Outcome.Sim.promised step_sim promise_eq rfl

/-- **libsodium's `fill_block_with_xor` with rows A, C and D rotated refines the one with rows B, C and D rotated, as
clang compiled both,** for every pointer, on every memory the model has an answer for. -/
theorem fill_block_with_xor :
    Refines (fun a0 a1 a2 m => (Base.fill_block_with_xor a0 a1 a2 m).answered) Cand.fill_block_with_xor :=
  fun a0 a1 a2 m => (Refine.answered_iff _ _).2
    ((fill_block_with_xor_same a0 a1 a2 m).mono fun x y h => by subst h; exact ⟨Refine.unit _ _, Mem.le.refl _⟩)

#print axioms fill_block_with_xor_same
#print axioms fill_block_with_xor

end FillBlockWithXor
