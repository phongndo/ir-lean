import Whole
import Base
import Cand
import FillBlockWithXor
import T0
import T1

open IRLean IRLean.Whole

set_option maxRecDepth 100000

namespace FillSegment

/-- The candidate's block of the same name, with the same fields and the same memory. -/
def same : Base.argon2_fill_segment_avx512f.Block → Cand.argon2_fill_segment_avx512f.Block
  | (.g0 (.bb3 m a0 a1 a2)) => (.g0 (.bb3 m a0 a1 a2))
  | (.g0 (.bb4 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15)) => (.g0 (.bb4 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15))
  | (.g0 (.bb5 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17)) => (.g0 (.bb5 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17))
  | (.g0 (.bb6 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17)) => (.g0 (.bb6 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17))
  | (.g0 (.bb7 m a0 a2 v8 v9 v10 v11 v12 v14 v15 v25)) => (.g0 (.bb7 m a0 a2 v8 v9 v10 v11 v12 v14 v15 v25))
  | (.g0 (.bb8 m v28 a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17)) => (.g0 (.bb8 m v28 a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17))
  | (.g0 (.bb9 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44)) => (.g0 (.bb9 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44))
  | (.g0 (.bb10 m v48 v49 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47)) => (.g0 (.bb10 m v48 v49 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47))
  | (.g0 (.bb11 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v49 v50)) => (.g0 (.bb11 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v49 v50))
  | (.g0 (.bb12 m v53 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v50)) => (.g0 (.bb12 m v53 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v50))
  | (.g0 (.bb13 m v61 a0 a2 v3 v4 v5 v8 v9 v10 v11 v12 v14 v15 v28)) => (.g0 (.bb13 m v61 a0 a2 v3 v4 v5 v8 v9 v10 v11 v12 v14 v15 v28))
  | (.g0 (.bb14 m v62 v63 v64 a0 a2 v8 v9 v10 v11 v12 v14 v15)) => (.g0 (.bb14 m v62 v63 v64 a0 a2 v8 v9 v10 v11 v12 v14 v15))
  | (.g0 (.bb15 m a0 v8 v10 v12 v14 v15 v62 v63 v64 v65 v66 v67 v68 v69 v73 v74 v77 v82)) => (.g0 (.bb15 m a0 v8 v10 v12 v14 v15 v62 v63 v64 v65 v66 v67 v68 v69 v73 v74 v77 v82))
  | (.g0 (.bb16 m v106 v107 v108 v109 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104)) => (.g0 (.bb16 m v106 v107 v108 v109 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104))
  | (.g0 (.bb17 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114)) => (.g0 (.bb17 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114))
  | (.g0 (.bb18 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114)) => (.g0 (.bb18 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114))
  | (.g1 (.bb19 m v121 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114)) => (.g1 (.bb19 m v121 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114))
  | (.g1 (.bb20 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129)) => (.g1 (.bb20 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129))
  | (.g1 (.bb21 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128)) => (.g1 (.bb21 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128))
  | (.g1 (.bb22 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129)) => (.g1 (.bb22 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129))
  | (.g1 (.bb23 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132)) => (.g1 (.bb23 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132))
  | (.g1 (.bb24 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132)) => (.g1 (.bb24 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132))
  | (.g1 (.bb25 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129)) => (.g1 (.bb25 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129))
  | (.g1 (.bb26 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128)) => (.g1 (.bb26 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128))
  | (.g1 (.bb27 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128)) => (.g1 (.bb27 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128))
  | (.g1 (.bb28 m v145 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128)) => (.g1 (.bb28 m v145 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128))
  | (.g1 (.bb29 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v146)) => (.g1 (.bb29 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v146))
  | (.g1 (.bb30 m v149 v150 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128)) => (.g1 (.bb30 m v149 v150 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128))
  | (.g1 (.bb31 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170)) => (.g1 (.bb31 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170))
  | (.g1 (.bb32 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170)) => (.g1 (.bb32 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170))
  | (.g1 (.bb33 m v234 v235 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233)) => (.g1 (.bb33 m v234 v235 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233))
  | (.g1 (.bb34 m v401 v402 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233)) => (.g1 (.bb34 m v401 v402 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233))
  | (.g2 (.bb35 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233)) => (.g2 (.bb35 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233))
  | (.g2 (.bb36 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114)) => (.g2 (.bb36 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114))
  | (.g2 (.bb37 m v8)) => (.g2 (.bb37 m v8))

set_option maxHeartbeats 4000000 in
theorem step_bb3 (m : Mem) (a0 : PtrVal) (a1 a2 : Val 64) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb3 m a0 a1 a2))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb3 m a0 a1 a2)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb4 (m : Mem) (a0 : PtrVal) (a1 a2 : Val 64) (v3 v4 v5 v6 v7 v8 : PtrVal) (v9 : Val 32) (v10 : Val 64) (v11 : Val 32) (v12 : Val 8) (v14 v15 : PtrVal) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb4 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb4 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb5 (m : Mem) (a0 : PtrVal) (a1 a2 : Val 64) (v3 v4 v5 v6 v7 v8 : PtrVal) (v9 : Val 32) (v10 : Val 64) (v11 : Val 32) (v12 : Val 8) (v14 v15 : PtrVal) (v17 : Val 32) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb5 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb5 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb6 (m : Mem) (a0 : PtrVal) (a1 a2 : Val 64) (v3 v4 v5 v6 v7 v8 : PtrVal) (v9 : Val 32) (v10 : Val 64) (v11 : Val 32) (v12 : Val 8) (v14 v15 : PtrVal) (v17 : Val 32) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb6 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb6 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb7 (m : Mem) (a0 : PtrVal) (a2 : Val 64) (v8 : PtrVal) (v9 : Val 32) (v10 : Val 64) (v11 : Val 32) (v12 : Val 8) (v14 v15 v25 : PtrVal) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb7 m a0 a2 v8 v9 v10 v11 v12 v14 v15 v25))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb7 m a0 a2 v8 v9 v10 v11 v12 v14 v15 v25)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb8 (m : Mem) (v28 a0 : PtrVal) (a1 a2 : Val 64) (v3 v4 v5 v6 v7 v8 : PtrVal) (v9 : Val 32) (v10 : Val 64) (v11 : Val 32) (v12 : Val 8) (v14 v15 : PtrVal) (v17 : Val 32) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb8 m v28 a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb8 m v28 a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb9 (m : Mem) (a0 : PtrVal) (a2 : Val 64) (v3 v4 v5 v6 v7 v8 : PtrVal) (v9 : Val 32) (v10 : Val 64) (v11 : Val 32) (v12 : Val 8) (v14 v15 v28 v44 : PtrVal) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb9 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb9 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb10 (m : Mem) (v48 v49 : Val 64) (a0 : PtrVal) (a2 : Val 64) (v3 v4 v5 v6 v7 v8 : PtrVal) (v9 : Val 32) (v10 : Val 64) (v11 : Val 32) (v12 : Val 8) (v14 v15 v28 v44 v47 : PtrVal) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb10 m v48 v49 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb10 m v48 v49 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb11 (m : Mem) (a0 : PtrVal) (a2 : Val 64) (v3 v4 v5 v6 v7 v8 : PtrVal) (v9 : Val 32) (v10 : Val 64) (v11 : Val 32) (v12 : Val 8) (v14 v15 v28 v44 v47 : PtrVal) (v48 v49 v50 : Val 64) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb11 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v49 v50))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb11 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v49 v50)) := by
  sim_unfold
  sim_same
  call_same FillBlockWithXor.fill_block_with_xor_same
  sim_same
  call_same FillBlockWithXor.fill_block_with_xor_same
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb12 (m : Mem) (v53 : Val 64) (a0 : PtrVal) (a2 : Val 64) (v3 v4 v5 v6 v7 v8 : PtrVal) (v9 : Val 32) (v10 : Val 64) (v11 : Val 32) (v12 : Val 8) (v14 v15 v28 v44 v47 : PtrVal) (v48 v50 : Val 64) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb12 m v53 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v50))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb12 m v53 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v50)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb13 (m : Mem) (v61 : Val 32) (a0 : PtrVal) (a2 : Val 64) (v3 v4 v5 v8 : PtrVal) (v9 : Val 32) (v10 : Val 64) (v11 : Val 32) (v12 : Val 8) (v14 v15 v28 : PtrVal) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb13 m v61 a0 a2 v3 v4 v5 v8 v9 v10 v11 v12 v14 v15 v28))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb13 m v61 a0 a2 v3 v4 v5 v8 v9 v10 v11 v12 v14 v15 v28)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb14 (m : Mem) (v62 : Val 32) (v63 : PtrVal) (v64 : Val 1) (a0 : PtrVal) (a2 : Val 64) (v8 : PtrVal) (v9 : Val 32) (v10 : Val 64) (v11 : Val 32) (v12 : Val 8) (v14 v15 : PtrVal) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb14 m v62 v63 v64 a0 a2 v8 v9 v10 v11 v12 v14 v15))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb14 m v62 v63 v64 a0 a2 v8 v9 v10 v11 v12 v14 v15)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb15 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v12 : Val 8) (v14 v15 : PtrVal) (v62 : Val 32) (v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v68 : Val 32) (v69 : PtrVal) (v73 : Val 32) (v74 : PtrVal) (v77 v82 : Val 32) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb15 m a0 v8 v10 v12 v14 v15 v62 v63 v64 v65 v66 v67 v68 v69 v73 v74 v77 v82))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb15 m a0 v8 v10 v12 v14 v15 v62 v63 v64 v65 v66 v67 v68 v69 v73 v74 v77 v82)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb16 (m : Mem) (v106 : Val 64) (v107 v108 v109 : Val 32) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb16 m v106 v107 v108 v109 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb16 m v106 v107 v108 v109 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb17 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v107 v108 v110 v114 : Val 32) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb17 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb17 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb18 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v107 v108 v110 v114 : Val 32) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G0.step (.bb18 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114))
      (Cand.argon2_fill_segment_avx512f.G0.step (.bb18 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb19 (m : Mem) (v121 a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v107 v108 v110 v114 : Val 32) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb19 m v121 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb19 m v121 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb20 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v107 v108 v110 v114 : Val 32) (v122 v128 : Val 64) (v129 : Val 1) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb20 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb20 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb21 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v108 v110 v114 : Val 32) (v122 v128 : Val 64) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb21 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb21 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb22 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v107 v108 v110 v114 : Val 32) (v122 v128 : Val 64) (v129 : Val 1) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb22 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb22 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb23 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v108 v110 v114 : Val 32) (v122 v128 : Val 64) (v132 : Val 32) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb23 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb23 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb24 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v108 v110 v114 : Val 32) (v122 v128 : Val 64) (v132 : Val 32) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb24 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb24 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb25 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v107 v108 v110 v114 : Val 32) (v122 v128 : Val 64) (v129 : Val 1) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb25 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb25 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb26 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v107 v108 v110 v114 : Val 32) (v122 v128 : Val 64) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb26 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb26 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb27 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v107 v108 v110 v114 : Val 32) (v122 v128 : Val 64) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb27 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb27 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb28 (m : Mem) (v145 : Val 32) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v107 v108 v110 v114 : Val 32) (v122 v128 : Val 64) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb28 m v145 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb28 m v145 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb29 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v107 v108 v110 v114 : Val 32) (v122 v128 : Val 64) (v146 : Val 32) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb29 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v146))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb29 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v146)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb30 (m : Mem) (v149 : Val 32) (v150 : Val 64) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v108 v110 v114 : Val 32) (v122 v128 : Val 64) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb30 m v149 v150 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb30 m v149 v150 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb31 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v108 v114 : Val 32) (v168 v170 : PtrVal) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb31 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb31 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170)) := by
  sim_unfold
  sim_same
  call_same FillBlockWithXor.fill_block_with_xor_same
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb32 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v108 v114 : Val 32) (v168 v170 : PtrVal) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb32 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb32 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb33 (m : Mem) (v234 : Val 1) (v235 a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v108 v114 : Val 32) (v170 : PtrVal) (v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233 : (Vec 8 64)) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb33 m v234 v235 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb33 m v234 v235 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233)) := by
  sim_unfold
  sim_same
  sim_at v323
  cut_store (r0_o0_same v296 v302 v305 v306 v312 v318 v321 v322) (R0Src.r0_o0_src.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322)) (R0Tgt.r0_o0_tgt.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322))
  cut_store (r0_o1_same v296 v302 v305 v306 v312 v318 v321 v322) (R0Src.r0_o1_src.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322)) (R0Tgt.r0_o1_tgt.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322))
  cut_store (r0_o2_same v296 v302 v305 v306 v312 v318 v321 v322) (R0Src.r0_o2_src.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322)) (R0Tgt.r0_o2_tgt.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322))
  cut_store (r0_o3_same v296 v302 v305 v306 v312 v318 v321 v322) (R0Src.r0_o3_src.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322)) (R0Tgt.r0_o3_tgt.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322))
  cut_store (r0_o4_same v296 v302 v305 v306 v312 v318 v321 v322) (R0Src.r0_o4_src.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322)) (R0Tgt.r0_o4_tgt.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322))
  cut_store (r0_o5_same v296 v302 v305 v306 v312 v318 v321 v322) (R0Src.r0_o5_src.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322)) (R0Tgt.r0_o5_tgt.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322))
  cut_store (r0_o6_same v296 v302 v305 v306 v312 v318 v321 v322) (R0Src.r0_o6_src.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322)) (R0Tgt.r0_o6_tgt.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322))
  cut_store (r0_o7_same v296 v302 v305 v306 v312 v318 v321 v322) (R0Src.r0_o7_src.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322)) (R0Tgt.r0_o7_tgt.step (.bb1 v296 v302 v305 v306 v312 v318 v321 v322))
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb34 (m : Mem) (v401 : Val 1) (v402 a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v108 v114 : Val 32) (v170 : PtrVal) (v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233 : (Vec 8 64)) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G1.step (.bb34 m v401 v402 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233))
      (Cand.argon2_fill_segment_avx512f.G1.step (.bb34 m v401 v402 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233)) := by
  sim_unfold
  sim_same
  sim_at v490
  cut_store (r1_o0_same v463 v469 v472 v473 v479 v485 v488 v489) (R1Src.r1_o0_src.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489)) (R1Tgt.r1_o0_tgt.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489))
  cut_store (r1_o1_same v463 v469 v472 v473 v479 v485 v488 v489) (R1Src.r1_o1_src.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489)) (R1Tgt.r1_o1_tgt.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489))
  cut_store (r1_o2_same v463 v469 v472 v473 v479 v485 v488 v489) (R1Src.r1_o2_src.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489)) (R1Tgt.r1_o2_tgt.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489))
  cut_store (r1_o3_same v463 v469 v472 v473 v479 v485 v488 v489) (R1Src.r1_o3_src.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489)) (R1Tgt.r1_o3_tgt.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489))
  cut_store (r1_o4_same v463 v469 v472 v473 v479 v485 v488 v489) (R1Src.r1_o4_src.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489)) (R1Tgt.r1_o4_tgt.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489))
  cut_store (r1_o5_same v463 v469 v472 v473 v479 v485 v488 v489) (R1Src.r1_o5_src.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489)) (R1Tgt.r1_o5_tgt.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489))
  cut_store (r1_o6_same v463 v469 v472 v473 v479 v485 v488 v489) (R1Src.r1_o6_src.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489)) (R1Tgt.r1_o6_tgt.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489))
  cut_store (r1_o7_same v463 v469 v472 v473 v479 v485 v488 v489) (R1Src.r1_o7_src.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489)) (R1Tgt.r1_o7_tgt.step (.bb1 v463 v469 v472 v473 v479 v485 v488 v489))
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb35 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v108 v114 : Val 32) (v170 : PtrVal) (v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233 : (Vec 8 64)) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G2.step (.bb35 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233))
      (Cand.argon2_fill_segment_avx512f.G2.step (.bb35 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb36 (m : Mem) (a0 v8 : PtrVal) (v10 : Val 64) (v14 v15 v63 : PtrVal) (v64 v65 v66 v67 : Val 1) (v69 : PtrVal) (v73 : Val 32) (v74 v89 : PtrVal) (v90 : Val 1) (v91 : Val 32) (v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 : PtrVal) (v106 : Val 64) (v108 v114 : Val 32) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G2.step (.bb36 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114))
      (Cand.argon2_fill_segment_avx512f.G2.step (.bb36 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114)) := by
  sim_unfold
  sim_same
  sim_end

set_option maxHeartbeats 4000000 in
theorem step_bb37 (m : Mem) (v8 : PtrVal) :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.G2.step (.bb37 m v8))
      (Cand.argon2_fill_segment_avx512f.G2.step (.bb37 m v8)) := by
  sim_unfold
  sim_same
  sim_end

/-- Blocks that are the same block step to the same block, or return the same result and memory. -/
theorem step_sim (b : Base.argon2_fill_segment_avx512f.Block) (b' : Cand.argon2_fill_segment_avx512f.Block) (h : same b = b') :
    Outcome.Sim (Next.Rel (fun b b' => same b = b') Eq) (Base.argon2_fill_segment_avx512f.step b) (Cand.argon2_fill_segment_avx512f.step b') := by
  subst h
  cases b with
  | g0 b =>
    cases b with
    | bb3 m a0 a1 a2 => exact step_bb3 m a0 a1 a2
    | bb4 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 => exact step_bb4 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15
    | bb5 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17 => exact step_bb5 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17
    | bb6 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17 => exact step_bb6 m a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17
    | bb7 m a0 a2 v8 v9 v10 v11 v12 v14 v15 v25 => exact step_bb7 m a0 a2 v8 v9 v10 v11 v12 v14 v15 v25
    | bb8 m v28 a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17 => exact step_bb8 m v28 a0 a1 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v17
    | bb9 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 => exact step_bb9 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44
    | bb10 m v48 v49 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 => exact step_bb10 m v48 v49 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47
    | bb11 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v49 v50 => exact step_bb11 m a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v49 v50
    | bb12 m v53 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v50 => exact step_bb12 m v53 a0 a2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v28 v44 v47 v48 v50
    | bb13 m v61 a0 a2 v3 v4 v5 v8 v9 v10 v11 v12 v14 v15 v28 => exact step_bb13 m v61 a0 a2 v3 v4 v5 v8 v9 v10 v11 v12 v14 v15 v28
    | bb14 m v62 v63 v64 a0 a2 v8 v9 v10 v11 v12 v14 v15 => exact step_bb14 m v62 v63 v64 a0 a2 v8 v9 v10 v11 v12 v14 v15
    | bb15 m a0 v8 v10 v12 v14 v15 v62 v63 v64 v65 v66 v67 v68 v69 v73 v74 v77 v82 => exact step_bb15 m a0 v8 v10 v12 v14 v15 v62 v63 v64 v65 v66 v67 v68 v69 v73 v74 v77 v82
    | bb16 m v106 v107 v108 v109 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 => exact step_bb16 m v106 v107 v108 v109 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104
    | bb17 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 => exact step_bb17 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114
    | bb18 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 => exact step_bb18 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114
  | g1 b =>
    cases b with
    | bb19 m v121 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 => exact step_bb19 m v121 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114
    | bb20 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129 => exact step_bb20 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129
    | bb21 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 => exact step_bb21 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128
    | bb22 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129 => exact step_bb22 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129
    | bb23 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132 => exact step_bb23 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132
    | bb24 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132 => exact step_bb24 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 v132
    | bb25 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129 => exact step_bb25 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v129
    | bb26 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 => exact step_bb26 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128
    | bb27 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 => exact step_bb27 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128
    | bb28 m v145 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 => exact step_bb28 m v145 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128
    | bb29 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v146 => exact step_bb29 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v107 v108 v110 v114 v122 v128 v146
    | bb30 m v149 v150 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128 => exact step_bb30 m v149 v150 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v110 v114 v122 v128
    | bb31 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170 => exact step_bb31 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170
    | bb32 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170 => exact step_bb32 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v168 v170
    | bb33 m v234 v235 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233 => exact step_bb33 m v234 v235 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233
    | bb34 m v401 v402 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233 => exact step_bb34 m v401 v402 a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233
  | g2 b =>
    cases b with
    | bb35 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233 => exact step_bb35 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 v170 v173 v177 v181 v185 v189 v193 v197 v201 v205 v209 v213 v217 v221 v225 v229 v233
    | bb36 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114 => exact step_bb36 m a0 v8 v10 v14 v15 v63 v64 v65 v66 v67 v69 v73 v74 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v106 v108 v114
    | bb37 m v8 => exact step_bb37 m v8

/-- They're under the loops' promise together. -/
theorem promise_eq (b : Base.argon2_fill_segment_avx512f.Block) (b' : Cand.argon2_fill_segment_avx512f.Block) (h : same b = b') :
    Cand.argon2_fill_segment_avx512f.promise b' = Base.argon2_fill_segment_avx512f.promise b := by
  subst h
  rcases b with b | b | b <;> cases b <;> rfl

/-- **The candidate's `argon2_fill_segment_avx512f` does what the baseline's does,** for every argument and memory:
where the baseline's returns, the candidate's returns with the same memory, and where the baseline's never finishes,
neither does the candidate's. Where the baseline's is undefined or the model has no answer for it, there's no
claim. -/
theorem argon2_fill_segment_avx512f_same (a0 : PtrVal) (a1 a2 : Val 64) (m : Mem) :
    Outcome.Sim Eq (Base.argon2_fill_segment_avx512f a0 a1 a2 m) (Cand.argon2_fill_segment_avx512f a0 a1 a2 m) := by
  simp only [Base.argon2_fill_segment_avx512f, Cand.argon2_fill_segment_avx512f]
  refine Mono.noundefPtr (Refine.Reflexive.refl _) ?_
  rw [Mem.call_eq, Mem.call_eq]
  refine Outcome.Sim.andThen (r := Eq) ?_ fun x y h => by subst h; exact Outcome.Sim.refl (fun _ => rfl) _
  simp only [Mem.withFrame]
  refine Outcome.Sim.andThen (r := Eq) ?_ fun x y h => by subst h; exact Outcome.Sim.refl (fun _ => rfl) _
  exact Outcome.Sim.promised step_sim promise_eq rfl

/-- **libsodium's `argon2_fill_segment_avx512f` with rows A, C and D rotated refines the one with rows B, C and D
rotated, as clang compiled both,** for every argument, on every memory the model has an answer for. -/
theorem argon2_fill_segment_avx512f :
    Refines (fun a0 a1 a2 m => (Base.argon2_fill_segment_avx512f a0 a1 a2 m).answered)
      Cand.argon2_fill_segment_avx512f :=
  fun a0 a1 a2 m => (Refine.answered_iff _ _).2
    ((argon2_fill_segment_avx512f_same a0 a1 a2 m).mono fun x y h => by
      subst h; exact ⟨Refine.unit _ _, Mem.le.refl _⟩)

#print axioms argon2_fill_segment_avx512f_same
#print axioms argon2_fill_segment_avx512f

end FillSegment
