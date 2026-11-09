import Vnni
import S01Src
import S01Tgt
import Lemma_core_01920f5ad1
import Lemma_fact_746b247f44
import Lemma_fact_a9fed6a78f
import Lemma_fact_4ff0e38a51

open IRLean Llama.Vnni

/-- %314 of `ggml_gemv_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s01_same (v90 : (Vec 4 64)) (v92 : (Vec 4 64)) (v182 : (Vec 2 64)) (v9 : (Vec 2 64)) (v94 : (Vec 4 64)) (v96 : (Vec 4 64)) (v98 : (Vec 4 64)) (v100 : (Vec 4 64)) (v185 : (Vec 2 64)) (v102 : (Vec 4 64)) (v104 : (Vec 4 64)) (v140 : Val 32) (v144 : Val 32) (v142 : Val 32) :
    S01Tgt.s01_tgt v90 v92 v182 v9 v94 v96 v98 v100 v185 v102 v104 v140 v144 v142 = S01Src.s01_src v90 v92 v182 v9 v94 v96 v98 v100 v185 v102 v104 v140 v144 v142 := by
  unfold S01Tgt.s01_tgt S01Src.s01_src
  rw [run, run]
  simp only [S01Tgt.s01_tgt.step, S01Src.s01_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_01920f5ad1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_746b247f44 v90 v92) (LemmaReuse.Store.fact_a9fed6a78f v90 v92) (LemmaReuse.Store.fact_a9fed6a78f v94 v96) (LemmaReuse.Store.fact_746b247f44 v94 v96) (LemmaReuse.Store.fact_a9fed6a78f v98 v100) (LemmaReuse.Store.fact_746b247f44 v98 v100) (LemmaReuse.Store.fact_a9fed6a78f v102 v104) (LemmaReuse.Store.fact_746b247f44 v102 v104) (LemmaReuse.Store.fact_4ff0e38a51 v140 v144 v142)
