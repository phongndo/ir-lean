import Vnni
import S00Src
import S00Tgt
import Lemma_core_01920f5ad1
import Lemma_fact_60cbe19736
import Lemma_fact_4502eec962
import Lemma_fact_4ff0e38a51

open IRLean Llama.Vnni

/-- %250 of `ggml_gemv_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s00_same (v90 : (Vec 4 64)) (v92 : (Vec 4 64)) (v176 : (Vec 2 64)) (v9 : (Vec 2 64)) (v94 : (Vec 4 64)) (v96 : (Vec 4 64)) (v98 : (Vec 4 64)) (v100 : (Vec 4 64)) (v179 : (Vec 2 64)) (v102 : (Vec 4 64)) (v104 : (Vec 4 64)) (v123 : Val 32) (v127 : Val 32) (v125 : Val 32) :
    S00Tgt.s00_tgt v90 v92 v176 v9 v94 v96 v98 v100 v179 v102 v104 v123 v127 v125 = S00Src.s00_src v90 v92 v176 v9 v94 v96 v98 v100 v179 v102 v104 v123 v127 v125 := by
  unfold S00Tgt.s00_tgt S00Src.s00_src
  rw [run, run]
  simp only [S00Tgt.s00_tgt.step, S00Src.s00_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_01920f5ad1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_60cbe19736 v90 v92) (LemmaReuse.Store.fact_4502eec962 v90 v92) (LemmaReuse.Store.fact_4502eec962 v94 v96) (LemmaReuse.Store.fact_60cbe19736 v94 v96) (LemmaReuse.Store.fact_4502eec962 v98 v100) (LemmaReuse.Store.fact_60cbe19736 v98 v100) (LemmaReuse.Store.fact_4502eec962 v102 v104) (LemmaReuse.Store.fact_60cbe19736 v102 v104) (LemmaReuse.Store.fact_4ff0e38a51 v123 v127 v125)
