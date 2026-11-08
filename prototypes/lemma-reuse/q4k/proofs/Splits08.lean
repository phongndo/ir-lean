import Vnni
import S08Src
import S08Tgt
import Lemma_core_25cc0c39f5
import Lemma_fact_3355f82c98
import Lemma_fact_45defd144e
import Lemma_fact_2f9dda90a0

open IRLean Llama.Vnni

/-- %652 of `ggml_gemm_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s08_same (v159 : (Vec 8 32)) (v161 : (Vec 8 32)) (v175 : (Vec 8 32)) (v177 : (Vec 8 32)) (v446 : (Vec 8 32)) (v163 : (Vec 8 32)) (v165 : (Vec 8 32)) (v179 : (Vec 8 32)) (v181 : (Vec 8 32)) (v451 : (Vec 8 32)) (v155 : (Vec 8 32)) (v157 : (Vec 8 32)) (v171 : (Vec 8 32)) (v173 : (Vec 8 32)) (v441 : (Vec 8 32)) (v151 : (Vec 8 32)) (v153 : (Vec 8 32)) (v167 : (Vec 8 32)) (v169 : (Vec 8 32)) (v436 : (Vec 8 32)) (v266 : (Vec 2 32)) (v261 : Val 32) (v267 : Val 32) (v268 : Val 32) (v304 : (Vec 2 32)) (v299 : Val 32) (v305 : Val 32) (v306 : Val 32) :
    S08Tgt.s08_tgt v159 v161 v175 v177 v446 v163 v165 v179 v181 v451 v155 v157 v171 v173 v441 v151 v153 v167 v169 v436 v266 v261 v267 v268 v304 v299 v305 v306 = S08Src.s08_src v159 v161 v175 v177 v446 v163 v165 v179 v181 v451 v155 v157 v171 v173 v441 v151 v153 v167 v169 v436 v266 v261 v267 v268 v304 v299 v305 v306 := by
  unfold S08Tgt.s08_tgt S08Src.s08_src
  rw [run, run]
  simp only [S08Tgt.s08_tgt.step, S08Src.s08_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_25cc0c39f5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_3355f82c98 v159 v161 v175 v177) (LemmaReuse.Store.fact_3355f82c98 v163 v165 v179 v181) (LemmaReuse.Store.fact_3355f82c98 v155 v157 v171 v173) (LemmaReuse.Store.fact_3355f82c98 v151 v153 v167 v169) (LemmaReuse.Store.fact_45defd144e v163 v165 v179 v181) (LemmaReuse.Store.fact_45defd144e v159 v161 v175 v177) (LemmaReuse.Store.fact_45defd144e v155 v157 v171 v173) (LemmaReuse.Store.fact_45defd144e v151 v153 v167 v169) (LemmaReuse.Store.fact_2f9dda90a0 v266 v261 v267 v268 v304 v299 v305 v306)
