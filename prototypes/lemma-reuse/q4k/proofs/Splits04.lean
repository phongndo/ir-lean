import Vnni
import S04Src
import S04Tgt
import Lemma_core_25cc0c39f5
import Lemma_fact_1de73dfe1c
import Lemma_fact_2de38c123b
import Lemma_fact_2f9dda90a0

open IRLean Llama.Vnni

/-- %648 of `ggml_gemm_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s04_same (v159 : (Vec 8 32)) (v161 : (Vec 8 32)) (v175 : (Vec 8 32)) (v177 : (Vec 8 32)) (v426 : (Vec 8 32)) (v163 : (Vec 8 32)) (v165 : (Vec 8 32)) (v179 : (Vec 8 32)) (v181 : (Vec 8 32)) (v431 : (Vec 8 32)) (v155 : (Vec 8 32)) (v157 : (Vec 8 32)) (v171 : (Vec 8 32)) (v173 : (Vec 8 32)) (v421 : (Vec 8 32)) (v151 : (Vec 8 32)) (v153 : (Vec 8 32)) (v167 : (Vec 8 32)) (v169 : (Vec 8 32)) (v416 : (Vec 8 32)) (v247 : (Vec 2 32)) (v242 : Val 32) (v248 : Val 32) (v249 : Val 32) (v285 : (Vec 2 32)) (v280 : Val 32) (v286 : Val 32) (v287 : Val 32) :
    S04Tgt.s04_tgt v159 v161 v175 v177 v426 v163 v165 v179 v181 v431 v155 v157 v171 v173 v421 v151 v153 v167 v169 v416 v247 v242 v248 v249 v285 v280 v286 v287 = S04Src.s04_src v159 v161 v175 v177 v426 v163 v165 v179 v181 v431 v155 v157 v171 v173 v421 v151 v153 v167 v169 v416 v247 v242 v248 v249 v285 v280 v286 v287 := by
  unfold S04Tgt.s04_tgt S04Src.s04_src
  rw [run, run]
  simp only [S04Tgt.s04_tgt.step, S04Src.s04_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_25cc0c39f5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_1de73dfe1c v159 v161 v175 v177) (LemmaReuse.Store.fact_1de73dfe1c v163 v165 v179 v181) (LemmaReuse.Store.fact_1de73dfe1c v155 v157 v171 v173) (LemmaReuse.Store.fact_1de73dfe1c v151 v153 v167 v169) (LemmaReuse.Store.fact_2de38c123b v163 v165 v179 v181) (LemmaReuse.Store.fact_2de38c123b v159 v161 v175 v177) (LemmaReuse.Store.fact_2de38c123b v155 v157 v171 v173) (LemmaReuse.Store.fact_2de38c123b v151 v153 v167 v169) (LemmaReuse.Store.fact_2f9dda90a0 v247 v242 v248 v249 v285 v280 v286 v287)
