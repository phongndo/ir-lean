import Vnni
import S30Src
import S30Tgt
import Lemma_core_01920f5ad1
import Lemma_fact_198e6e01d7
import Lemma_fact_be126601dd
import Lemma_fact_5e8d79da5d

open IRLean Llama.Vnni

/-- %2738 of `ggml_gemm_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s30_same (v2353 : (Vec 8 32)) (v2355 : (Vec 8 32)) (v2472 : (Vec 8 32)) (v2357 : (Vec 8 32)) (v2359 : (Vec 8 32)) (v2474 : (Vec 8 32)) (v2349 : (Vec 8 32)) (v2351 : (Vec 8 32)) (v2470 : (Vec 8 32)) (v2345 : (Vec 8 32)) (v2347 : (Vec 8 32)) (v2468 : (Vec 8 32)) (v2419 : Val 32) (v2423 : Val 32) (v2421 : Val 32) :
    S30Tgt.s30_tgt v2353 v2355 v2472 v2357 v2359 v2474 v2349 v2351 v2470 v2345 v2347 v2468 v2419 v2423 v2421 = S30Src.s30_src v2353 v2355 v2472 v2357 v2359 v2474 v2349 v2351 v2470 v2345 v2347 v2468 v2419 v2423 v2421 := by
  unfold S30Tgt.s30_tgt S30Src.s30_src
  rw [run, run]
  simp only [S30Tgt.s30_tgt.step, S30Src.s30_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_01920f5ad1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_198e6e01d7 v2353 v2355) (LemmaReuse.Store.fact_198e6e01d7 v2357 v2359) (LemmaReuse.Store.fact_198e6e01d7 v2349 v2351) (LemmaReuse.Store.fact_198e6e01d7 v2345 v2347) (LemmaReuse.Store.fact_be126601dd v2357 v2359) (LemmaReuse.Store.fact_be126601dd v2353 v2355) (LemmaReuse.Store.fact_be126601dd v2349 v2351) (LemmaReuse.Store.fact_be126601dd v2345 v2347) (LemmaReuse.Store.fact_5e8d79da5d v2419 v2423 v2421)
