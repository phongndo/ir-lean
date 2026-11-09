import Vnni
import S26Src
import S26Tgt
import Lemma_core_01920f5ad1
import Lemma_fact_fcc9b34b1f
import Lemma_fact_e5537fed30
import Lemma_fact_5e8d79da5d

open IRLean Llama.Vnni

/-- %2732 of `ggml_gemm_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s26_same (v2353 : (Vec 8 32)) (v2355 : (Vec 8 32)) (v2464 : (Vec 8 32)) (v2357 : (Vec 8 32)) (v2359 : (Vec 8 32)) (v2466 : (Vec 8 32)) (v2349 : (Vec 8 32)) (v2351 : (Vec 8 32)) (v2462 : (Vec 8 32)) (v2345 : (Vec 8 32)) (v2347 : (Vec 8 32)) (v2460 : (Vec 8 32)) (v2402 : Val 32) (v2406 : Val 32) (v2404 : Val 32) :
    S26Tgt.s26_tgt v2353 v2355 v2464 v2357 v2359 v2466 v2349 v2351 v2462 v2345 v2347 v2460 v2402 v2406 v2404 = S26Src.s26_src v2353 v2355 v2464 v2357 v2359 v2466 v2349 v2351 v2462 v2345 v2347 v2460 v2402 v2406 v2404 := by
  unfold S26Tgt.s26_tgt S26Src.s26_src
  rw [run, run]
  simp only [S26Tgt.s26_tgt.step, S26Src.s26_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_01920f5ad1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_fcc9b34b1f v2353 v2355) (LemmaReuse.Store.fact_fcc9b34b1f v2357 v2359) (LemmaReuse.Store.fact_fcc9b34b1f v2349 v2351) (LemmaReuse.Store.fact_fcc9b34b1f v2345 v2347) (LemmaReuse.Store.fact_e5537fed30 v2357 v2359) (LemmaReuse.Store.fact_e5537fed30 v2353 v2355) (LemmaReuse.Store.fact_e5537fed30 v2349 v2351) (LemmaReuse.Store.fact_e5537fed30 v2345 v2347) (LemmaReuse.Store.fact_5e8d79da5d v2402 v2406 v2404)
