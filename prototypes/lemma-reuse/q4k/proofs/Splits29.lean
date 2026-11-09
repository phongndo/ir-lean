import Vnni
import S29Src
import S29Tgt
import Lemma_core_01920f5ad1
import Lemma_fact_c01b84b1da
import Lemma_fact_0f634a210e
import Lemma_fact_cfa7dec569

open IRLean Llama.Vnni

/-- %2736 of `ggml_gemm_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s29_same (v2353 : (Vec 8 32)) (v2355 : (Vec 8 32)) (v2464 : (Vec 8 32)) (v2357 : (Vec 8 32)) (v2359 : (Vec 8 32)) (v2466 : (Vec 8 32)) (v2349 : (Vec 8 32)) (v2351 : (Vec 8 32)) (v2462 : (Vec 8 32)) (v2345 : (Vec 8 32)) (v2347 : (Vec 8 32)) (v2460 : (Vec 8 32)) (v2402 : Val 32) (v2406 : Val 32) (v2404 : Val 32) :
    S29Tgt.s29_tgt v2353 v2355 v2464 v2357 v2359 v2466 v2349 v2351 v2462 v2345 v2347 v2460 v2402 v2406 v2404 = S29Src.s29_src v2353 v2355 v2464 v2357 v2359 v2466 v2349 v2351 v2462 v2345 v2347 v2460 v2402 v2406 v2404 := by
  unfold S29Tgt.s29_tgt S29Src.s29_src
  rw [run, run]
  simp only [S29Tgt.s29_tgt.step, S29Src.s29_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_01920f5ad1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_c01b84b1da v2353 v2355) (LemmaReuse.Store.fact_c01b84b1da v2357 v2359) (LemmaReuse.Store.fact_c01b84b1da v2349 v2351) (LemmaReuse.Store.fact_c01b84b1da v2345 v2347) (LemmaReuse.Store.fact_0f634a210e v2357 v2359) (LemmaReuse.Store.fact_0f634a210e v2353 v2355) (LemmaReuse.Store.fact_0f634a210e v2349 v2351) (LemmaReuse.Store.fact_0f634a210e v2345 v2347) (LemmaReuse.Store.fact_cfa7dec569 v2402 v2406 v2404)
