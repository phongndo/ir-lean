import Vnni
import S33Src
import S33Tgt
import Lemma_core_01920f5ad1
import Lemma_fact_739babaa5b
import Lemma_fact_167b0d9f10
import Lemma_fact_cfa7dec569

open IRLean Llama.Vnni

/-- %2742 of `ggml_gemm_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s33_same (v2353 : (Vec 8 32)) (v2355 : (Vec 8 32)) (v2472 : (Vec 8 32)) (v2357 : (Vec 8 32)) (v2359 : (Vec 8 32)) (v2474 : (Vec 8 32)) (v2349 : (Vec 8 32)) (v2351 : (Vec 8 32)) (v2470 : (Vec 8 32)) (v2345 : (Vec 8 32)) (v2347 : (Vec 8 32)) (v2468 : (Vec 8 32)) (v2419 : Val 32) (v2423 : Val 32) (v2421 : Val 32) :
    S33Tgt.s33_tgt v2353 v2355 v2472 v2357 v2359 v2474 v2349 v2351 v2470 v2345 v2347 v2468 v2419 v2423 v2421 = S33Src.s33_src v2353 v2355 v2472 v2357 v2359 v2474 v2349 v2351 v2470 v2345 v2347 v2468 v2419 v2423 v2421 := by
  unfold S33Tgt.s33_tgt S33Src.s33_src
  rw [run, run]
  simp only [S33Tgt.s33_tgt.step, S33Src.s33_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_01920f5ad1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_739babaa5b v2353 v2355) (LemmaReuse.Store.fact_739babaa5b v2357 v2359) (LemmaReuse.Store.fact_739babaa5b v2349 v2351) (LemmaReuse.Store.fact_739babaa5b v2345 v2347) (LemmaReuse.Store.fact_167b0d9f10 v2357 v2359) (LemmaReuse.Store.fact_167b0d9f10 v2353 v2355) (LemmaReuse.Store.fact_167b0d9f10 v2349 v2351) (LemmaReuse.Store.fact_167b0d9f10 v2345 v2347) (LemmaReuse.Store.fact_cfa7dec569 v2419 v2423 v2421)
