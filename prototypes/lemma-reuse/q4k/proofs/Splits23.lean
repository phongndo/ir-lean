import Vnni
import S23Src
import S23Tgt
import Lemma_core_01920f5ad1
import Lemma_fact_739babaa5b
import Lemma_fact_167b0d9f10
import Lemma_fact_cfa7dec569

open IRLean Llama.Vnni

/-- %2092 of `ggml_gemm_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s23_same (v1688 : (Vec 8 32)) (v1690 : (Vec 8 32)) (v1891 : (Vec 8 32)) (v1692 : (Vec 8 32)) (v1694 : (Vec 8 32)) (v1894 : (Vec 8 32)) (v1684 : (Vec 8 32)) (v1686 : (Vec 8 32)) (v1888 : (Vec 8 32)) (v1680 : (Vec 8 32)) (v1682 : (Vec 8 32)) (v1885 : (Vec 8 32)) (v1754 : Val 32) (v1758 : Val 32) (v1756 : Val 32) :
    S23Tgt.s23_tgt v1688 v1690 v1891 v1692 v1694 v1894 v1684 v1686 v1888 v1680 v1682 v1885 v1754 v1758 v1756 = S23Src.s23_src v1688 v1690 v1891 v1692 v1694 v1894 v1684 v1686 v1888 v1680 v1682 v1885 v1754 v1758 v1756 := by
  unfold S23Tgt.s23_tgt S23Src.s23_src
  rw [run, run]
  simp only [S23Tgt.s23_tgt.step, S23Src.s23_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_01920f5ad1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_739babaa5b v1688 v1690) (LemmaReuse.Store.fact_739babaa5b v1692 v1694) (LemmaReuse.Store.fact_739babaa5b v1684 v1686) (LemmaReuse.Store.fact_739babaa5b v1680 v1682) (LemmaReuse.Store.fact_167b0d9f10 v1692 v1694) (LemmaReuse.Store.fact_167b0d9f10 v1688 v1690) (LemmaReuse.Store.fact_167b0d9f10 v1684 v1686) (LemmaReuse.Store.fact_167b0d9f10 v1680 v1682) (LemmaReuse.Store.fact_cfa7dec569 v1754 v1758 v1756)
