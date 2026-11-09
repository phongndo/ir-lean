import Vnni
import S20Src
import S20Tgt
import Lemma_core_01920f5ad1
import Lemma_fact_fcc9b34b1f
import Lemma_fact_e5537fed30
import Lemma_fact_5e8d79da5d

open IRLean Llama.Vnni

/-- %2089 of `ggml_gemm_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s20_same (v1688 : (Vec 8 32)) (v1690 : (Vec 8 32)) (v1879 : (Vec 8 32)) (v1692 : (Vec 8 32)) (v1694 : (Vec 8 32)) (v1882 : (Vec 8 32)) (v1684 : (Vec 8 32)) (v1686 : (Vec 8 32)) (v1876 : (Vec 8 32)) (v1680 : (Vec 8 32)) (v1682 : (Vec 8 32)) (v1873 : (Vec 8 32)) (v1737 : Val 32) (v1741 : Val 32) (v1739 : Val 32) :
    S20Tgt.s20_tgt v1688 v1690 v1879 v1692 v1694 v1882 v1684 v1686 v1876 v1680 v1682 v1873 v1737 v1741 v1739 = S20Src.s20_src v1688 v1690 v1879 v1692 v1694 v1882 v1684 v1686 v1876 v1680 v1682 v1873 v1737 v1741 v1739 := by
  unfold S20Tgt.s20_tgt S20Src.s20_src
  rw [run, run]
  simp only [S20Tgt.s20_tgt.step, S20Src.s20_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_01920f5ad1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_fcc9b34b1f v1688 v1690) (LemmaReuse.Store.fact_fcc9b34b1f v1692 v1694) (LemmaReuse.Store.fact_fcc9b34b1f v1684 v1686) (LemmaReuse.Store.fact_fcc9b34b1f v1680 v1682) (LemmaReuse.Store.fact_e5537fed30 v1692 v1694) (LemmaReuse.Store.fact_e5537fed30 v1688 v1690) (LemmaReuse.Store.fact_e5537fed30 v1684 v1686) (LemmaReuse.Store.fact_e5537fed30 v1680 v1682) (LemmaReuse.Store.fact_5e8d79da5d v1737 v1741 v1739)
