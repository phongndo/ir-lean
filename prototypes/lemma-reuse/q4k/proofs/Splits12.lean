import Vnni
import S12Src
import S12Tgt
import Lemma_core_25cc0c39f5
import Lemma_fact_1de73dfe1c
import Lemma_fact_2de38c123b
import Lemma_fact_2f9dda90a0

open IRLean Llama.Vnni

/-- %1408 of `ggml_gemm_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s12_same (v938 : (Vec 8 32)) (v940 : (Vec 8 32)) (v954 : (Vec 8 32)) (v956 : (Vec 8 32)) (v1125 : (Vec 8 32)) (v942 : (Vec 8 32)) (v944 : (Vec 8 32)) (v958 : (Vec 8 32)) (v960 : (Vec 8 32)) (v1129 : (Vec 8 32)) (v934 : (Vec 8 32)) (v936 : (Vec 8 32)) (v950 : (Vec 8 32)) (v952 : (Vec 8 32)) (v1121 : (Vec 8 32)) (v930 : (Vec 8 32)) (v932 : (Vec 8 32)) (v946 : (Vec 8 32)) (v948 : (Vec 8 32)) (v1117 : (Vec 8 32)) (v1026 : (Vec 2 32)) (v1021 : Val 32) (v1027 : Val 32) (v1028 : Val 32) (v1064 : (Vec 2 32)) (v1059 : Val 32) (v1065 : Val 32) (v1066 : Val 32) :
    S12Tgt.s12_tgt v938 v940 v954 v956 v1125 v942 v944 v958 v960 v1129 v934 v936 v950 v952 v1121 v930 v932 v946 v948 v1117 v1026 v1021 v1027 v1028 v1064 v1059 v1065 v1066 = S12Src.s12_src v938 v940 v954 v956 v1125 v942 v944 v958 v960 v1129 v934 v936 v950 v952 v1121 v930 v932 v946 v948 v1117 v1026 v1021 v1027 v1028 v1064 v1059 v1065 v1066 := by
  unfold S12Tgt.s12_tgt S12Src.s12_src
  rw [run, run]
  simp only [S12Tgt.s12_tgt.step, S12Src.s12_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_25cc0c39f5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_1de73dfe1c v938 v940 v954 v956) (LemmaReuse.Store.fact_1de73dfe1c v942 v944 v958 v960) (LemmaReuse.Store.fact_1de73dfe1c v934 v936 v950 v952) (LemmaReuse.Store.fact_1de73dfe1c v930 v932 v946 v948) (LemmaReuse.Store.fact_2de38c123b v942 v944 v958 v960) (LemmaReuse.Store.fact_2de38c123b v938 v940 v954 v956) (LemmaReuse.Store.fact_2de38c123b v934 v936 v950 v952) (LemmaReuse.Store.fact_2de38c123b v930 v932 v946 v948) (LemmaReuse.Store.fact_2f9dda90a0 v1026 v1021 v1027 v1028 v1064 v1059 v1065 v1066)
