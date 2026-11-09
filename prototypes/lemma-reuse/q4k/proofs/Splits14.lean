import Vnni
import S14Src
import S14Tgt
import Lemma_core_25cc0c39f5
import Lemma_fact_3355f82c98
import Lemma_fact_45defd144e
import Lemma_fact_2f9dda90a0

open IRLean Llama.Vnni

/-- %1411 of `ggml_gemm_q4_K_8x8_q8_K`, rewritten, is what clang's IR computes. The proof tests/llama.py writes for it, continued with lemmas from the store. -/
theorem s14_same (v938 : (Vec 8 32)) (v940 : (Vec 8 32)) (v954 : (Vec 8 32)) (v956 : (Vec 8 32)) (v1141 : (Vec 8 32)) (v942 : (Vec 8 32)) (v944 : (Vec 8 32)) (v958 : (Vec 8 32)) (v960 : (Vec 8 32)) (v1145 : (Vec 8 32)) (v934 : (Vec 8 32)) (v936 : (Vec 8 32)) (v950 : (Vec 8 32)) (v952 : (Vec 8 32)) (v1137 : (Vec 8 32)) (v930 : (Vec 8 32)) (v932 : (Vec 8 32)) (v946 : (Vec 8 32)) (v948 : (Vec 8 32)) (v1133 : (Vec 8 32)) (v1045 : (Vec 2 32)) (v1040 : Val 32) (v1046 : Val 32) (v1047 : Val 32) (v1083 : (Vec 2 32)) (v1078 : Val 32) (v1084 : Val 32) (v1085 : Val 32) :
    S14Tgt.s14_tgt v938 v940 v954 v956 v1141 v942 v944 v958 v960 v1145 v934 v936 v950 v952 v1137 v930 v932 v946 v948 v1133 v1045 v1040 v1046 v1047 v1083 v1078 v1084 v1085 = S14Src.s14_src v938 v940 v954 v956 v1141 v942 v944 v958 v960 v1145 v934 v936 v950 v952 v1137 v930 v932 v946 v948 v1133 v1045 v1040 v1046 v1047 v1083 v1078 v1084 v1085 := by
  unfold S14Tgt.s14_tgt S14Src.s14_src
  rw [run, run]
  simp only [S14Tgt.s14_tgt.step, S14Src.s14_src.step, ret, Outcome.ok]
  refine congrArg (fun x => some (Except.ok x)) ?_
  exact LemmaReuse.Store.core_25cc0c39f5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LemmaReuse.Store.fact_3355f82c98 v938 v940 v954 v956) (LemmaReuse.Store.fact_3355f82c98 v942 v944 v958 v960) (LemmaReuse.Store.fact_3355f82c98 v934 v936 v950 v952) (LemmaReuse.Store.fact_3355f82c98 v930 v932 v946 v948) (LemmaReuse.Store.fact_45defd144e v942 v944 v958 v960) (LemmaReuse.Store.fact_45defd144e v938 v940 v954 v956) (LemmaReuse.Store.fact_45defd144e v934 v936 v950 v952) (LemmaReuse.Store.fact_45defd144e v930 v932 v946 v948) (LemmaReuse.Store.fact_2f9dda90a0 v1045 v1040 v1046 v1047 v1083 v1078 v1084 v1085)
