import Vnni

open IRLean Llama.Vnni

/-! Saved by prototypes/lemma-reuse/q4k.py. -/

namespace LemmaReuse.Store

/-- Nibbles, of how s02's `v376` is computed. -/
theorem fact_2de38c123b (p0 : (Vec 8 32)) (p1 : (Vec 8 32)) (p2 : (Vec 8 32)) (p3 : (Vec 8 32)) :
    Nibbles (Vec.shuffle 64 (Vec.split 64 8 4 (Vec.map2 (fun a b => Val.and a b) (Vec.shuffle 16 (Vec.shuffle 16 p0 p1 #[some 0, some 1, some 2, some 3, some 8, some 9, some 10, some 11, none, none, none, none, none, none, none, none]) (Vec.shuffle 16 p2 p3 #[some 0, some 1, some 2, some 3, some 8, some 9, some 10, some 11, none, none, none, none, none, none, none, none]) #[some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7, some 16, some 17, some 18, some 19, some 20, some 21, some 22, some 23]) #v[(some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32)])) (HasPoison.poison : (Vec 64 8)) #[some 4, some 5, some 6, some 7, some 12, some 13, some 14, some 15, some 4, some 5, some 6, some 7, some 12, some 13, some 14, some 15, some 20, some 21, some 22, some 23, some 28, some 29, some 30, some 31, some 20, some 21, some 22, some 23, some 28, some 29, some 30, some 31, some 36, some 37, some 38, some 39, some 44, some 45, some 46, some 47, some 36, some 37, some 38, some 39, some 44, some 45, some 46, some 47, some 52, some 53, some 54, some 55, some 60, some 61, some 62, some 63, some 52, some 53, some 54, some 55, some 60, some 61, some 62, some 63]) := by
  vnni_facts

end LemmaReuse.Store
