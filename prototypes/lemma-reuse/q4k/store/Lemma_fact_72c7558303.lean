import Vnni

open IRLean Llama.Vnni

/-! Saved by prototypes/lemma-reuse/q4k.py. -/

namespace LemmaReuse.Store

/-- Nibbles, of how s03's `v352` is computed. -/
theorem fact_72c7558303 (p0 : (Vec 8 32)) (p1 : (Vec 8 32)) (p2 : (Vec 8 32)) (p3 : (Vec 8 32)) :
    Nibbles (Vec.shuffle 64 (Vec.split 64 8 4 (Vec.map2 (fun a b => Val.and a b) (Vec.shuffle 16 (Vec.shuffle 16 p0 p1 #[some 4, some 5, some 6, some 7, some 12, some 13, some 14, some 15, none, none, none, none, none, none, none, none]) (Vec.shuffle 16 p2 p3 #[some 4, some 5, some 6, some 7, some 12, some 13, some 14, some 15, none, none, none, none, none, none, none, none]) #[some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7, some 16, some 17, some 18, some 19, some 20, some 21, some 22, some 23]) #v[(some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32)])) (HasPoison.poison : (Vec 64 8)) #[some 0, some 1, some 2, some 3, some 8, some 9, some 10, some 11, some 0, some 1, some 2, some 3, some 8, some 9, some 10, some 11, some 16, some 17, some 18, some 19, some 24, some 25, some 26, some 27, some 16, some 17, some 18, some 19, some 24, some 25, some 26, some 27, some 32, some 33, some 34, some 35, some 40, some 41, some 42, some 43, some 32, some 33, some 34, some 35, some 40, some 41, some 42, some 43, some 48, some 49, some 50, some 51, some 56, some 57, some 58, some 59, some 48, some 49, some 50, some 51, some 56, some 57, some 58, some 59]) := by
  vnni_facts

end LemmaReuse.Store
