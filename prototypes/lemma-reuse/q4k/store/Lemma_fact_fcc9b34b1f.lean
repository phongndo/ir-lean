import Vnni

open IRLean Llama.Vnni

/-! Saved by prototypes/lemma-reuse/q4k.py. -/

namespace LemmaReuse.Store

/-- Nibbles, of how s18's `v1801` is computed. -/
theorem fact_fcc9b34b1f (p0 : (Vec 8 32)) (p1 : (Vec 8 32)) :
    Nibbles (Vec.shuffle 32 (Vec.split 32 8 4 (Vec.map2 (fun a b => Val.and a b) (Vec.shuffle 8 p0 p1 #[some 0, some 1, some 2, some 3, some 8, some 9, some 10, some 11]) #v[(some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32)])) (HasPoison.poison : (Vec 32 8)) #[some 0, some 1, some 2, some 3, some 8, some 9, some 10, some 11, some 0, some 1, some 2, some 3, some 8, some 9, some 10, some 11, some 16, some 17, some 18, some 19, some 24, some 25, some 26, some 27, some 16, some 17, some 18, some 19, some 24, some 25, some 26, some 27]) := by
  vnni_facts

end LemmaReuse.Store
