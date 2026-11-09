import Vnni

open IRLean Llama.Vnni

/-! Saved by prototypes/lemma-reuse/q4k.py. -/

namespace LemmaReuse.Store

/-- Nibbles, of how s00's `v245` is computed. -/
theorem fact_60cbe19736 (p0 : (Vec 4 64)) (p1 : (Vec 4 64)) :
    Nibbles (Vec.split 32 8 4 (Vec.shuffle 8 (Vec.map2 (fun a b => Val.and a b) (Vec.split 8 32 2 p0) #v[(some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32)]) (Vec.map2 (fun a b => Val.and a b) (Vec.split 8 32 2 p1) #v[(some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32)]) #[some 1, some 9, some 3, some 11, some 5, some 13, some 7, some 15])) := by
  vnni_facts

end LemmaReuse.Store
