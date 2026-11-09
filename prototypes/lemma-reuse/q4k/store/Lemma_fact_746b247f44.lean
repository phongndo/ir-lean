import Vnni

open IRLean Llama.Vnni

/-! Saved by prototypes/lemma-reuse/q4k.py. -/

namespace LemmaReuse.Store

/-- Nibbles, of how s01's `v309` is computed. -/
theorem fact_746b247f44 (p0 : (Vec 4 64)) (p1 : (Vec 4 64)) :
    Nibbles (Vec.split 32 8 4 (Vec.shuffle 8 (Vec.map2 (fun a b => Val.and a b) (Vec.join 8 32 2 (Vec.map2 (fun a b => Val.lshr a b) (Vec.split 16 16 4 p0) #v[(some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16)])) #v[(some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32)]) (Vec.map2 (fun a b => Val.and a b) (Vec.join 8 32 2 (Vec.map2 (fun a b => Val.lshr a b) (Vec.split 16 16 4 p1) #v[(some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16)])) #v[(some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32)]) #[some 1, some 9, some 3, some 11, some 5, some 13, some 7, some 15])) := by
  vnni_facts

end LemmaReuse.Store
