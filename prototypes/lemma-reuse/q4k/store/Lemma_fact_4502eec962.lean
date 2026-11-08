import Vnni

open IRLean Llama.Vnni

/-! Saved by prototypes/lemma-reuse/q4k.py. -/

namespace LemmaReuse.Store

/-- Nibbles, of how s00's `v239` is computed. -/
theorem fact_4502eec962 (p0 : (Vec 4 64)) (p1 : (Vec 4 64)) :
    Nibbles (Vec.split 32 8 4 (Vec.shuffle 8 (Vec.map2 (fun a b => Val.and a b) (Vec.split 8 32 2 p0) #v[(some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32)]) (Vec.map2 (fun a b => Val.and a b) (Vec.split 8 32 2 p1) #v[(some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32)]) #[some 0, some 8, some 2, some 10, some 4, some 12, some 6, some 14])) := by
  vnni_facts

end LemmaReuse.Store
