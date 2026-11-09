import Vnni

open IRLean Llama.Vnni

/-! Saved by prototypes/lemma-reuse/q4k.py. -/

namespace LemmaReuse.Store

/-- Nibbles, of how s19's `v1841` is computed. -/
theorem fact_0f634a210e (p0 : (Vec 8 32)) (p1 : (Vec 8 32)) :
    Nibbles (Vec.shuffle 32 (Vec.split 32 8 4 (Vec.map2 (fun a b => Val.and a b) (Vec.shuffle 8 p0 p1 #[some 4, some 5, some 6, some 7, some 12, some 13, some 14, some 15]) #v[(some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32), (some 252645135#32)])) (HasPoison.poison : (Vec 32 8)) #[some 4, some 5, some 6, some 7, some 12, some 13, some 14, some 15, some 4, some 5, some 6, some 7, some 12, some 13, some 14, some 15, some 20, some 21, some 22, some 23, some 28, some 29, some 30, some 31, some 20, some 21, some 22, some 23, some 28, some 29, some 30, some 31]) := by
  vnni_facts

end LemmaReuse.Store
