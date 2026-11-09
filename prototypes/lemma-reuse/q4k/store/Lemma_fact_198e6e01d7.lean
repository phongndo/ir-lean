import Vnni

open IRLean Llama.Vnni

/-! Saved by prototypes/lemma-reuse/q4k.py. -/

namespace LemmaReuse.Store

/-- Nibbles, of how s22's `v1817` is computed. -/
theorem fact_198e6e01d7 (p0 : (Vec 8 32)) (p1 : (Vec 8 32)) :
    Nibbles (Vec.shuffle 32 (Vec.split 32 8 2 (Vec.map2 (fun a b => Val.and a b) (Vec.map2 (fun a b => Val.lshr a b) (Vec.split 16 16 2 (Vec.shuffle 8 p0 p1 #[some 0, some 1, some 2, some 3, some 8, some 9, some 10, some 11])) #v[(some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16), (some 4#16)]) #v[(some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16), (some 3855#16)])) (HasPoison.poison : (Vec 32 8)) #[some 0, some 1, some 2, some 3, some 8, some 9, some 10, some 11, some 0, some 1, some 2, some 3, some 8, some 9, some 10, some 11, some 16, some 17, some 18, some 19, some 24, some 25, some 26, some 27, some 16, some 17, some 18, some 19, some 24, some 25, some 26, some 27]) := by
  vnni_facts

end LemmaReuse.Store
