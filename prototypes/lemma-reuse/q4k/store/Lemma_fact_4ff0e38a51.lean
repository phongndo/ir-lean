import Vnni

open IRLean Llama.Vnni

/-! Saved by prototypes/lemma-reuse/q4k.py. -/

namespace LemmaReuse.Store

/-- Pairs, of how s00's `v162` is computed. -/
theorem fact_4ff0e38a51 (p0 : Val 32) (p1 : Val 32) (p2 : Val 32) :
    Pairs (Vec.map (fun a => Val.zext 16 a) (Vec.shuffle 16 (Vec.split 16 8 4 (Vec.insert (Vec.insert (Vec.insert (Vec.insert (HasPoison.poison : (Vec 4 32)) (Val.and p0 (some 1061109567#32)) (some 0#64)) (Val.or (Val.and p1 (some 252645135#32)) (Val.and (Val.lshr p0 (some 2#32)) (some 808464432#32)) (disjoint := true)) (some 1#64)) (Val.and p2 (some 1061109567#32)) (some 2#64)) (Val.or (Val.and (Val.lshr p1 (some 4#32)) (some 252645135#32)) (Val.and (Val.lshr p2 (some 2#32)) (some 808464432#32)) (disjoint := true)) (some 3#64))) (HasPoison.poison : (Vec 16 8)) #[some 0, some 0, some 4, some 4, some 1, some 1, some 5, some 5, some 2, some 2, some 6, some 6, some 3, some 3, some 7, some 7])) := by
  vnni_facts

end LemmaReuse.Store
