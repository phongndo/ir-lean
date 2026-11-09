import Count

/-! Saved by prototypes/lemma-reuse/lemmas.py. -/

namespace LemmaReuse.Store

/-- At 32 bits, each 8-bit field holds its count of set bits. -/
theorem layer_15cdd830e1 (a : BitVec 32) :
    ((((((a - ((a >>> 1#32) &&& 1431655765#32)) >>> 2#32) &&& 858993459#32) + ((a - ((a >>> 1#32) &&& 1431655765#32)) &&& 858993459#32)) >>> 4#32) + ((((a - ((a >>> 1#32) &&& 1431655765#32)) >>> 2#32) &&& 858993459#32) + ((a - ((a >>> 1#32) &&& 1431655765#32)) &&& 858993459#32))) &&& 252645135#32 =
      LemmaReuse.field a 8 3 ++ LemmaReuse.field a 8 2 ++ LemmaReuse.field a 8 1 ++ LemmaReuse.field a 8 0 := by
  simp only [LemmaReuse.field, Nat.reduceMul]
  bv_decide (config := { timeout := 60 })

end LemmaReuse.Store
