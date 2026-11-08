import Count

/-! Saved by prototypes/lemma-reuse/lemmas.py. -/

namespace LemmaReuse.Store

/-- At 64 bits, each 8-bit field holds its count of set bits. -/
theorem layer_d9d842756f (a : BitVec 64) :
    ((((((a - ((a >>> 1#64) &&& 6148914691236517205#64)) >>> 2#64) &&& 3689348814741910323#64) + ((a - ((a >>> 1#64) &&& 6148914691236517205#64)) &&& 3689348814741910323#64)) >>> 4#64) + ((((a - ((a >>> 1#64) &&& 6148914691236517205#64)) >>> 2#64) &&& 3689348814741910323#64) + ((a - ((a >>> 1#64) &&& 6148914691236517205#64)) &&& 3689348814741910323#64))) &&& 1085102592571150095#64 =
      LemmaReuse.field a 8 7 ++ LemmaReuse.field a 8 6 ++ LemmaReuse.field a 8 5 ++ LemmaReuse.field a 8 4 ++ LemmaReuse.field a 8 3 ++ LemmaReuse.field a 8 2 ++ LemmaReuse.field a 8 1 ++ LemmaReuse.field a 8 0 := by
  simp only [LemmaReuse.field, Nat.reduceMul]
  bv_decide (config := { timeout := 60 })

end LemmaReuse.Store
