import Count

/-! Saved by prototypes/lemma-reuse/lemmas.py. -/

namespace LemmaReuse.Store

/-- At 128 bits, each 8-bit field holds its count of set bits. -/
theorem layer_0ff6fe9e15 (a : BitVec 128) :
    ((((((a - ((a >>> 1#128) &&& 113427455640312821154458202477256070485#128)) >>> 2#128) &&& 68056473384187692692674921486353642291#128) + ((a - ((a >>> 1#128) &&& 113427455640312821154458202477256070485#128)) &&& 68056473384187692692674921486353642291#128)) >>> 4#128) + ((((a - ((a >>> 1#128) &&& 113427455640312821154458202477256070485#128)) >>> 2#128) &&& 68056473384187692692674921486353642291#128) + ((a - ((a >>> 1#128) &&& 113427455640312821154458202477256070485#128)) &&& 68056473384187692692674921486353642291#128))) &&& 20016609818878733144904388672456953615#128 =
      LemmaReuse.field a 8 15 ++ LemmaReuse.field a 8 14 ++ LemmaReuse.field a 8 13 ++ LemmaReuse.field a 8 12 ++ LemmaReuse.field a 8 11 ++ LemmaReuse.field a 8 10 ++ LemmaReuse.field a 8 9 ++ LemmaReuse.field a 8 8 ++ LemmaReuse.field a 8 7 ++ LemmaReuse.field a 8 6 ++ LemmaReuse.field a 8 5 ++ LemmaReuse.field a 8 4 ++ LemmaReuse.field a 8 3 ++ LemmaReuse.field a 8 2 ++ LemmaReuse.field a 8 1 ++ LemmaReuse.field a 8 0 := by
  simp only [LemmaReuse.field, Nat.reduceMul]
  bv_decide (config := { timeout := 60 })

end LemmaReuse.Store
