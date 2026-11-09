import Count

/-! Saved by prototypes/lemma-reuse/lemmas.py. -/

namespace LemmaReuse.Store

/-- A 128-bit population count is the sum of its 8-bit fields' counts. An instance of `LemmaReuse.cpop_fieldSum`, which holds at every width. -/
theorem split_b78ac5f9a3 (a : BitVec 128) :
    BitVec.setWidth 32 (BitVec.cpop a) =
      BitVec.setWidth 32 (LemmaReuse.field a 8 0 + LemmaReuse.field a 8 1 + LemmaReuse.field a 8 2 + LemmaReuse.field a 8 3 + LemmaReuse.field a 8 4 + LemmaReuse.field a 8 5 + LemmaReuse.field a 8 6 + LemmaReuse.field a 8 7 + LemmaReuse.field a 8 8 + LemmaReuse.field a 8 9 + LemmaReuse.field a 8 10 + LemmaReuse.field a 8 11 + LemmaReuse.field a 8 12 + LemmaReuse.field a 8 13 + LemmaReuse.field a 8 14 + LemmaReuse.field a 8 15) := by
  have h := LemmaReuse.cpop_fieldSum a 8 16 32 rfl (by decide)
  simp only [LemmaReuse.fieldSum, BitVec.ofNat_eq_ofNat, BitVec.zero_add] at h
  exact h

end LemmaReuse.Store
