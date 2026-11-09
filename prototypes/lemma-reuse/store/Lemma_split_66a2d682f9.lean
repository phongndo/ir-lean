import Count

/-! Saved by prototypes/lemma-reuse/lemmas.py. -/

namespace LemmaReuse.Store

/-- A 64-bit population count is the sum of its 8-bit fields' counts. An instance of `LemmaReuse.cpop_fieldSum`, which holds at every width. -/
theorem split_66a2d682f9 (a : BitVec 64) :
    BitVec.setWidth 32 (BitVec.cpop a) =
      BitVec.setWidth 32 (LemmaReuse.field a 8 0 + LemmaReuse.field a 8 1 + LemmaReuse.field a 8 2 + LemmaReuse.field a 8 3 + LemmaReuse.field a 8 4 + LemmaReuse.field a 8 5 + LemmaReuse.field a 8 6 + LemmaReuse.field a 8 7) := by
  have h := LemmaReuse.cpop_fieldSum a 8 8 32 rfl (by decide)
  simp only [LemmaReuse.fieldSum, BitVec.ofNat_eq_ofNat, BitVec.zero_add] at h
  exact h

end LemmaReuse.Store
