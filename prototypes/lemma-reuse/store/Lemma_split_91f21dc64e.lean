import Count

/-! Saved by prototypes/lemma-reuse/lemmas.py. -/

namespace LemmaReuse.Store

/-- A 32-bit population count is the sum of its 8-bit fields' counts. An instance of `LemmaReuse.cpop_fieldSum`, which holds at every width. -/
theorem split_91f21dc64e (a : BitVec 32) :
    BitVec.cpop a =
      BitVec.setWidth 32 (LemmaReuse.field a 8 0 + LemmaReuse.field a 8 1 + LemmaReuse.field a 8 2 + LemmaReuse.field a 8 3) := by
  have h := LemmaReuse.cpop_fieldSum a 8 4 32 rfl (by decide)
  simp only [LemmaReuse.fieldSum, BitVec.ofNat_eq_ofNat, BitVec.zero_add, BitVec.setWidth_eq] at h
  exact h

end LemmaReuse.Store
