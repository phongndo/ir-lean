import Std.Tactic.BVDecide

/-! Saved by prototypes/lemma-reuse/lemmas.py. -/

namespace LemmaReuse.Store

/-- 4 fields of 8 bits, each at most 255, added without carrying. -/
theorem step_b4f1aa7047 {x0 x1 x2 x3 : BitVec 8} (_h0 : x0 ≤ 255#8) (_h1 : x1 ≤ 255#8) (_h2 : x2 ≤ 255#8) (_h3 : x3 ≤ 255#8) :
    (x3 ++ x2 ++ x1 ++ x0) &&& 255#32 =
      BitVec.setWidth 32 x0 := by
  bv_decide (config := { timeout := 60 })

end LemmaReuse.Store
