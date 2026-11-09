import Std.Tactic.BVDecide

/-! Saved by prototypes/lemma-reuse/lemmas.py. -/

namespace LemmaReuse.Store

/-- 4 fields of 8 bits, each at most 127, added without carrying. -/
theorem step_baa1347fcb {x0 x1 x2 x3 : BitVec 8} (_h0 : x0 ≤ 127#8) (_h1 : x1 ≤ 127#8) (_h2 : x2 ≤ 127#8) (_h3 : x3 ≤ 127#8) :
    ((x3 ++ x2 ++ x1 ++ x0) >>> 16#32) + (x3 ++ x2 ++ x1 ++ x0) =
      x3 ++ x2 ++ (x3 + x1) ++ (x2 + x0) := by
  bv_decide (config := { timeout := 60 })

end LemmaReuse.Store
