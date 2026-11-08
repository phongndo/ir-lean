import Std.Tactic.BVDecide

/-! Saved by prototypes/lemma-reuse/lemmas.py. -/

namespace LemmaReuse.Store

/-- 8 fields of 8 bits, each at most 127, added without carrying. -/
theorem step_6934d83747 {x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8} (_h0 : x0 ≤ 127#8) (_h1 : x1 ≤ 127#8) (_h2 : x2 ≤ 127#8) (_h3 : x3 ≤ 127#8) (_h4 : x4 ≤ 127#8) (_h5 : x5 ≤ 127#8) (_h6 : x6 ≤ 127#8) (_h7 : x7 ≤ 127#8) :
    BitVec.setWidth 32 (((x7 ++ x6 ++ x5 ++ x4 ++ x3 ++ x2 ++ x1 ++ x0) >>> 32#64) + (x7 ++ x6 ++ x5 ++ x4 ++ x3 ++ x2 ++ x1 ++ x0)) =
      (x7 + x3) ++ (x6 + x2) ++ (x5 + x1) ++ (x4 + x0) := by
  bv_decide (config := { timeout := 60 })

end LemmaReuse.Store
