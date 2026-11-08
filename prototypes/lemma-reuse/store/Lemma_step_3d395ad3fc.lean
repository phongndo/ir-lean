import Std.Tactic.BVDecide

/-! Saved by prototypes/lemma-reuse/lemmas.py. -/

namespace LemmaReuse.Store

/-- 16 fields of 8 bits, each at most 127, added without carrying. -/
theorem step_3d395ad3fc {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : BitVec 8} (_h0 : x0 ≤ 127#8) (_h1 : x1 ≤ 127#8) (_h2 : x2 ≤ 127#8) (_h3 : x3 ≤ 127#8) (_h4 : x4 ≤ 127#8) (_h5 : x5 ≤ 127#8) (_h6 : x6 ≤ 127#8) (_h7 : x7 ≤ 127#8) (_h8 : x8 ≤ 127#8) (_h9 : x9 ≤ 127#8) (_h10 : x10 ≤ 127#8) (_h11 : x11 ≤ 127#8) (_h12 : x12 ≤ 127#8) (_h13 : x13 ≤ 127#8) (_h14 : x14 ≤ 127#8) (_h15 : x15 ≤ 127#8) :
    BitVec.setWidth 64 (((x15 ++ x14 ++ x13 ++ x12 ++ x11 ++ x10 ++ x9 ++ x8 ++ x7 ++ x6 ++ x5 ++ x4 ++ x3 ++ x2 ++ x1 ++ x0) >>> 64#128) + (x15 ++ x14 ++ x13 ++ x12 ++ x11 ++ x10 ++ x9 ++ x8 ++ x7 ++ x6 ++ x5 ++ x4 ++ x3 ++ x2 ++ x1 ++ x0)) =
      (x15 + x7) ++ (x14 + x6) ++ (x13 + x5) ++ (x12 + x4) ++ (x11 + x3) ++ (x10 + x2) ++ (x9 + x1) ++ (x8 + x0) := by
  bv_decide (config := { timeout := 60 })

end LemmaReuse.Store
