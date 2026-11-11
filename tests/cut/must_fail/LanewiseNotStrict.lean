import IRLean.MonoX86

/-! A lane-wise operation keeps refinement only if its function on a lane is poison where an operand is. This is PAVG
with a poison lane read as 0, as a `freeze` of each lane would, and `IRLean.Mono.map2_strict`, the lemma every
lane-wise x86 intrinsic goes through, stops at the obligation that the function is poison for poison: where the
source's lane is poison and the target's isn't, the two averages differ. `tests/cut.sh` checks this fails, there. -/

open IRLean

/-- PAVGB, with poison read as 0. -/
def pavgFrozen (a b : Vec n 8) : Vec n 8 :=
  Vec.map2
    (fun x y => some (((x.getD 0).setWidth 9 + (y.getD 0).setWidth 9 + 1) >>> 1 |>.setWidth 8))
    a b

theorem pavg_frozen_mono {a a' b b' : Vec n 8} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (pavgFrozen a b) (pavgFrozen a' b') :=
  Mono.map2_strict (by intros; rfl) (by intro a; cases a <;> rfl) ha hb
