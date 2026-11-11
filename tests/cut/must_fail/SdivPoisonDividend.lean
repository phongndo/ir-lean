import IRLean.Mono

/-! `sdiv` keeps refinement because the model makes a poison dividend overflow by `-1`, as the least number would:
the dividend the target has for it might be that number. This is `sdiv` with a poison dividend that never
overflows, and the proof of `IRLean.Mono.sdiv`, word for word, stops where the target's dividend is the least number
and the divisor `-1`: the target's division is undefined, and the source's isn't. `tests/cut.sh` checks this fails,
there. -/

open IRLean Refine

/-- `Val.divOverflows`, with a poison dividend never overflowing. -/
def divOverflowsWrong (a : Val w) (y : BitVec w) : Bool :=
  match a with
  | none => false
  | some x => x.sdivOverflow y

def sdivWrong (a b : Val w) : Outcome (Val w) :=
  match b with
  | none => Outcome.ub .divByPoison
  | some y =>
    if y == 0#w then Outcome.ub .divByZero else
    if divOverflowsWrong a y then Outcome.ub .divOverflow else
    match a with
    | none => Outcome.ok none
    | some x => Outcome.ok (some (x.sdiv y))

theorem divOverflowsWrong_mono {a a' : Val w} (ha : Refine.le a a') (y : BitVec w)
    (h : divOverflowsWrong a y = false) : divOverflowsWrong a' y = false := by
  cases a with
  | some x => cases ha; exact h
  | none =>
    cases a' with
    | none => exact h
    | some x' =>
      simp only [divOverflowsWrong, beq_eq_false_iff_ne, ne_eq] at h
      simp [divOverflowsWrong, BitVec.sdivOverflow_eq, h]
