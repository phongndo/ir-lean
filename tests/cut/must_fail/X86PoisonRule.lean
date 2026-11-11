import IRLean.MonoX86

/-! An x86 intrinsic keeps refinement only if a lane of its result is poison wherever a lane it reads is. This is
PCLMULQDQ with `b`'s quadword read through `getD 0`, forgetting that it may be poison, and the proof of
`IRLean.Mono.X86.pclmulqdq`, word for word, stops at that lane: where the source's quadword of `b` is poison and the
target's isn't, the two products differ. `tests/cut.sh` checks this fails, there. -/

open IRLean Mono Refine

/-- PCLMULQDQ, poison only where `a`'s quadword is. -/
def pclmulqdqForgets (imm : Nat) (a b : Vec n 64) : Vec n 64 :=
  Vector.ofFn fun i =>
    let block := 2 * (i.val / 2)
    match a.lane (block + (if imm.testBit 0 then 1 else 0)) with
    | some x =>
      some ((X86.clmul64 x ((b.lane (block + (if imm.testBit 4 then 1 else 0))).getD 0)).extractLsb'
        (64 * (i.val % 2)) 64)
    | none => none

theorem pclmulqdq_forgets_mono {imm : Nat} {a a' b b' : Vec n 64} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (pclmulqdqForgets imm a b) (pclmulqdqForgets imm a' b') := fun i => by
  simp only [pclmulqdqForgets, Fin.getElem_fin, Vector.getElem_ofFn]
  strict_lane lane ha (2 * (↑i / 2) + if imm.testBit 0 = true then 1 else 0)
  strict_lane lane hb (2 * (↑i / 2) + if imm.testBit 4 = true then 1 else 0)
  exact refl_val _
