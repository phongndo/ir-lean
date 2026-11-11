import IRLean.MemRefineOps

/-! A write keeps the relation only if the bytes it writes for poison allow anything. This is `llvm.memset` writing
a zero byte where the byte to set is poison, and `IRLean.Mem.le.memset`'s proof, word for word, stops at that byte:
where the source's byte is poison and the target's isn't, the source wrote 0 and the target something else.
`tests/memory_refine.sh` checks this fails, there. -/

open IRLean

/-- `Mem.memset`, with a poison byte set as 0. -/
def memsetZero (m : Mem) (p : PtrVal) (v : Val 8) (n : Val 64) : Outcome Mem :=
  match n with
  | none => Outcome.ub .poisonPointer
  | some k =>
    if k == 0#64 then Outcome.ok m else
    match m.access p k.toNat 1 with
    | .error e => Outcome.ub e
    | .ok (q, a) =>
      if a.readonly then Outcome.ub .writeToConstant else
      match m.check q a true with
      | some e => some (.error e)
      | none => Outcome.ok <| m.write q a k.toNat fun _ => .val (v.getD 0)

theorem memsetZero_mono {m m' : Mem} (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') {v v' : Val 8}
    (hv : Refine.le v v') {len len' : Val 64} (hn : Refine.le len len') :
    Outcome.Sim Refine.le (memsetZero m p v len) (memsetZero m' p' v' len') := by
  cases len with
  | none => trivial
  | some k =>
    cases hn
    simp only [memsetZero]
    split
    · exact Outcome.Sim.ok h
    · cases p with
      | none => simp only [Mem.access]; trivial
      | some q =>
        cases hp
        rcases h.access_cases (some q) k.toNat 1 with ⟨e, he, he'⟩ | ⟨q₀, a, a', ha, ha', hle⟩
        · rw [he, he']; trivial
        · simp only [ha, ha', hle.readonly, h.check hle]
          split
          · trivial
          · cases m.check q₀ a true with
            | some e => trivial
            | none =>
              refine Outcome.Sim.ok (h.write hle q₀ _ fun i => ?_)
              cases v with
              | none => trivial
              | some x => cases hv; exact Byte.le.refl _
