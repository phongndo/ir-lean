import IRLean.MemRefine
import IRLean.MonoX86

/-! # The rest of memory keeps the relation

`IRLean/MemRefine.lean` proves the cut lemma's obligation, that the code after a cut keeps refinement, for loads and
stores of integers, a store of a vector, `getelementptr` with one index, `alloca`, a function's frame and its promises
about memory. This proves it for the rest of what the emitter translates, which is what a SIMD kernel needs most:

| Operation | Lemma | What it takes |
| --- | --- | --- |
| `load` of a vector | `Mem.le.loadVec`, and `Mono.loadVec` for the same memory | As `Mem.le.loadInt`: the loads are related, or the target's stops the model, where the source read poison and the target's bytes hold a pointer |
| `load` of a pointer | `Mem.le.loadPtr`, `Mono.loadPtr` | The same |
| `store` of a pointer | `Mem.le.storePtr` | A pointer stored where the source stored poison leaves bytes the source's allow |
| `getelementptr` with several indices | `Mem.le.gepSteps`, `Mono.gepSteps` | Offsets related one by one |
| `llvm.memset`, `llvm.memcpy` | `Mem.le.memset`, `Mem.le.memcpy` | Lengths, pointers and the byte related |
| `llvm.lifetime.start` and `.end` | `Mem.le.lifetime` | **The same pointer on both sides.** On poison it does nothing, and on the pointer the target has for it, it ends that allocation's life, which the source's memory doesn't allow |
| `malloc`, `free` | `Mem.le.malloc`, `Mem.le.free` | Related sizes and pointers |
| `strlen` | `Mem.le.strlen` | Related pointers |
| `initializes` | `Mem.le.addInitializes` | **The same pointer**, for the same reason as `lifetime`: on poison it adds no range |
| `returned` | `Mono.returnedInt`, `Mono.returnedArgument` | **An argument that isn't poison.** The source returning poison for a poison argument is allowed, and the target returning a value for it isn't |
| A `noalias` result | `Mem.le.noaliasResult` | **A result that isn't poison in the source**: poison passes, and the value the target has for it might not |
| `llvm.assume` with `nonnull` | `Mem.le.assumeNonnull` | Related pointers: poison stops the source's model |

`Mem.leData` is a stronger relation for code that stores refined values and loads them back, as a SIMD kernel's
accumulator does: `Mem.le`, with the same running calls, and no pointer in the target's bytes that isn't in the
source's at the same place. Under it a load keeps the relation outright, `Mem.leData.loadVec` and `loadInt`, and the
stores, `memset` and `memcpy` keep it. A store of a pointer that the source had as poison doesn't. -/

namespace IRLean

namespace Mem.le

variable {m m' : Mem} {w : Nat}

/-- An allocation replaced on both sides by ones related. -/
theorem setAlloc (h : Mem.le m m') (b : Nat) {x y : Option Alloc} (hxy : Option.Rel Alloc.le x y) :
    Mem.le (m.setAlloc b x) (m'.setAlloc b y) where
  allocs c := by
    simp only [Mem.setAlloc]
    split
    · exact hxy
    · exact h.allocs c
  next := h.next
  base := h.base
  frame := h.frame
  failAlloc := h.failAlloc
  calls := h.calls
  nextCall := h.nextCall

/-- An access through the same pointer, unfolded: where the source's succeeds, the target's does, on an allocation the
source's allows. -/
theorem access_cases (h : Mem.le m m') (p : PtrVal) (n align : Nat) :
    (∃ e, m.access p n align = .error e ∧ m'.access p n align = .error e) ∨
      ∃ q a a', m.access p n align = .ok (q, a) ∧ m'.access p n align = .ok (q, a') ∧ Alloc.le a a' := by
  have hacc := h.access p n align
  revert hacc
  cases m.access p n align with
  | error e => intro he; exact .inl ⟨e, rfl, he⟩
  | ok qa => obtain ⟨q, a⟩ := qa; rintro ⟨a', ha', hle⟩; exact .inr ⟨q, a, a', rfl, ha', hle⟩

/-! ### Loads -/

/-- **`load` of a vector keeps the relation, unless the target can't read a lane's bytes as an integer.** As
`loadInt`: where the source read a lane as a value, the target reads the same, and where the source read poison, the
target reads anything, or stops the model, if its bytes hold a pointer. -/
theorem loadVec (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') (n w align : Nat) :
    Outcome.Sim Refine.le (Mem.loadVec n w m p align) (Mem.loadVec n w m' p' align) ∨
      ∃ s, Mem.loadVec n w m' p' align = Outcome.stop s := by
  cases p with
  | none => exact .inl trivial
  | some q =>
    cases hp
    simp only [Mem.loadVec]
    rcases h.access_cases (some q) (n * (w / 8)) align with ⟨e, he, he'⟩ | ⟨q₀, a, a', ha, ha', hle⟩
    · rw [he, he']; exact .inl trivial
    · simp only [ha, ha', h.check hle]
      cases m.check q₀ a false with
      | some e => exact .inl trivial
      | none =>
        dsimp only
        -- Each side's lanes, as the loads collect them.
        generalize hL : List.map (fun (i : Nat) => (_ : Except ModelStop (Option Nat))) (List.range n) = L
        generalize hL' : List.map (fun (i : Nat) => (_ : Except ModelStop (Option Nat))) (List.range n) = L'
        have hlane : ∀ (i k : Nat), L[i]? = some (.ok (some k)) → L'[i]? = some (.ok (some k)) := by
          intro i k hk
          rw [← hL, List.getElem?_map] at hk
          rw [← hL', List.getElem?_map]
          cases hr : (List.range n)[i]? with
          | none => rw [hr] at hk; cases hk
          | some j =>
            rw [hr] at hk
            simp only [Option.map_some, Option.some.injEq] at hk ⊢
            exact collect (forall₂_map_self (fun _ => h.visible hle q₀ _) _) hk
        -- Both sides test a lane for an error the same way.
        generalize hP : (fun (l : Except ModelStop (Option Nat)) => (_ : Option ModelStop)) = P
        cases hS : L.findSome? P with
        | some e => exact .inl trivial
        | none =>
          cases hT : L'.findSome? P with
          | some e => exact .inr ⟨e, rfl⟩
          | none =>
            refine .inl (Outcome.Sim.ok fun i => ?_)
            rw [Fin.getElem_fin, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_ofFn]
            cases hi : L[i.val]? with
            | none => trivial
            | some r =>
              cases r with
              | error e => trivial
              | ok r =>
                cases r with
                | none => trivial
                | some k => rw [hlane _ _ hi]; exact Refine.refl_val _

/-- Bytes that are a whole pointer, related to others, are the others. `G` is `assemblePtr`'s test of a byte. -/
theorem whole_eq {G : Byte × Nat → Bool} (hG : ∀ b i, G (b, i) = true → ∃ r k, b = .ptr r k) :
    ∀ {bs bs' : List Byte} (k : Nat), Forall₂ Byte.le bs bs' → (bs.zipIdx k).all G = true → bs' = bs
  | _, _, _, .nil, _ => rfl
  | _, _, k, @Forall₂.cons _ _ _ c c' t t' hc ht, hall => by
    simp only [List.zipIdx_cons, List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨r, j, rfl⟩ := hG c k hall.1
    have hc' : c' = .ptr r j := hc
    rw [hc', whole_eq hG (k + 1) ht hall.2]

/-- Bytes a pointer was read from in the source read as the same pointer in the target, and zeroed ones as null. -/
theorem assemblePtr {bs bs' : List Byte} (h : Forall₂ Byte.le bs bs') {p : Ptr}
    (ha : Mem.assemblePtr bs = .ok (some p)) : Mem.assemblePtr bs' = .ok (some p) := by
  have ha0 := ha
  cases h with
  | nil => cases ha
  | @cons b b' l l' hb hl =>
    cases b with
    | ptr q j =>
      simp only [Mem.assemblePtr] at ha
      split at ha
      · rename_i hwhole
        rw [whole_eq (fun b i hb => ?_) 0 (.cons hb hl) hwhole]
        · exact ha0
        · cases b with
          | ptr r k => exact ⟨r, k, rfl⟩
          | _ => cases hb
      · cases ha
    | val x =>
      have hb' : b' = .val x := hb
      subst hb'
      simp only [Mem.assemblePtr] at ha ⊢
      revert ha
      cases hc : Mem.collect (.val x :: l) with
      | error e => intro ha; cases ha
      | ok r =>
        intro ha
        cases r with
        | none => cases ha
        | some k =>
          rw [collect (.cons (Byte.le.refl _) hl) hc]
          exact ha
    | poison =>
      revert ha
      simp only [Mem.assemblePtr, Mem.collect]
      cases Mem.collect l <;> simp
    | uninit =>
      revert ha
      simp only [Mem.assemblePtr, Mem.collect]
      cases Mem.collect l <;> simp

/-- **`load` of a pointer keeps the relation, unless the target can't read its bytes as a pointer.** -/
theorem loadPtr (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') (align : Nat) :
    Outcome.Sim Refine.le (m.loadPtr p align) (m'.loadPtr p' align) ∨
      ∃ s, m'.loadPtr p' align = Outcome.stop s := by
  cases p with
  | none => exact .inl trivial
  | some q =>
    cases hp
    simp only [Mem.loadPtr]
    rcases h.access_cases (some q) 8 align with ⟨e, he, he'⟩ | ⟨q₀, a, a', ha, ha', hle⟩
    · rw [he, he']; exact .inl trivial
    · simp only [ha, ha', h.check hle]
      cases m.check q₀ a false with
      | some e => exact .inl trivial
      | none =>
        dsimp only
        have hbytes : Forall₂ Byte.le (m.read q₀ a q₀.offset.toNat 8) (m'.read q₀ a' q₀.offset.toNat 8) :=
          forall₂_map_self (fun _ => h.visible hle q₀ _) _
        cases hs : Mem.assemblePtr (m.read q₀ a q₀.offset.toNat 8) with
        | error e => exact .inl trivial
        | ok r =>
          cases r with
          | some r => rw [assemblePtr hbytes hs]; exact .inl (Outcome.Sim.ok (Refine.Reflexive.refl _))
          | none =>
            cases Mem.assemblePtr (m'.read q₀ a' q₀.offset.toNat 8) with
            | error e => exact .inr ⟨e, rfl⟩
            | ok r' => exact .inl (Outcome.Sim.ok (Refine.ptr_none _))

/-! ### Stores, and what writes memory -/

/-- **`store` of a pointer keeps the relation.** A pointer stored where the source stored poison leaves bytes the
source's poison allows. -/
theorem storePtr (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') {v v' : PtrVal} (hv : Refine.le v v')
    (align : Nat) : Outcome.Sim Refine.le (m.storePtr p v align) (m'.storePtr p' v' align) := by
  cases p with
  | none => simp only [Mem.storePtr, Mem.access]; trivial
  | some q =>
    cases hp
    simp only [Mem.storePtr]
    rcases h.access_cases (some q) 8 align with ⟨e, he, he'⟩ | ⟨q₀, a, a', ha, ha', hle⟩
    · rw [he, he']; trivial
    · simp only [ha, ha', hle.readonly, h.check hle]
      split
      · trivial
      · cases m.check q₀ a true with
        | some e => trivial
        | none =>
          refine Outcome.Sim.ok (h.write hle q₀ 8 fun i => ?_)
          cases v with
          | none => trivial
          | some x => cases hv; exact Byte.le.refl _

/-- **`llvm.memset` keeps the relation.** A byte set where the source set poison leaves bytes poison allows. -/
theorem memset (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') {v v' : Val 8} (hv : Refine.le v v')
    {len len' : Val 64} (hn : Refine.le len len') :
    Outcome.Sim Refine.le (m.memset p v len) (m'.memset p' v' len') := by
  cases len with
  | none => trivial
  | some k =>
    cases hn
    simp only [Mem.memset]
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

/-- **`llvm.memcpy` keeps the relation:** the target copies bytes the source's allow. -/
theorem memcpy (h : Mem.le m m') {d d' s s' : PtrVal} (hd : Refine.le d d') (hs : Refine.le s s')
    {len len' : Val 64} (hn : Refine.le len len') :
    Outcome.Sim Refine.le (m.memcpy d s len) (m'.memcpy d' s' len') := by
  cases len with
  | none => trivial
  | some k =>
    cases hn
    simp only [Mem.memcpy]
    split
    · exact Outcome.Sim.ok h
    · cases d with
      | none => simp only [Mem.access]; trivial
      | some dq =>
        cases hd
        rcases h.access_cases (some dq) k.toNat 1 with ⟨e, he, he'⟩ | ⟨d₀, da, da', hda, hda', hdle⟩
        · rw [he, he']; trivial
        · cases s with
          | none => rw [hda]; simp only [Mem.access]; trivial
          | some sq =>
            cases hs
            rcases h.access_cases (some sq) k.toNat 1 with ⟨e, he, he'⟩ | ⟨s₀, sa, sa', hsa, hsa', hsle⟩
            · rw [hda, hda', he, he']; trivial
            · simp only [hda, hda', hsa, hsa', hdle.readonly, h.check hsle, h.check hdle]
              split
              · trivial
              · split
                · trivial
                · cases m.check s₀ sa false with
                  | some e => trivial
                  | none =>
                    cases m.check d₀ da true with
                    | some e => trivial
                    | none => exact Outcome.Sim.ok (h.write hdle d₀ _ fun i => h.visible hsle s₀ _)

/-- **`llvm.lifetime.start` and `.end` keep the relation, through the same pointer.** A pointer the target has for
the source's poison isn't enough: on poison the source does nothing, and the target would start or end the life of
an allocation the source's memory still has as it was. -/
theorem lifetime (h : Mem.le m m') (p : PtrVal) (alive : Bool) :
    Outcome.Sim Refine.le (m.lifetime p alive) (m'.lifetime p alive) := by
  cases p with
  | none => exact Outcome.Sim.ok h
  | some q =>
    simp only [Mem.lifetime]
    cases ha : m.allocs q.block with
    | none => rw [h.gone ha]; exact Outcome.Sim.ok h
    | some a =>
      obtain ⟨a', ha', hle⟩ := h.alloc ha
      rw [ha']
      exact Outcome.Sim.ok (h.setAlloc _ (.some ⟨hle.size, rfl, hle.heap, hle.stack, fun _ => Byte.le.refl _⟩))

/-- **`malloc` keeps the relation:** both sides give the new allocation the same number, and fail alike. -/
theorem malloc (h : Mem.le m m') {s s' : Val 64} (hs : Refine.le s s') :
    Outcome.Sim Refine.le (Mem.malloc s m) (Mem.malloc s' m') := by
  cases s with
  | none => trivial
  | some n =>
    cases hs
    have hrule : ∀ f, m'.allocatorRule f = m.allocatorRule f := fun f =>
      forall₂_findSome? (fun c d hcd => by simp only [hcd.effects]) h.calls
    simp only [Mem.malloc, h.next, h.failAlloc, hrule]
    cases m.allocatorRule (m.failAlloc m.next) with
    | some e => trivial
    | none =>
      dsimp only
      split
      · exact Outcome.Sim.ok ⟨Refine.Reflexive.refl _, ⟨h.allocs, rfl, h.base, h.frame, rfl, h.calls, h.nextCall⟩⟩
      · refine Outcome.Sim.ok ⟨Refine.Reflexive.refl _, ⟨fun b => ?_, rfl, h.base, h.frame, rfl, h.calls, h.nextCall⟩⟩
        dsimp only
        split
        · exact .some (Alloc.le.refl _)
        · exact h.allocs b

/-- **`free` keeps the relation.** -/
theorem free (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') :
    Outcome.Sim Refine.le (Mem.free p m) (Mem.free p' m') := by
  cases p with
  | none => trivial
  | some q =>
    cases hp
    have hrule : ∀ f, m'.allocatorRule f = m.allocatorRule f := fun f =>
      forall₂_findSome? (fun c d hcd => by simp only [hcd.effects]) h.calls
    have hrun : m'.isRunning = m.isRunning := funext h.isRunning
    simp only [Mem.free]
    split
    · exact Outcome.Sim.ok ⟨trivial, h⟩
    · cases ha : m.allocs q.block with
      | none => rw [h.gone ha]; trivial
      | some a =>
        obtain ⟨a', ha', hle⟩ := h.alloc ha
        simp only [ha', hle.heap, hrun, h.check hle, hrule]
        split
        · split
          · trivial
          · cases m.check q a true with
            | some e => trivial
            | none =>
              cases m.allocatorRule false with
              | some e => trivial
              | none => exact Outcome.Sim.ok ⟨trivial, h.setAlloc _ .none⟩
        · trivial

/-- `strlen`'s scan: where the source finds the end, the target finds it at the same place. -/
theorem strlenFrom (h : Mem.le m m') {a a' : Alloc} (hle : Alloc.le a a') (q : Ptr) :
    ∀ fuel o k, Mem.strlenFrom m q a fuel o = .ok k → Mem.strlenFrom m' q a' fuel o = .ok k
  | 0, _, _, hk => by cases hk
  | fuel + 1, o, k, hk => by
    have hv := h.visible hle q o
    simp only [Mem.strlenFrom] at hk ⊢
    revert hk hv
    cases m.visible q a o with
    | val b =>
      intro hk hv
      rw [show m'.visible q a' o = .val b from hv]
      dsimp only at hk ⊢
      by_cases hb : (b == 0#8) = true
      · simp only [hb, ite_true] at hk ⊢; exact hk
      · simp only [hb, Bool.false_eq_true, ite_false] at hk ⊢
        revert hk
        cases hr : Mem.strlenFrom m q a fuel (o + 1) with
        | error e => intro hk; cases hk
        | ok n' => intro hk; rw [strlenFrom h hle q fuel (o + 1) n' hr]; exact hk
    | uninit => intro hk; cases hk
    | poison => intro hk; cases hk
    | ptr _ _ => intro hk; cases hk

/-- **`strlen` keeps the relation.** -/
theorem strlen (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') :
    Outcome.Sim Refine.le (Mem.strlen p m) (Mem.strlen p' m') := by
  cases p with
  | none => trivial
  | some q =>
    cases hp
    simp only [Mem.strlen]
    cases ha : m.allocs q.block with
    | none => trivial
    | some a =>
      obtain ⟨a', ha', hle⟩ := h.alloc ha
      simp only [ha', h.check hle, hle.size]
      cases m.check q a false with
      | some e => trivial
      | none =>
        dsimp only
        cases hs : Mem.strlenFrom m q a (a.size - q.offset.toNat) q.offset.toNat with
        | error e => trivial
        | ok k =>
          rw [strlenFrom h hle q _ _ k hs]
          exact Outcome.Sim.ok ⟨Refine.refl_val _, h⟩

/-- **`initializes` keeps the relation, for the same pointer.** On poison it adds no range, and on the pointer the
target has for it, it would, which `Call.le` doesn't allow. -/
theorem addInitializes (h : Mem.le m m') (p : PtrVal) (lo hi : BitVec 64) :
    Mem.le (m.addInitializes p lo hi) (m'.addInitializes p lo hi) := by
  cases p with
  | none => exact h
  | some q =>
    simp only [Mem.addInitializes]
    have hc := h.calls
    revert hc
    cases m.calls with
    | nil => intro hc; rw [forall₂_nil_left hc]; exact h
    | cons c rest =>
      intro hc
      obtain ⟨d, rest', hd, hcd, hrest⟩ := forall₂_cons_left hc
      rw [hd]
      exact { h with
        calls := .cons ⟨hcd.id, hcd.effects, hcd.start, hcd.tracked, by rw [hcd.ranges], hcd.written,
          hcd.initialized⟩ hrest }

/-- **A `noalias` result keeps refinement, where the source's isn't poison.** The source's poison passes the check,
and the pointer the target has for it might not be new. -/
theorem noaliasResult (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') (hdef : p ≠ none) {r : α → β → Prop}
    {k : Outcome α} {k' : Outcome β} (hk : Outcome.Sim r k k') :
    Outcome.Sim r (m.noaliasResult p k) (m'.noaliasResult p' k') := by
  cases p with
  | none => exact absurd rfl hdef
  | some q =>
    cases hp
    simp only [Mem.noaliasResult]
    have hc := h.calls
    revert hc
    cases m.calls with
    | nil => intro hc; rw [forall₂_nil_left hc]; exact hk
    | cons c rest =>
      intro hc
      obtain ⟨d, rest', hd, hcd, _⟩ := forall₂_cons_left hc
      rw [hd]
      dsimp only
      have hheap : (m'.allocs q.block).any (·.heap) = (m.allocs q.block).any (·.heap) := by
        cases ha : m.allocs q.block with
        | none => rw [h.gone ha]
        | some a =>
          obtain ⟨a', ha', hle⟩ := h.alloc ha
          rw [ha']
          simp only [Option.any_some, hle.heap]
      rw [hcd.start, hheap]
      split
      · exact hk
      · trivial

/-- `llvm.assume` with a `nonnull` bundle: the layout is the same on both sides, and a poison pointer stops the
source's model. -/
theorem assumeNonnull (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') {r : α → β → Prop} {k : Outcome α}
    {k' : Outcome β} (hk : Outcome.Sim r k k') :
    Outcome.Sim r (m.assumeNonnull p k) (m'.assumeNonnull p' k') := by
  cases p with
  | none => trivial
  | some q =>
    cases hp
    simp only [Mem.assumeNonnull, h.addr]
    split
    · trivial
    · exact hk

/-! ### `getelementptr` with several indices -/

/-- **`getelementptr` with several indices keeps the relation,** offset by offset. -/
theorem gepSteps (h : Mem.le m m') {inbounds nusw nuw : Bool} :
    ∀ {p p' : PtrVal} {total total' : Val 64} {offs offs' : List (Val 64)}, Refine.le p p' →
      Refine.le total total' → Forall₂ Refine.le offs offs' →
      Refine.le (Mem.gepSteps.go m inbounds nusw nuw p total offs)
        (Mem.gepSteps.go m' inbounds nusw nuw p' total' offs')
  | _, _, _, _, _, _, hp, _, .nil => by simp only [Mem.gepSteps.go]; exact hp
  | p, p', total, total', _, _, hp, ht, @Forall₂.cons _ _ _ off off' rest rest' ho hrest => by
    simp only [Mem.gepSteps.go]
    have hadd := Mono.add (nuw := nuw) (nsw := inbounds || nusw) ht ho
    revert hadd
    cases Val.add total off nuw (inbounds || nusw) with
    | none => intro _; trivial
    | some t =>
      intro hadd
      rw [show Val.add total' off' nuw (inbounds || nusw) = some t from hadd]
      exact gepSteps h (h.gep hp ho) (Refine.refl_val _) hrest

end Mem.le

namespace Mono

/-- The same memory on both sides, for the loads a proof needs most, as `Mono.loadInt`. -/
theorem loadVec (m : Mem) {p p' : PtrVal} (hp : Refine.le p p') (n w align : Nat) :
    Outcome.Sim Refine.le (Mem.loadVec n w m p align) (Mem.loadVec n w m p' align) := by
  cases p with
  | none => trivial
  | some q => cases hp; exact Outcome.Sim.refl (fun x => Refine.Reflexive.refl x) _

theorem loadPtr (m : Mem) {p p' : PtrVal} (hp : Refine.le p p') (align : Nat) :
    Outcome.Sim Refine.le (m.loadPtr p align) (m.loadPtr p' align) := by
  cases p with
  | none => trivial
  | some q => cases hp; exact Outcome.Sim.refl (fun x => Refine.Reflexive.refl x) _

theorem gepSteps (m : Mem) {p p' : PtrVal} (hp : Refine.le p p') {offs offs' : List (Val 64)}
    (ho : Forall₂ Refine.le offs offs') {inbounds nusw nuw : Bool} :
    Refine.le (m.gepSteps p offs inbounds nusw nuw) (m.gepSteps p' offs' inbounds nusw nuw) :=
  (Mem.le.refl m).gepSteps hp (Refine.refl_val _) ho

/-- **`returned` on an integer keeps refinement, for an argument that isn't poison.** For a poison argument the source
may return poison, and the target a value, which isn't the argument. -/
theorem returnedInt {arg : Val w} (harg : arg ≠ none) {res res' : Val w} (hr : Refine.le res res')
    {r : α → β → Prop} {k : Outcome α} {k' : Outcome β} (hk : Outcome.Sim r k k') :
    Outcome.Sim r (Mem.returnedInt arg res k) (Mem.returnedInt arg res' k') := by
  simp only [Mem.returnedInt]
  cases res with
  | none =>
    cases arg with
    | none => exact absurd rfl harg
    | some x => simp only [beq_iff_eq, reduceCtorEq, ite_false]; trivial
  | some y =>
    cases hr
    split
    · exact hk
    · trivial

/-- **`returned` on a pointer keeps refinement, for an argument that isn't poison.** -/
theorem returnedArgument {arg : PtrVal} (harg : arg ≠ none) {res res' : PtrVal} (hr : Refine.le res res')
    {r : α → β → Prop} {k : Outcome α} {k' : Outcome β} (hk : Outcome.Sim r k k') :
    Outcome.Sim r (Mem.returnedArgument arg res k) (Mem.returnedArgument arg res' k') := by
  cases arg with
  | none => exact absurd rfl harg
  | some a =>
    cases res with
    | none => trivial
    | some q =>
      cases hr
      simp only [Mem.returnedArgument]
      split
      · exact hk
      · trivial

end Mono

/-! ### Memories related by their data

`Mem.le` lets a target's byte be a pointer where the source's was poison or uninitialized, and then a load in the
target can stop the model where the source's gave poison, so `Mem.le.loadInt` and `loadVec` give a disjunction that a
proof can't use. Code that only ever stores integers and vectors never makes such a byte, and `Mem.leData` says so:
`Mem.le`, with the same running calls, so that a byte a promise hides is hidden on both sides, and no pointer in the
target's bytes that isn't in the source's at the same place. Under it a load keeps refinement outright, and a store
of an integer or a vector, `memset`, `memcpy` and `lifetime` keep the relation. -/

/-- Two memories related by what their bytes hold as data: see above. -/
structure Mem.leData (m m' : Mem) : Prop where
  le : Mem.le m m'
  calls : m'.calls = m.calls
  ptr : ∀ b a a', m.allocs b = some a → m'.allocs b = some a' → ∀ i p j, a'.bytes i = .ptr p j → a.bytes i = .ptr p j

namespace Mem.leData

variable {m m' : Mem} {w : Nat}

theorem refl (m : Mem) : Mem.leData m m :=
  ⟨Mem.le.refl m, rfl, fun _ _ _ ha ha' _ _ _ hp => by rw [ha] at ha'; cases ha'; exact hp⟩

/-- Bytes collect to a number or poison exactly when none of them is a pointer. -/
theorem collect_ok_iff : ∀ bs : List Byte, (∃ r, Mem.collect bs = .ok r) ↔ ∀ b ∈ bs, ∀ p j, b ≠ .ptr p j
  | [] => by simp [Mem.collect]
  | b :: bs => by
    have ih := collect_ok_iff bs
    cases b with
    | ptr p j => simp [Mem.collect]
    | val x =>
      simp only [Mem.collect, List.mem_cons, forall_eq_or_imp, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true, true_and]
      rw [← ih]
      cases Mem.collect bs with
      | error e => simp
      | ok r => cases r <;> simp
    | poison =>
      simp only [Mem.collect, List.mem_cons, forall_eq_or_imp, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true, true_and]
      rw [← ih]
      cases Mem.collect bs <;> simp
    | uninit =>
      simp only [Mem.collect, List.mem_cons, forall_eq_or_imp, ne_eq, reduceCtorEq, not_false_eq_true,
        implies_true, true_and]
      rw [← ih]
      cases Mem.collect bs <;> simp

/-- With the same running calls, a promise hides a byte on both sides or on neither. -/
theorem unwritten (h : Mem.leData m m') {a a' : Alloc} (ha : Alloc.le a a') (q : Ptr) (o : Nat) :
    m'.unwritten q a' o = m.unwritten q a o := by
  simp only [Mem.unwritten, Mem.callAccess, h.calls, ha.readonly, ha.stack]

/-- A byte the target reads as a pointer, the source reads as the same pointer. -/
theorem visible_ptr (h : Mem.leData m m') {a a' : Alloc} (ha : Alloc.le a a') {q : Ptr}
    (hq : m.allocs q.block = some a) (hq' : m'.allocs q.block = some a') (o : Nat) {p : Ptr} {j : Nat}
    (hv : m'.visible q a' o = .ptr p j) : m.visible q a o = .ptr p j := by
  simp only [Mem.visible, h.unwritten ha] at hv ⊢
  split at hv
  · cases hv
  · rw [ite_eq_right (by assumption)]
    exact h.ptr _ _ _ hq hq' o p j hv

/-- What the target reads where the source reads integers: integers, or poison, never a pointer. -/
theorem collect_ok (h : Mem.leData m m') {a a' : Alloc} (ha : Alloc.le a a') {q : Ptr}
    (hq : m.allocs q.block = some a) (hq' : m'.allocs q.block = some a') (o n : Nat)
    (hs : ∃ r, Mem.collect (m.read q a o n) = .ok r) : ∃ r, Mem.collect (m'.read q a' o n) = .ok r := by
  rw [collect_ok_iff] at hs ⊢
  intro b hb p j hbp
  simp only [Mem.read, List.mem_map, List.mem_range] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  exact hs _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩) p j (h.visible_ptr ha hq hq' _ hbp)

/-- **`load` of a vector keeps refinement outright,** on memories related by their data. -/
theorem loadVec (h : Mem.leData m m') {p p' : PtrVal} (hp : Refine.le p p') (n w align : Nat) :
    Outcome.Sim Refine.le (Mem.loadVec n w m p align) (Mem.loadVec n w m' p' align) := by
  cases p with
  | none => trivial
  | some q =>
    cases hp
    simp only [Mem.loadVec]
    rcases h.le.access_cases (some q) (n * (w / 8)) align with ⟨e, he, he'⟩ | ⟨q₀, a, a', ha, ha', hle⟩
    · rw [he, he']; trivial
    · have hq := (Mem.access_ok_iff.1 ha).2.1
      have hq' := (Mem.access_ok_iff.1 ha').2.1
      simp only [ha, ha', h.le.check hle]
      cases m.check q₀ a false with
      | some e => trivial
      | none =>
        dsimp only
        generalize hL : List.map (fun (i : Nat) => (_ : Except ModelStop (Option Nat))) (List.range n) = L
        generalize hL' : List.map (fun (i : Nat) => (_ : Except ModelStop (Option Nat))) (List.range n) = L'
        have hlen : L'.length = L.length := by rw [← hL, ← hL']; simp
        have hval : ∀ (i k : Nat), L[i]? = some (.ok (some k)) → L'[i]? = some (.ok (some k)) := by
          intro i k hk
          rw [← hL, List.getElem?_map] at hk
          rw [← hL', List.getElem?_map]
          cases hr : (List.range n)[i]? with
          | none => rw [hr] at hk; cases hk
          | some j =>
            rw [hr] at hk
            simp only [Option.map_some, Option.some.injEq] at hk ⊢
            exact Mem.le.collect (forall₂_map_self (fun _ => h.le.visible hle q₀ _) _) hk
        have hok : ∀ (i : Nat) r, L[i]? = some (.ok r) → ∃ r', L'[i]? = some (.ok r') := by
          intro i r hk
          rw [← hL, List.getElem?_map] at hk
          rw [← hL', List.getElem?_map]
          cases hr : (List.range n)[i]? with
          | none => rw [hr] at hk; cases hk
          | some j =>
            rw [hr] at hk
            simp only [Option.map_some, Option.some.injEq] at hk ⊢
            exact h.collect_ok hle hq hq' _ _ ⟨r, hk⟩
        generalize hP : (fun (l : Except ModelStop (Option Nat)) => (_ : Option ModelStop)) = P
        have hPok : ∀ l, P l = none ↔ ∃ r, l = .ok r := by
          intro l; rw [← hP]; cases l <;> simp
        cases hS : L.findSome? P with
        | some e => trivial
        | none =>
          -- No lane of the source's holds a pointer, so none of the target's does.
          have hT : L'.findSome? P = none := by
            rw [List.findSome?_eq_none_iff] at hS ⊢
            intro l hl
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
            have hiL : i < L.length := hlen ▸ hi
            obtain ⟨r, hr⟩ := (hPok _).1 (hS _ (List.getElem_mem hiL))
            obtain ⟨r', hr'⟩ := hok i r (by rw [List.getElem?_eq_getElem hiL, hr])
            rw [List.getElem?_eq_getElem hi] at hr'
            exact (hPok _).2 ⟨r', Option.some.inj hr'⟩
          rw [hT]
          refine Outcome.Sim.ok fun i => ?_
          rw [Fin.getElem_fin, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_ofFn]
          cases hi : L[i.val]? with
          | none => trivial
          | some r =>
            cases r with
            | error e => trivial
            | ok r =>
              cases r with
              | none => trivial
              | some k => rw [hval _ _ hi]; exact Refine.refl_val _

/-- **`load` of an integer keeps refinement outright,** on memories related by their data. -/
theorem loadInt (h : Mem.leData m m') {p p' : PtrVal} (hp : Refine.le p p') (w align : Nat) :
    Outcome.Sim Refine.le (m.loadInt w p align) (m'.loadInt w p' align) := by
  cases p with
  | none => trivial
  | some q =>
    cases hp
    simp only [Mem.loadInt]
    rcases h.le.access_cases (some q) (w / 8) align with ⟨e, he, he'⟩ | ⟨q₀, a, a', ha, ha', hle⟩
    · rw [he, he']; trivial
    · have hq := (Mem.access_ok_iff.1 ha).2.1
      have hq' := (Mem.access_ok_iff.1 ha').2.1
      simp only [ha, ha', h.le.check hle]
      cases m.check q₀ a false with
      | some e => trivial
      | none =>
        dsimp only
        have hbytes : Forall₂ Byte.le (m.read q₀ a q₀.offset.toNat (w / 8))
            (m'.read q₀ a' q₀.offset.toNat (w / 8)) :=
          forall₂_map_self (fun _ => h.le.visible hle q₀ _) _
        cases hs : Mem.collect (m.read q₀ a q₀.offset.toNat (w / 8)) with
        | error e => trivial
        | ok r =>
          obtain ⟨r', hr'⟩ := h.collect_ok hle hq hq' _ _ ⟨r, hs⟩
          cases r with
          | some k => rw [Mem.le.collect hbytes hs]; exact Outcome.Sim.ok (Refine.refl_val _)
          | none => rw [hr']; cases r' <;> exact Outcome.Sim.ok (Refine.val_none _)

/-- A store's bytes, on memories related by their data, where the target's bytes are allowed and are pointers only
where the source's are the same, leave memories related by their data. -/
theorem write (h : Mem.leData m m') {q : Ptr} {a a' : Alloc} (ha : Alloc.le a a') (hq : m.allocs q.block = some a)
    (hq' : m'.allocs q.block = some a') (n : Nat) {f f' : Nat → Byte} (hf : ∀ i, Byte.le (f i) (f' i))
    (hfp : ∀ i p j, f' i = .ptr p j → f i = .ptr p j) : Mem.leData (m.write q a n f) (m'.write q a' n f') where
  le := h.le.write ha q n hf
  calls := by simp only [Mem.write, h.calls]
  ptr b c c' hc hc' i p j hp := by
    by_cases hb : b = q.block
    · subst hb
      rw [Mem.write_allocs_self] at hc hc'
      cases hc
      cases hc'
      simp only [Mem.Alloc.overlay] at hp ⊢
      split at hp
      · rw [ite_eq_left (by assumption)]; exact hfp _ _ _ hp
      · rw [ite_eq_right (by assumption)]; exact h.ptr _ _ _ hq hq' i p j hp
    · rw [Mem.write_allocs_other _ _ _ _ _ hb] at hc hc'
      exact h.ptr _ _ _ hc hc' i p j hp

theorem toLe (h : Mem.leData m m') : Mem.le m m' := h.le

/-- **`store` of an integer keeps the relation of the memories' data.** -/
theorem storeInt (h : Mem.leData m m') {p p' : PtrVal} (hp : Refine.le p p') {v v' : Val w} (hv : Refine.le v v')
    (align : Nat) : Outcome.Sim Mem.leData (m.storeInt p v align) (m'.storeInt p' v' align) := by
  cases p with
  | none => simp only [Mem.storeInt, Mem.access]; trivial
  | some q =>
    cases hp
    simp only [Mem.storeInt]
    rcases h.le.access_cases (some q) (w / 8) align with ⟨e, he, he'⟩ | ⟨q₀, a, a', ha, ha', hle⟩
    · rw [he, he']; trivial
    · have hq := (Mem.access_ok_iff.1 ha).2.1
      have hq' := (Mem.access_ok_iff.1 ha').2.1
      simp only [ha, ha', hle.readonly, h.le.check hle]
      split
      · trivial
      · cases m.check q₀ a true with
        | some e => trivial
        | none =>
          refine Outcome.Sim.ok (h.write hle hq hq' _ (fun i => ?_) (fun i p j hp => ?_))
          · cases v with
            | none => trivial
            | some x => cases hv; exact Byte.le.refl _
          · cases v' with
            | none => cases hp
            | some x => cases hp

/-- **`store` of a vector keeps the relation of the memories' data.** -/
theorem storeVec (h : Mem.leData m m') {p p' : PtrVal} (hp : Refine.le p p') {n : Nat} {v v' : Vec n w}
    (hv : Refine.le v v') (align : Nat) :
    Outcome.Sim Mem.leData (m.storeVec p v align) (m'.storeVec p' v' align) := by
  cases p with
  | none => simp only [Mem.storeVec, Mem.access]; trivial
  | some q =>
    cases hp
    simp only [Mem.storeVec]
    rcases h.le.access_cases (some q) (n * (w / 8)) align with ⟨e, he, he'⟩ | ⟨q₀, a, a', ha, ha', hle⟩
    · rw [he, he']; trivial
    · have hq := (Mem.access_ok_iff.1 ha).2.1
      have hq' := (Mem.access_ok_iff.1 ha').2.1
      simp only [ha, ha', hle.readonly, h.le.check hle]
      split
      · trivial
      · cases m.check q₀ a true with
        | some e => trivial
        | none =>
          refine Outcome.Sim.ok (h.write hle hq hq' _ (fun i => ?_) (fun i p j hp => ?_))
          · have hl := Mono.lane hv (i / (w / 8))
            revert hl
            cases Vec.lane v (i / (w / 8)) with
            | none => intro _; trivial
            | some x => intro hl; rw [(Refine.val_some _ _).1 hl]; exact Byte.le.refl _
          · revert hp
            cases Vec.lane v' (i / (w / 8)) with
            | none => intro hp; cases hp
            | some x => intro hp; cases hp

/-- **`llvm.memset` keeps the relation of the memories' data.** -/
theorem memset (h : Mem.leData m m') {p p' : PtrVal} (hp : Refine.le p p') {v v' : Val 8} (hv : Refine.le v v')
    {len len' : Val 64} (hn : Refine.le len len') :
    Outcome.Sim Mem.leData (m.memset p v len) (m'.memset p' v' len') := by
  cases len with
  | none => trivial
  | some k =>
    cases hn
    simp only [Mem.memset]
    split
    · exact Outcome.Sim.ok h
    · cases p with
      | none => simp only [Mem.access]; trivial
      | some q =>
        cases hp
        rcases h.le.access_cases (some q) k.toNat 1 with ⟨e, he, he'⟩ | ⟨q₀, a, a', ha, ha', hle⟩
        · rw [he, he']; trivial
        · have hq := (Mem.access_ok_iff.1 ha).2.1
          have hq' := (Mem.access_ok_iff.1 ha').2.1
          simp only [ha, ha', hle.readonly, h.le.check hle]
          split
          · trivial
          · cases m.check q₀ a true with
            | some e => trivial
            | none =>
              refine Outcome.Sim.ok (h.write hle hq hq' _ (fun i => ?_) (fun i p j hp => ?_))
              · cases v with
                | none => trivial
                | some x => cases hv; exact Byte.le.refl _
              · cases v' with
                | none => cases hp
                | some x => cases hp

/-- **`llvm.memcpy` keeps the relation of the memories' data:** a pointer the target copies, the source copies
too. -/
theorem memcpy (h : Mem.leData m m') {d d' s s' : PtrVal} (hd : Refine.le d d') (hs : Refine.le s s')
    {len len' : Val 64} (hn : Refine.le len len') :
    Outcome.Sim Mem.leData (m.memcpy d s len) (m'.memcpy d' s' len') := by
  cases len with
  | none => trivial
  | some k =>
    cases hn
    simp only [Mem.memcpy]
    split
    · exact Outcome.Sim.ok h
    · cases d with
      | none => simp only [Mem.access]; trivial
      | some dq =>
        cases hd
        rcases h.le.access_cases (some dq) k.toNat 1 with ⟨e, he, he'⟩ | ⟨d₀, da, da', hda, hda', hdle⟩
        · rw [he, he']; trivial
        · cases s with
          | none => rw [hda]; simp only [Mem.access]; trivial
          | some sq =>
            cases hs
            rcases h.le.access_cases (some sq) k.toNat 1 with ⟨e, he, he'⟩ | ⟨s₀, sa, sa', hsa, hsa', hsle⟩
            · rw [hda, hda', he, he']; trivial
            · have hdq := (Mem.access_ok_iff.1 hda).2.1
              have hdq' := (Mem.access_ok_iff.1 hda').2.1
              have hsq := (Mem.access_ok_iff.1 hsa).2.1
              have hsq' := (Mem.access_ok_iff.1 hsa').2.1
              simp only [hda, hda', hsa, hsa', hdle.readonly, h.le.check hsle, h.le.check hdle]
              split
              · trivial
              · split
                · trivial
                · cases m.check s₀ sa false with
                  | some e => trivial
                  | none =>
                    cases m.check d₀ da true with
                    | some e => trivial
                    | none =>
                      exact Outcome.Sim.ok (h.write hdle hdq hdq' _ (fun i => h.le.visible hsle s₀ _)
                        (fun i p j hp => h.visible_ptr hsle hsq hsq' _ hp))

/-- `llvm.lifetime.start` and `.end`, through the same pointer: the bytes become uninitialized on both sides. -/
theorem lifetime (h : Mem.leData m m') (p : PtrVal) (alive : Bool) :
    Outcome.Sim Mem.leData (m.lifetime p alive) (m'.lifetime p alive) := by
  cases p with
  | none => exact Outcome.Sim.ok h
  | some q =>
    simp only [Mem.lifetime]
    cases ha : m.allocs q.block with
    | none => rw [h.le.gone ha]; exact Outcome.Sim.ok h
    | some a =>
      obtain ⟨a', ha', hle⟩ := h.le.alloc ha
      rw [ha']
      refine Outcome.Sim.ok ⟨h.le.setAlloc _ (.some ⟨hle.size, rfl, hle.heap, hle.stack, fun _ => Byte.le.refl _⟩),
        h.calls, fun b c c' hc hc' i r j hr => ?_⟩
      simp only [Mem.setAlloc] at hc hc'
      split at hc
      · rename_i hb
        rw [ite_eq_left hb] at hc'
        cases hc'
        cases hr
      · rename_i hb
        rw [ite_eq_right hb] at hc'
        exact h.ptr _ _ _ hc hc' i r j hr

end Mem.leData

/-- `getelementptr` with several indices, as the emitter writes it. -/
theorem Mem.le.gepSteps' {m m' : Mem} (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p')
    {offs offs' : List (Val 64)} (ho : Forall₂ Refine.le offs offs') {inbounds nusw nuw : Bool} :
    Refine.le (m.gepSteps p offs inbounds nusw nuw) (m'.gepSteps p' offs' inbounds nusw nuw) :=
  h.gepSteps hp (Refine.refl_val _) ho

/-! ### Proving that two blocks' steps are related

What a whole-function proof does at each block, as `tests/cut/GhAdBlocks.lean` does for a function clang compiled:
memory's lemmas on values join `refine_mono_simd`, and `sim_mono` walks two blocks' code, which the emitter writes the
same way on both sides, instruction by instruction. -/

macro_rules
  | `(tactic| refine_mono_ext) => `(tactic| first
    | exact Mem.leData.toLe (by assumption)
    | exact Refine.unit _ _
    | refine Mem.le.gep ?_ ?_ ?_ | refine Mem.le.gepSteps' ?_ ?_ ?_ | refine Mem.le.toVal ?_ ?_
    | refine Mem.le.nonnull ?_ ?_ | refine Mem.le.aligned ?_ _ ?_ | refine Mem.le.tag _ ?_
    | exact Forall₂.nil | refine Forall₂.cons ?_ ?_)

/-- Walks two blocks' code that the emitter wrote the same way, on memories related by their data: each load, store,
`memset`, `memcpy` and `lifetime` by `Mem.leData`'s lemma, an operation that can be undefined by its `Mono` lemma,
and each branch, jump and return by `Outcome.Sim`'s. What's left is for `refine_mono_simd`, on values, and for the
proof's relation between blocks. -/
macro "sim_mono" : tactic =>
  `(tactic| repeat' (first
    | refine Outcome.Sim.andThen (Mem.leData.loadVec (by assumption) ?_ _ _ _) fun _ _ _ => ?_
    | refine Outcome.Sim.andThen (Mem.leData.loadInt (by assumption) ?_ _ _) fun _ _ _ => ?_
    | refine Outcome.Sim.andThen (Mem.leData.storeVec (by assumption) ?_ ?_ _) fun _ _ _ => ?_
    | refine Outcome.Sim.andThen (Mem.leData.storeInt (by assumption) ?_ ?_ _) fun _ _ _ => ?_
    | refine Outcome.Sim.andThen (Mem.leData.memset (by assumption) ?_ ?_ ?_) fun _ _ _ => ?_
    | refine Outcome.Sim.andThen (Mem.leData.memcpy (by assumption) ?_ ?_ ?_) fun _ _ _ => ?_
    | refine Outcome.Sim.andThen (Mem.leData.lifetime (by assumption) _ _) fun _ _ _ => ?_
    | refine Outcome.Sim.andThen (Refine.sim_of_le (Mono.udiv ?_ ?_)) fun _ _ _ => ?_
    | refine Outcome.Sim.andThen (Refine.sim_of_le (Mono.urem ?_ ?_)) fun _ _ _ => ?_
    | refine Outcome.Sim.andThen (Refine.sim_of_le (Mono.sdiv ?_ ?_)) fun _ _ _ => ?_
    | refine Outcome.Sim.andThen (Refine.sim_of_le (Mono.srem ?_ ?_)) fun _ _ _ => ?_
    | refine Outcome.Sim.andThen (Refine.sim_of_le (Mono.mapOutcome2 (fun _ _ _ _ _ _ => ?_) ?_ ?_))
        fun _ _ _ => ?_
    | refine Mono.noundef ?_ ?_ | refine Mono.noundefPtr ?_ ?_ | refine Mono.noundefAll ?_ ?_
    | refine Mono.assume ?_ ?_ | refine Mono.sw ?_ fun _ => ?_ | refine Mono.branch ?_ ?_ ?_
    | refine Mono.vscaleRange ?_
    | refine Mem.le.assumeNonnull (Mem.leData.toLe (by assumption)) ?_ ?_
    | refine Mem.le.dereferenceable (Mem.leData.toLe (by assumption)) ?_ _ ?_
    | refine Outcome.Sim.br ?_ ?_ ?_
    | refine Outcome.Sim.jump ?_
    | refine Outcome.Sim.ret ?_))

end IRLean
