import Inflate.updatewindow

/-! zlib's `updatewindow`, from `inflate.c`, as clang compiles it at `-O2 -fno-strict-aliasing` for x86-64 Linux,
proved memory-safe. For any state meeting the invariant below, and any `copy` that the output buffer has room for
behind `end`, it returns 0, changes nothing but the window's first `wsize` bytes and three fields of the state, and
leaves the invariant holding for the next call. `tests/proofs.sh` regenerates `Inflate` from zlib's own source.

It says nothing about which bytes end up in the window. It also assumes the window is already allocated. If not,
`updatewindow` allocates it through `strm->zalloc`, a call through a pointer to code outside the module, which stops
the model. `docs/memory.md` has the rest of what this does and doesn't claim. -/

open IRLean Inflate

namespace UpdateWindow

local notation "St" => Inflate.updatewindow.step

/-! ### The statement -/

/-- The window's size once `updatewindow` has set it up: `wsize`, or `1 << wbits` the first time. -/
def size (wbits wsize : BitVec 32) : BitVec 32 := if wsize = 0#32 then 1#32 <<< wbits else wsize

/-- The fields fit a window of `ws` bytes: before it's used, `1 << wbits` bytes fit, and after, `wsize` bytes
fit and `wnext` is at most `wsize`. -/
def Fits (ws : Nat) (wbits wsize wnext : BitVec 32) : Prop :=
  (wsize = 0#32 → wbits.toNat < 32 ∧ 2 ^ wbits.toNat ≤ ws) ∧
    (wsize ≠ 0#32 → wnext.toNat ≤ wsize.toNat ∧ wsize.toNat ≤ ws)

/-- Memory as `updatewindow` needs it, apart from the fields fitting the window. `strm`, at offset `zo` of
allocation `z`, holds a pointer to allocation `s` in its `state` field. `s` holds an `inflate_state`, with these
fields, and a pointer to allocation `w` in its `window` field. `w` is `ws` bytes long. The offsets are x86-64
Linux's. -/
structure Shape (m : Mem) (z zo s w ws : Nat) (wbits wsize whave wnext : BitVec 32) : Prop where
  strm : ∃ n, m.Object z n ∧ zo + 64 ≤ n
  strmAligned : ((m.base z).toNat + zo) % 8 = 0
  state : m.HoldsPtr z (zo + 56) ⟨s, 0#64, []⟩
  stateObject : ∃ n, m.Object s n ∧ 80 ≤ n
  stateWritable : m.Writable s
  stateAligned : (m.base s).toNat % 8 = 0
  hwbits : m.HoldsInt s 56 wbits
  hwsize : m.HoldsInt s 60 wsize
  hwhave : m.HoldsInt s 64 whave
  hwnext : m.HoldsInt s 68 wnext
  window : m.HoldsPtr s 72 ⟨w, 0#64, []⟩
  windowObject : m.Object w ws
  windowWritable : m.Writable w
  distinct : w ≠ s ∧ w ≠ z ∧ s ≠ z

/-- Memory as `updatewindow` needs it: the invariant a theorem about `inflate` would have to keep. -/
structure Stream (m : Mem) (z zo s w ws : Nat) (wbits wsize whave wnext : BitVec 32) : Prop
    extends Shape m z zo s w ws wbits wsize whave wnext where
  fits : Fits ws wbits wsize wnext

/-- Offset `eo` of allocation `e`, which isn't the window, has `need` bytes before it. -/
structure Output (m : Mem) (w e eo need : Nat) : Prop where
  object : ∃ n, m.Object e n ∧ eo ≤ n
  room : need ≤ eo
  distinct : e ≠ w

/-- What `updatewindow` may change: the window's first `wsz` bytes, and the state's `wsize`, `whave` and `wnext`. -/
def Touched (s w wsz : Nat) (b i : Nat) : Prop := (b = w ∧ i < wsz) ∨ (b = s ∧ 60 ≤ i ∧ i < 72)

/-! ### Inside the call -/

/-- What `updatewindow`'s attributes promise about `strm` and `end`, in call `k`. -/
def tag (k : Nat) : Tag := { call := k, readonly := true, nofree := true, expires := true, noAddress := true }

/-- Inside call `k`: nothing restricts memory, and the call is running. -/
structure Inside (m : Mem) (k : Nat) : Prop where
  unrestricted : m.Unrestricted
  running : m.isRunning k = true

variable {m m0 : Mem} {z zo s w ws e eo k need : Nat} {wbits wsize whave wnext : BitVec 32}

theorem Inside.reads (I : Inside m k) (b : Nat) (o : BitVec 64) : m.TagsAllow ⟨b, o, [tag k]⟩ false := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  exact Mem.tagRule_read I.running rfl

theorem Inside.changes {m' : Mem} {T : Nat → Nat → Prop} (I : Inside m k) (F : Mem.Changes m m' T) :
    Inside m' k :=
  ⟨F.unrestricted I.unrestricted, by rw [F.isRunning]; exact I.running⟩

theorem Output.changes {m' : Mem} {T : Nat → Nat → Prop} (O : Output m w e eo need) (F : Mem.Changes m m' T) :
    Output m' w e eo need := by
  obtain ⟨n, On, hn⟩ := O.object
  exact ⟨⟨n, F.object On, hn⟩, O.room, O.distinct⟩

/-- Memory that changed only in the window and the three fields keeps its shape, with whatever the fields now hold. -/
theorem Shape.update {m' : Mem} {T : Nat → Nat → Prop} {wsize' whave' wnext' : BitVec 32}
    (Sh : Shape m z zo s w ws wbits wsize whave wnext) (F : Mem.Changes m m' T)
    (hT : ∀ b i, T b i → b = w ∨ (b = s ∧ 60 ≤ i ∧ i < 72))
    (hsize : m'.HoldsInt s 60 wsize') (hhave : m'.HoldsInt s 64 whave') (hnext : m'.HoldsInt s 68 wnext') :
    Shape m' z zo s w ws wbits wsize' whave' wnext' := by
  obtain ⟨nz, Oz, hz⟩ := Sh.strm
  obtain ⟨ns, Os, hs⟩ := Sh.stateObject
  obtain ⟨d1, d2, d3⟩ := Sh.distinct
  refine ⟨⟨nz, F.object Oz, hz⟩, by rw [F.base]; exact Sh.strmAligned, ?_, ⟨ns, F.object Os, hs⟩,
    F.writable Sh.stateWritable, by rw [F.base]; exact Sh.stateAligned, ?_, hsize, hhave, hnext, ?_,
    F.object Sh.windowObject, F.writable Sh.windowWritable, Sh.distinct⟩
  · refine F.holdsPtr Sh.state fun i _ h => ?_
    rcases hT _ _ h with h | ⟨h, _⟩
    · exact d2 h.symm
    · exact d3 h.symm
  · refine F.holdsInt Sh.hwbits fun i hi h => ?_
    rcases hT _ _ h with h | ⟨_, h1, _⟩
    · exact d1 h.symm
    · simp at hi; omega
  · refine F.holdsPtr Sh.window fun i _ h => ?_
    rcases hT _ _ h with h | ⟨_, _, h2⟩
    · exact d1 h.symm
    · omega

/-- Memory with the same allocations at the same addresses has the same shape. -/
theorem Shape.same {m' : Mem} (h : Mem.SameObjects m m') (Sh : Shape m z zo s w ws wbits wsize whave wnext) :
    Shape m' z zo s w ws wbits wsize whave wnext := by
  obtain ⟨⟨nz, Oz, hz⟩, a1, st, ⟨ns, Os, hs⟩, sw, a2, h1, h2, h3, h4, wi, Ow, ww, d⟩ := Sh
  exact ⟨⟨nz, h.object Oz, hz⟩, by rw [h.base]; exact a1, h.holdsPtr st, ⟨ns, h.object Os, hs⟩, h.writable sw,
    by rw [h.base]; exact a2, h.holdsInt h1, h.holdsInt h2, h.holdsInt h3, h.holdsInt h4, h.holdsPtr wi,
    h.object Ow, h.writable ww, d⟩

theorem Output.same {m' : Mem} (h : Mem.SameObjects m m') (O : Output m w e eo need) : Output m' w e eo need := by
  obtain ⟨n, On, hn⟩ := O.object
  exact ⟨⟨n, h.object On, hn⟩, O.room, O.distinct⟩

/-- What the first two blocks need: the stream, the state's `wsize`, and a window pointer that isn't null. -/
structure Head (m : Mem) (z zo s w : Nat) (wsize : BitVec 32) : Prop where
  strm : ∃ n, m.Object z n ∧ zo + 64 ≤ n
  strmAligned : ((m.base z).toNat + zo) % 8 = 0
  state : m.HoldsPtr z (zo + 56) ⟨s, 0#64, []⟩
  stateObject : ∃ n, m.Object s n ∧ 80 ≤ n
  stateAligned : (m.base s).toNat % 8 = 0
  hwsize : m.HoldsInt s 60 wsize
  window : m.HoldsPtr s 72 ⟨w, 0#64, []⟩
  windowAddr : m.addr ⟨w, 0#64, []⟩ ≠ 0#64

theorem Shape.head (Sh : Shape m z zo s w ws wbits wsize whave wnext) : Head m z zo s w wsize :=
  ⟨Sh.strm, Sh.strmAligned, Sh.state, Sh.stateObject, Sh.stateAligned, Sh.hwsize, Sh.window,
    Sh.windowObject.addr_ne_zero (o := 0) (by omega) []⟩

theorem Head.same {m' : Mem} (h : Mem.SameObjects m m') (H : Head m z zo s w wsize) : Head m' z zo s w wsize := by
  obtain ⟨⟨nz, Oz, hz⟩, a1, st, ⟨ns, Os, hs⟩, a2, h2, wi, wa⟩ := H
  exact ⟨⟨nz, h.object Oz, hz⟩, by rw [h.base]; exact a1, h.holdsPtr st, ⟨ns, h.object Os, hs⟩,
    by rw [h.base]; exact a2, h.holdsInt h2, h.holdsPtr wi, by
      have : m'.addr = m.addr := by funext p; simp [Mem.addr, h.base]
      rw [this]; exact wa⟩

/-- A store to `wsize`, `whave` or `wnext`. -/
theorem Shape.store (Sh : Shape m z zo s w ws wbits wsize whave wnext) (I : Inside m k) {o align : Nat}
    (ho : 60 ≤ o ∧ o + 4 ≤ 72) (hal : align = 1 ∨ ((m.base s).toNat + o) % align = 0) (x : BitVec 32) :
    ∃ m', m.storeInt (some ⟨s, BitVec.ofNat 64 o, []⟩) (some x) align = Outcome.ok m' ∧
      Mem.Changes m m' (fun b i => b = s ∧ o ≤ i ∧ i < o + 4) ∧ m'.HoldsInt s o x := by
  obtain ⟨ns, Os, hs⟩ := Sh.stateObject
  exact Os.storeInt Sh.stateWritable (by omega) hal I.unrestricted (Mem.tagsAllow_nil _ _ _) x

/-- Whether a field is still what it was, after a store to another. -/
theorem keep {m' : Mem} {o o' : Nat} {v : BitVec 32} (F : Mem.Changes m m' fun b i => b = s ∧ o ≤ i ∧ i < o + 4)
    (H : m.HoldsInt s o' v) (h : o + 4 ≤ o' ∨ o' + 4 ≤ o) : m'.HoldsInt s o' v :=
  F.holdsInt H fun i hi ⟨_, h1, h2⟩ => by simp at hi; omega

/-- A copy into the window from the output buffer. -/
theorem Shape.copy (Sh : Shape m z zo s w ws wbits wsize whave wnext) (I : Inside m k) (O : Output m w e eo need)
    {lo len src : Nat} (hw : lo + len ≤ ws) (hsrc : src + len ≤ eo) :
    ∃ m', m.memcpy (some ⟨w, BitVec.ofNat 64 lo, []⟩) (some ⟨e, BitVec.ofNat 64 src, [tag k]⟩)
        (some (BitVec.ofNat 64 len)) = Outcome.ok m' ∧
      Mem.Changes m m' (fun b i => b = w ∧ lo ≤ i ∧ i < lo + len) := by
  obtain ⟨ne, Oe, hne⟩ := O.object
  exact Sh.windowObject.memcpy Sh.windowWritable hw Oe (by omega) O.distinct.symm I.unrestricted
    (Mem.tagsAllow_nil _ _ _) (I.reads _ _)

/-- A copy into the window changes nothing `Shape` describes. -/
theorem Shape.windowWrite {m' : Mem} {P : Nat → Prop} (Sh : Shape m z zo s w ws wbits wsize whave wnext)
    (F : Mem.Changes m m' fun b i => b = w ∧ P i) : Shape m' z zo s w ws wbits wsize whave wnext :=
  Sh.update F (fun _ _ h => .inl h.1) (F.holdsInt Sh.hwsize fun _ _ h => Sh.distinct.1 h.1.symm)
    (F.holdsInt Sh.hwhave fun _ _ h => Sh.distinct.1 h.1.symm)
    (F.holdsInt Sh.hwnext fun _ _ h => Sh.distinct.1 h.1.symm)

/-! ### Arithmetic the blocks need -/

theorem shl1 {y : BitVec 32} (hy : y.toNat < 32) :
    Val.shl (some 1#32) (some y) (nuw := true) = some (1#32 <<< y) := by
  have h1 : Val.shiftOk y = true := by
    simp only [Val.shiftOk, BitVec.lt_def, BitVec.toNat_ofNat, decide_eq_true_eq]
    omega
  have hy' : y < 32#32 := by simpa [BitVec.lt_def] using hy
  have h2 : ((1#32 <<< y) >>> y != 1#32) = false := by bv_decide
  simp only [Val.shl, h1, h2, Bool.not_true, Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false]

theorem toNat_shl1 {y : BitVec 32} (hy : y.toNat < 32) : (1#32 <<< y).toNat = 2 ^ y.toNat := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, show (1#32).toNat = 1 from rfl, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hy)

theorem sub_some (x y : BitVec 32) : Val.sub (some x) (some y) = some (x - y) := by simp [Val.sub]

theorem umin_some (x y : BitVec 32) :
    Val.umin (some x) (some y) = some (if BitVec.ule x y then x else y) := rfl

theorem range32 (n : Nat) (h : n < 2 ^ 32) :
    Val.range 0#64 4294967296#64 (some (BitVec.ofNat 64 n)) = some (BitVec.ofNat 64 n) := by
  have : BitVec.ult (BitVec.ofNat 64 n) 4294967296#64 = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
    omega
  simp only [Val.range, BitVec.sub_zero, this, ite_true]

theorem range_zero : Val.range 0#32 2#32 (some 0#32) = some 0#32 := rfl

theorem addr_null : m.addr Ptr.null = 0#64 := rfl

theorem ite_some {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if p then some a else some b) = some (if p then a else b) := by
  split <;> rfl

theorem toNat_sub_le {x y : BitVec 32} (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]
  have := x.isLt
  omega

/-- How much of `copy` fits between `wnext` and the window's end: `llvm.umin`, as the optimizer left it. -/
def dist (wsz wnext c : BitVec 32) : BitVec 32 := if BitVec.ule (wsz - wnext) c = true then wsz - wnext else c

theorem umin_dist (wsz wnext c : BitVec 32) :
    Val.umin (some (wsz - wnext)) (some c) = some (dist wsz wnext c) := rfl

theorem toNat_dist {wsz wnext c : BitVec 32} (h : wnext.toNat ≤ wsz.toNat) :
    (dist wsz wnext c).toNat = min (wsz.toNat - wnext.toNat) c.toNat := by
  have e := toNat_sub_le h
  unfold dist
  split
  · rename_i hu
    simp only [BitVec.ule, e, decide_eq_true_eq] at hu
    rw [e]; omega
  · rename_i hu
    simp only [BitVec.ule, e, decide_eq_true_eq] at hu
    omega

/-! ### The blocks, one at a time -/

theorem entry_step (Sh : Head m z zo s w wsize) (I : Inside m k) (en : PtrVal) (copy : Val 32) :
    St (.entry m (some ⟨z, BitVec.ofNat 64 zo, [tag k]⟩) en copy) =
      jump (.if_end6 m (some ⟨w, 0#64, []⟩) en copy (some ⟨s, 0#64, []⟩) (some ⟨s, BitVec.ofNat 64 72, []⟩)) := by
  obtain ⟨nz, Oz, hz⟩ := Sh.strm
  obtain ⟨ns, Os, hs⟩ := Sh.stateObject
  have g1 : m.gep (some ⟨z, BitVec.ofNat 64 zo, [tag k]⟩) (some 56#64) (inbounds := true) (nuw := true) =
      some ⟨z, BitVec.ofNat 64 (zo + 56), [tag k]⟩ := Oz.gep (by omega) _
  have l1 : m.loadPtr (some ⟨z, BitVec.ofNat 64 (zo + 56), [tag k]⟩) 8 = Outcome.ok (some ⟨s, 0#64, []⟩) :=
    Oz.loadPtr Sh.state (by omega) (.inr (by have := Sh.strmAligned; omega)) I.unrestricted (I.reads _ _)
  have g2 : m.gep (some ⟨s, 0#64, []⟩) (some 72#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 72, []⟩ := Os.gep (o := 0) (by omega) _
  have l2 : m.loadPtr (some ⟨s, BitVec.ofNat 64 72, []⟩) 8 = Outcome.ok (some ⟨w, 0#64, []⟩) :=
    Os.loadPtr Sh.window (by omega) (.inr (by have := Sh.stateAligned; omega)) I.unrestricted
      (Mem.tagsAllow_nil _ _ _)
  have hne : (m.addr ⟨w, 0#64, []⟩ == 0#64) = false := beq_eq_false_iff_ne.mpr Sh.windowAddr
  simp only [Inflate.updatewindow.step, g1, l1, g2, l2, andThen_ok, Mem.observeAddress, List.any_nil,
    Bool.false_eq_true, ite_false, Mem.toVal, addr_null, Val.icmpEq_some, hne, br_ofBool]

theorem if_end6_step (Sh : Head m z zo s w wsize) (I : Inside m k) (en : PtrVal) (copy : Val 32) (wp : PtrVal) :
    St (.if_end6 m (some ⟨w, 0#64, []⟩) en copy (some ⟨s, 0#64, []⟩) wp) =
      jump (if (wsize == 0#32) = true then
          .if_then8 m en copy (some ⟨s, 0#64, []⟩) wp (some ⟨w, 0#64, []⟩) (some ⟨s, BitVec.ofNat 64 60, []⟩)
        else
          .if_end12 m (some wsize) en copy (some ⟨s, 0#64, []⟩) wp (some ⟨w, 0#64, []⟩)
            (some ⟨s, BitVec.ofNat 64 60, []⟩)) := by
  obtain ⟨ns, Os, hs⟩ := Sh.stateObject
  have g : m.gep (some ⟨s, 0#64, []⟩) (some 60#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 60, []⟩ := Os.gep (o := 0) (by omega) _
  have l : m.loadInt 32 (some ⟨s, BitVec.ofNat 64 60, []⟩) 4 = Outcome.ok (some wsize) :=
    Os.loadInt Sh.hwsize (by omega) (by omega) (.inr (by have := Sh.stateAligned; omega)) I.unrestricted
      (Mem.tagsAllow_nil _ _ _)
  simp only [Inflate.updatewindow.step, g, l, andThen_ok, Val.icmpEq_some, br_ofBool]

/-- The first time: `wsize = 1 << wbits`, and `wnext` and `whave` start at 0. -/
theorem if_then8_step (Sh : Shape m z zo s w ws wbits wsize whave wnext) (I : Inside m k) (en : PtrVal)
    (copy : Val 32) (wp : PtrVal) (hb : wbits.toNat < 32) :
    ∃ m', St (.if_then8 m en copy (some ⟨s, 0#64, []⟩) wp (some ⟨w, 0#64, []⟩) (some ⟨s, BitVec.ofNat 64 60, []⟩)) =
        jump (.if_end12 m' (some (1#32 <<< wbits)) en copy (some ⟨s, 0#64, []⟩) wp (some ⟨w, 0#64, []⟩)
          (some ⟨s, BitVec.ofNat 64 60, []⟩)) ∧
      Shape m' z zo s w ws wbits (1#32 <<< wbits) 0#32 0#32 ∧ Inside m' k ∧
      Mem.Changes m m' fun b i => b = s ∧ 60 ≤ i ∧ i < 72 := by
  obtain ⟨ns, Os, hs⟩ := Sh.stateObject
  have al := Sh.stateAligned
  have g56 : m.gep (some ⟨s, 0#64, []⟩) (some 56#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 56, []⟩ := Os.gep (o := 0) (by omega) _
  have l56 : m.loadInt 32 (some ⟨s, BitVec.ofNat 64 56, []⟩) 8 = Outcome.ok (some wbits) :=
    Os.loadInt Sh.hwbits (by omega) (by omega) (.inr (by omega)) I.unrestricted (Mem.tagsAllow_nil _ _ _)
  obtain ⟨m1, s1, F1, H1⟩ := Sh.store I (o := 60) (align := 4) (by omega) (.inr (by omega)) (1#32 <<< wbits)
  have I1 := I.changes F1
  have Os1 := F1.object Os
  have g68 : m1.gep (some ⟨s, 0#64, []⟩) (some 68#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 68, []⟩ := Os1.gep (o := 0) (by omega) _
  have Sh1 : Shape m1 z zo s w ws wbits (1#32 <<< wbits) whave wnext :=
    Sh.update F1 (fun _ _ h => .inr ⟨h.1, by omega, by omega⟩) H1 (keep F1 Sh.hwhave (by omega))
      (keep F1 Sh.hwnext (by omega))
  obtain ⟨m2, s2, F2, H2⟩ := Sh1.store I1 (o := 68) (align := 4) (by omega)
    (.inr (by rw [F1.base]; omega)) 0#32
  have I2 := I1.changes F2
  have Os2 := F2.object Os1
  have g64 : m2.gep (some ⟨s, 0#64, []⟩) (some 64#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 64, []⟩ := Os2.gep (o := 0) (by omega) _
  have Sh2 : Shape m2 z zo s w ws wbits (1#32 <<< wbits) whave 0#32 :=
    Sh1.update F2 (fun _ _ h => .inr ⟨h.1, by omega, by omega⟩) (keep F2 Sh1.hwsize (by omega))
      (keep F2 Sh1.hwhave (by omega)) H2
  obtain ⟨m3, s3, F3, H3⟩ := Sh2.store I2 (o := 64) (align := 8) (by omega)
    (.inr (by rw [F2.base, F1.base]; omega)) 0#32
  have Sh3 : Shape m3 z zo s w ws wbits (1#32 <<< wbits) 0#32 0#32 :=
    Sh2.update F3 (fun _ _ h => .inr ⟨h.1, by omega, by omega⟩) (keep F3 Sh2.hwsize (by omega)) H3
      (keep F3 Sh2.hwnext (by omega))
  refine ⟨m3, ?_, Sh3, I2.changes F3,
    (F1.trans F2 fun _ _ h => by omega).trans F3 fun _ _ h => by omega⟩
  simp only [Inflate.updatewindow.step, g56, l56, andThen_ok, shl1 hb, s1, g68, s2, g64, s3]

theorem if_end12_step (en : PtrVal) (copy v26 : BitVec 32) (v4 wp v17 wsp : PtrVal) :
    St (.if_end12 m (some v26) en (some copy) v4 wp v17 wsp) =
      jump (if BitVec.ult copy v26 = true then .if_else m en (some copy) v4 wp v17 wsp (some v26)
        else .if_then15 m en v4 v17 wsp (some v26)) := by
  simp only [Inflate.updatewindow.step, Val.icmpUlt_some, br_ofBool]

/-- `copy` covers the whole window: it copies the last `wsize` bytes before `end`, and `wnext` goes back to 0. -/
theorem if_then15_step {wsz : BitVec 32} (Sh : Shape m z zo s w ws wbits wsz whave wnext) (I : Inside m k)
    (O : Output m w e eo wsz.toNat) (h1 : 0 < wsz.toNat) (hws : wsz.toNat ≤ ws) :
    ∃ m', St (.if_then15 m (some ⟨e, BitVec.ofNat 64 eo, [tag k]⟩) (some ⟨s, 0#64, []⟩) (some ⟨w, 0#64, []⟩)
          (some ⟨s, BitVec.ofNat 64 60, []⟩) (some wsz)) = jump (.cleanup m' (some 0#32)) ∧
      Shape m' z zo s w ws wbits wsz wsz 0#32 ∧ Inside m' k ∧ Mem.Changes m m' (Touched s w wsz.toNat) := by
  obtain ⟨ns, Os, hs⟩ := Sh.stateObject
  obtain ⟨ne, Oe, hne⟩ := O.object
  have Ow := Sh.windowObject
  have al := Sh.stateAligned
  have room := O.room
  have hlt := wsz.isLt
  have ng : Val.sub (some 0#64) (some (BitVec.ofNat 64 wsz.toNat)) (nsw := true) =
      some (0#64 - BitVec.ofNat 64 wsz.toNat) := Mem.neg_nsw (by omega)
  have gb : m.gep (some ⟨e, BitVec.ofNat 64 eo, [tag k]⟩) (some (0#64 - BitVec.ofNat 64 wsz.toNat))
      (inbounds := true) = some ⟨e, BitVec.ofNat 64 (eo - wsz.toNat), [tag k]⟩ := Oe.gep_back hne room _
  have nw := Ow.nonnull (o := 0) (by omega) []
  have dw := fun (x : Outcome (Next updatewindow.Block (Val 32 × Mem))) =>
    Ow.dereferenceable (o := 0) (k := 1) (by omega) [] x
  have nd := Oe.nonnull (o := eo - wsz.toNat) (by omega) [tag k]
  have de := fun (x : Outcome (Next updatewindow.Block (Val 32 × Mem))) =>
    Oe.dereferenceable (o := eo - wsz.toNat) (k := 1) (by omega) [tag k] x
  have rg := range32 wsz.toNat hlt
  obtain ⟨m1, c1, F1⟩ := Sh.copy I O (lo := 0) (len := wsz.toNat) (src := eo - wsz.toNat) (by omega) (by omega)
  have Sh1 := Sh.windowWrite F1
  have I1 := I.changes F1
  have g68 : m1.gep (some ⟨s, 0#64, []⟩) (some 68#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 68, []⟩ := (F1.object Os).gep (o := 0) (by omega) _
  obtain ⟨m2, s2, F2, H2⟩ := Sh1.store I1 (o := 68) (align := 4) (by omega) (.inr (by rw [F1.base]; omega)) 0#32
  have Sh2 : Shape m2 z zo s w ws wbits wsz whave 0#32 :=
    Sh1.update F2 (fun _ _ h => .inr ⟨h.1, by omega, by omega⟩) (keep F2 Sh1.hwsize (by omega))
      (keep F2 Sh1.hwhave (by omega)) H2
  have I2 := I1.changes F2
  have Os2 := F2.object (F1.object Os)
  have l60 : m2.loadInt 32 (some ⟨s, BitVec.ofNat 64 60, []⟩) 4 = Outcome.ok (some wsz) :=
    Os2.loadInt Sh2.hwsize (by omega) (by omega) (.inr (by rw [F2.base, F1.base]; omega)) I2.unrestricted
      (Mem.tagsAllow_nil _ _ _)
  have g64 : m2.gep (some ⟨s, 0#64, []⟩) (some 64#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 64, []⟩ := Os2.gep (o := 0) (by omega) _
  obtain ⟨m3, s3, F3, H3⟩ := Sh2.store I2 (o := 64) (align := 8) (by omega)
    (.inr (by rw [F2.base, F1.base]; omega)) wsz
  have Sh3 : Shape m3 z zo s w ws wbits wsz wsz 0#32 :=
    Sh2.update F3 (fun _ _ h => .inr ⟨h.1, by omega, by omega⟩) (keep F3 Sh2.hwsize (by omega)) H3
      (keep F3 Sh2.hwnext (by omega))
  refine ⟨m3, ?_, Sh3, I2.changes F3,
    ((F1.trans F2 (T'' := Touched s w wsz.toNat) fun _ _ h => by simp only [Touched] at *; omega).trans F3
      fun _ _ h => by simp only [Touched] at *; omega)⟩
  simp only [Inflate.updatewindow.step, Mem.zext32, ng, gb, Mem.aligned_one, nw, dw, nd, de, rg, noundef_some, c1,
    andThen_ok, g68, s2, l60, g64, s3]

/-- `copy` is less than the window's size: copy what fits from `wnext` to the window's end. -/
theorem if_else_step {wsz c : BitVec 32} (Sh : Shape m z zo s w ws wbits wsz whave wnext) (I : Inside m k)
    (O : Output m w e eo c.toNat) (hn : wnext.toNat ≤ wsz.toNat) (hws : wsz.toNat ≤ ws) :
    ∃ m', St (.if_else m (some ⟨e, BitVec.ofNat 64 eo, [tag k]⟩) (some c) (some ⟨s, 0#64, []⟩)
          (some ⟨s, BitVec.ofNat 64 72, []⟩) (some ⟨w, 0#64, []⟩) (some ⟨s, BitVec.ofNat 64 60, []⟩) (some wsz)) =
        jump (if BitVec.ult (wsz - wnext) c = true then
            .if_then39 m' (some ⟨e, BitVec.ofNat 64 eo, [tag k]⟩) (some c) (some ⟨s, 0#64, []⟩)
              (some ⟨s, BitVec.ofNat 64 72, []⟩) (some ⟨s, BitVec.ofNat 64 60, []⟩)
              (some ⟨s, BitVec.ofNat 64 68, []⟩) (some (dist wsz wnext c))
          else
            .if_else49 m' (some ⟨s, 0#64, []⟩) (some ⟨s, BitVec.ofNat 64 60, []⟩)
              (some ⟨s, BitVec.ofNat 64 68, []⟩) (some (dist wsz wnext c))) ∧
      Shape m' z zo s w ws wbits wsz whave wnext ∧ Inside m' k ∧
      Mem.Changes m m' (fun b i => b = w ∧ wnext.toNat ≤ i ∧ i < wnext.toNat + (dist wsz wnext c).toNat) := by
  obtain ⟨ns, Os, hs⟩ := Sh.stateObject
  obtain ⟨ne, Oe, hne⟩ := O.object
  have Ow := Sh.windowObject
  have al := Sh.stateAligned
  have room := O.room
  have hd := toNat_dist (c := c) hn
  have hlt := (dist wsz wnext c).isLt
  have hc := c.isLt
  have g68 : m.gep (some ⟨s, 0#64, []⟩) (some 68#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 68, []⟩ := Os.gep (o := 0) (by omega) _
  have l68 : m.loadInt 32 (some ⟨s, BitVec.ofNat 64 68, []⟩) 4 = Outcome.ok (some wnext) :=
    Os.loadInt Sh.hwnext (by omega) (by omega) (.inr (by omega)) I.unrestricted (Mem.tagsAllow_nil _ _ _)
  have gw : m.gep (some ⟨w, 0#64, []⟩) (some (BitVec.ofNat 64 wnext.toNat)) (inbounds := true) (nuw := true) =
      some ⟨w, BitVec.ofNat 64 wnext.toNat, []⟩ := by
    have := Ow.gep (o := 0) (k := wnext.toNat) (by omega) []
    simpa only [Nat.zero_add] using this
  have ng : Val.sub (some 0#64) (some (BitVec.ofNat 64 c.toNat)) (nsw := true) =
      some (0#64 - BitVec.ofNat 64 c.toNat) := Mem.neg_nsw (by omega)
  have gb : m.gep (some ⟨e, BitVec.ofNat 64 eo, [tag k]⟩) (some (0#64 - BitVec.ofNat 64 c.toNat))
      (inbounds := true) = some ⟨e, BitVec.ofNat 64 (eo - c.toNat), [tag k]⟩ := Oe.gep_back hne room _
  have nw := Ow.nonnull (o := wnext.toNat) (by omega) []
  have nd := Oe.nonnull (o := eo - c.toNat) (by omega) [tag k]
  have rg := range32 (dist wsz wnext c).toNat hlt
  obtain ⟨m1, c1, F1⟩ := Sh.copy I O (lo := wnext.toNat) (len := (dist wsz wnext c).toNat)
    (src := eo - c.toNat) (by omega) (by omega)
  refine ⟨m1, ?_, Sh.windowWrite F1, I.changes F1, F1⟩
  simp only [Inflate.updatewindow.step, g68, l68, andThen_ok, sub_some, umin_dist, Mem.zext32, gw, ng, gb,
    Mem.aligned_one, nw, nd, rg, noundef_some, c1, Val.icmpUgt_some, br_ofBool]

/-- The copy wrapped around the window's end: the rest goes at its start, and `wnext` follows it. -/
theorem if_then39_step {wsz c d : BitVec 32} (Sh : Shape m z zo s w ws wbits wsz whave wnext) (I : Inside m k)
    (O : Output m w e eo c.toNat) (hd : d.toNat ≤ c.toNat) (hr : c.toNat - d.toNat ≤ ws) :
    ∃ m', St (.if_then39 m (some ⟨e, BitVec.ofNat 64 eo, [tag k]⟩) (some c) (some ⟨s, 0#64, []⟩)
          (some ⟨s, BitVec.ofNat 64 72, []⟩) (some ⟨s, BitVec.ofNat 64 60, []⟩) (some ⟨s, BitVec.ofNat 64 68, []⟩)
          (some d)) = jump (.cleanup m' (some 0#32)) ∧
      Shape m' z zo s w ws wbits wsz wsz (c - d) ∧ Inside m' k ∧
      Mem.Changes m m' (fun b i => (b = w ∧ i < c.toNat - d.toNat) ∨ (b = s ∧ 60 ≤ i ∧ i < 72)) := by
  obtain ⟨ns, Os, hs⟩ := Sh.stateObject
  obtain ⟨ne, Oe, hne⟩ := O.object
  have Ow := Sh.windowObject
  have al := Sh.stateAligned
  have room := O.room
  have hcd := toNat_sub_le hd
  have hlt := (c - d).isLt
  have lw : m.loadPtr (some ⟨s, BitVec.ofNat 64 72, []⟩) 8 = Outcome.ok (some ⟨w, 0#64, []⟩) :=
    Os.loadPtr Sh.window (by omega) (.inr (by omega)) I.unrestricted (Mem.tagsAllow_nil _ _ _)
  have ng : Val.sub (some 0#64) (some (BitVec.ofNat 64 (c - d).toNat)) (nsw := true) =
      some (0#64 - BitVec.ofNat 64 (c - d).toNat) := Mem.neg_nsw (by omega)
  have gb : m.gep (some ⟨e, BitVec.ofNat 64 eo, [tag k]⟩) (some (0#64 - BitVec.ofNat 64 (c - d).toNat))
      (inbounds := true) = some ⟨e, BitVec.ofNat 64 (eo - (c - d).toNat), [tag k]⟩ :=
    Oe.gep_back hne (by omega) _
  have nw := Ow.nonnull (o := 0) (by omega) []
  have nd := Oe.nonnull (o := eo - (c - d).toNat) (by omega) [tag k]
  have rg := range32 (c - d).toNat hlt
  obtain ⟨m1, c1, F1⟩ := Sh.copy I O (lo := 0) (len := (c - d).toNat) (src := eo - (c - d).toNat)
    (by omega) (by omega)
  have Sh1 := Sh.windowWrite F1
  have I1 := I.changes F1
  obtain ⟨m2, s2, F2, H2⟩ := Sh1.store I1 (o := 68) (align := 4) (by omega) (.inr (by rw [F1.base]; omega)) (c - d)
  have Sh2 : Shape m2 z zo s w ws wbits wsz whave (c - d) :=
    Sh1.update F2 (fun _ _ h => .inr ⟨h.1, by omega, by omega⟩) (keep F2 Sh1.hwsize (by omega))
      (keep F2 Sh1.hwhave (by omega)) H2
  have I2 := I1.changes F2
  have Os2 := F2.object (F1.object Os)
  have l60 : m2.loadInt 32 (some ⟨s, BitVec.ofNat 64 60, []⟩) 4 = Outcome.ok (some wsz) :=
    Os2.loadInt Sh2.hwsize (by omega) (by omega) (.inr (by rw [F2.base, F1.base]; omega)) I2.unrestricted
      (Mem.tagsAllow_nil _ _ _)
  have g64 : m2.gep (some ⟨s, 0#64, []⟩) (some 64#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 64, []⟩ := Os2.gep (o := 0) (by omega) _
  obtain ⟨m3, s3, F3, H3⟩ := Sh2.store I2 (o := 64) (align := 8) (by omega)
    (.inr (by rw [F2.base, F1.base]; omega)) wsz
  have Sh3 : Shape m3 z zo s w ws wbits wsz wsz (c - d) :=
    Sh2.update F3 (fun _ _ h => .inr ⟨h.1, by omega, by omega⟩) (keep F3 Sh2.hwsize (by omega)) H3
      (keep F3 Sh2.hwnext (by omega))
  refine ⟨m3, ?_, Sh3, I2.changes F3,
    ((F1.trans F2 (T'' := fun b i => (b = w ∧ i < c.toNat - d.toNat) ∨ (b = s ∧ 60 ≤ i ∧ i < 72))
      fun _ _ h => by omega).trans F3 fun _ _ h => by omega)⟩
  simp only [Inflate.updatewindow.step, sub_some, lw, andThen_ok, Mem.zext32, ng, gb, Mem.aligned_one, nw, nd, rg,
    noundef_some, c1, s2, l60, g64, s3]

/-- All of `copy` fit before the window's end: `wnext` moves past it, back to 0 at the end. -/
theorem if_else49_step {wsz d : BitVec 32} (Sh : Shape m z zo s w ws wbits wsz whave wnext) (I : Inside m k) :
    ∃ m', St (.if_else49 m (some ⟨s, 0#64, []⟩) (some ⟨s, BitVec.ofNat 64 60, []⟩)
          (some ⟨s, BitVec.ofNat 64 68, []⟩) (some d)) =
        jump (if BitVec.ult whave wsz = true then
            .if_then62 m' (some d) (some ⟨s, BitVec.ofNat 64 64, []⟩) (some whave)
          else .cleanup m' (some 0#32)) ∧
      Shape m' z zo s w ws wbits wsz whave (if (wnext + d == wsz) = true then 0#32 else wnext + d) ∧
      Inside m' k ∧ Mem.Changes m m' (fun b i => b = s ∧ 68 ≤ i ∧ i < 72) := by
  obtain ⟨ns, Os, hs⟩ := Sh.stateObject
  have al := Sh.stateAligned
  have l68 : m.loadInt 32 (some ⟨s, BitVec.ofNat 64 68, []⟩) 4 = Outcome.ok (some wnext) :=
    Os.loadInt Sh.hwnext (by omega) (by omega) (.inr (by omega)) I.unrestricted (Mem.tagsAllow_nil _ _ _)
  have l60 : m.loadInt 32 (some ⟨s, BitVec.ofNat 64 60, []⟩) 4 = Outcome.ok (some wsz) :=
    Os.loadInt Sh.hwsize (by omega) (by omega) (.inr (by omega)) I.unrestricted (Mem.tagsAllow_nil _ _ _)
  obtain ⟨m1, s1, F1, H1⟩ := Sh.store I (o := 68) (align := 4) (by omega) (.inr (by omega))
    (if (wnext + d == wsz) = true then 0#32 else wnext + d)
  have Sh1 := Sh.update F1 (fun _ _ h => .inr ⟨h.1, by omega, by omega⟩) (keep F1 Sh.hwsize (by omega))
    (keep F1 Sh.hwhave (by omega)) H1
  have I1 := I.changes F1
  have Os1 := F1.object Os
  have g64 : m1.gep (some ⟨s, 0#64, []⟩) (some 64#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 64, []⟩ := Os1.gep (o := 0) (by omega) _
  have l64 : m1.loadInt 32 (some ⟨s, BitVec.ofNat 64 64, []⟩) 8 = Outcome.ok (some whave) :=
    Os1.loadInt Sh1.hwhave (by omega) (by omega) (.inr (by rw [F1.base]; omega)) I1.unrestricted
      (Mem.tagsAllow_nil _ _ _)
  refine ⟨m1, ?_, Sh1, I1, F1⟩
  simp only [Inflate.updatewindow.step, l68, andThen_ok, Val.add_some, l60, Val.icmpEq_some, select_ofBool,
    ite_some, s1, g64, l64, Val.icmpUlt_some, br_ofBool]

/-- `whave` grows by what was copied, while the window isn't yet full. -/
theorem if_then62_step {d : BitVec 32} (Sh : Shape m z zo s w ws wbits wsize whave wnext) (I : Inside m k) :
    ∃ m', St (.if_then62 m (some d) (some ⟨s, BitVec.ofNat 64 64, []⟩) (some whave)) =
        jump (.cleanup m' (some 0#32)) ∧
      Shape m' z zo s w ws wbits wsize (whave + d) wnext ∧ Inside m' k ∧
      Mem.Changes m m' (fun b i => b = s ∧ 64 ≤ i ∧ i < 68) := by
  have al := Sh.stateAligned
  obtain ⟨m1, s1, F1, H1⟩ := Sh.store I (o := 64) (align := 8) (by omega) (.inr (by omega)) (whave + d)
  refine ⟨m1, ?_, Sh.update F1 (fun _ _ h => .inr ⟨h.1, by omega, by omega⟩) (keep F1 Sh.hwsize (by omega)) H1
    (keep F1 Sh.hwnext (by omega)), I.changes F1, F1⟩
  simp only [Inflate.updatewindow.step, Val.add_some, s1, andThen_ok]

theorem cleanup_run : run St (.cleanup m (some 0#32)) = Outcome.ok (some 0#32, m) :=
  run_ret St (by simp only [Inflate.updatewindow.step, range_zero])

/-! ### The whole function -/

/-- Every path from `if_end12`, where the window's size is set. -/
theorem from_if_end12 {wsz c : BitVec 32} (Sh : Shape m z zo s w ws wbits wsz whave wnext) (I : Inside m k)
    (O : Output m w e eo (min c.toNat wsz.toNat)) (hn : wnext.toNat ≤ wsz.toNat) (h1 : 0 < wsz.toNat)
    (hws : wsz.toNat ≤ ws) :
    ∃ m' whave' wnext', run St (.if_end12 m (some wsz) (some ⟨e, BitVec.ofNat 64 eo, [tag k]⟩) (some c)
          (some ⟨s, 0#64, []⟩) (some ⟨s, BitVec.ofNat 64 72, []⟩) (some ⟨w, 0#64, []⟩)
          (some ⟨s, BitVec.ofNat 64 60, []⟩)) = Outcome.ok (some 0#32, m') ∧
      Shape m' z zo s w ws wbits wsz whave' wnext' ∧ wnext'.toNat < wsz.toNat ∧ Inside m' k ∧
      Mem.Changes m m' (Touched s w wsz.toNat) := by
  rw [run_jump _ (if_end12_step _ _ _ _ _ _ _)]
  have room := O.room
  by_cases hc : BitVec.ult c wsz = true
  · simp only [hc, ite_true]
    have hc' : c.toNat < wsz.toNat := by simpa [BitVec.ult] using hc
    have O' : Output m w e eo c.toNat := { O with room := by omega }
    obtain ⟨m1, e1, Sh1, I1, F1⟩ := if_else_step Sh I O' hn hws
    have O1 := O'.changes F1
    have hsub := toNat_sub_le hn
    have hd := toNat_dist (c := c) hn
    rw [run_jump _ e1]
    by_cases hu : BitVec.ult (wsz - wnext) c = true
    · simp only [hu, ite_true]
      have hu' : wsz.toNat - wnext.toNat < c.toNat := by simpa [BitVec.ult, hsub] using hu
      obtain ⟨m2, e2, Sh2, I2, F2⟩ := if_then39_step (d := dist wsz wnext c) Sh1 I1 O1 (by omega) (by omega)
      rw [run_jump _ e2, cleanup_run]
      refine ⟨m2, wsz, c - dist wsz wnext c, rfl, Sh2, ?_, I2,
        F1.trans F2 fun _ _ h => by simp only [Touched] at *; omega⟩
      rw [toNat_sub_le (by omega)]
      omega
    · simp only [hu, Bool.false_eq_true, ite_false]
      have hu' : c.toNat ≤ wsz.toNat - wnext.toNat := by simpa [BitVec.ult, hsub] using hu
      obtain ⟨m2, e2, Sh2, I2, F2⟩ := if_else49_step (d := dist wsz wnext c) Sh1 I1
      have F12 := F1.trans F2 (T'' := Touched s w wsz.toNat) fun _ _ h => by simp only [Touched] at *; omega
      have hnw : (if (wnext + dist wsz wnext c == wsz) = true then 0#32 else wnext + dist wsz wnext c).toNat <
          wsz.toNat := by
        have hadd : (wnext + dist wsz wnext c).toNat = wnext.toNat + (dist wsz wnext c).toNat := by
          rw [BitVec.toNat_add]; omega
        split
        · simp; omega
        · rename_i hne
          have : (wnext + dist wsz wnext c).toNat ≠ wsz.toNat := by
            intro h; exact hne (by simp [BitVec.eq_of_toNat_eq h])
          omega
      rw [run_jump _ e2]
      by_cases hv : BitVec.ult whave wsz = true
      · simp only [hv, ite_true]
        obtain ⟨m3, e3, Sh3, I3, F3⟩ := if_then62_step Sh2 I2
        rw [run_jump _ e3, cleanup_run]
        exact ⟨m3, _, _, rfl, Sh3, hnw, I3, F12.trans F3 fun _ _ h => by simp only [Touched] at *; omega⟩
      · simp only [hv, Bool.false_eq_true, ite_false]
        rw [cleanup_run]
        exact ⟨m2, _, _, rfl, Sh2, hnw, I2, F12⟩
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hc' : wsz.toNat ≤ c.toNat := by simpa [BitVec.ult] using hc
    have O' : Output m w e eo wsz.toNat := { O with room := by omega }
    obtain ⟨m1, e1, Sh1, I1, F1⟩ := if_then15_step Sh I O' h1 hws
    rw [run_jump _ e1, cleanup_run]
    exact ⟨m1, wsz, 0#32, rfl, Sh1, by simp; omega, I1, F1⟩

/-- Every path through the function's blocks. -/
theorem run_ok {c : BitVec 32} (S : Stream m z zo s w ws wbits wsize whave wnext) (I : Inside m k)
    (O : Output m w e eo (min c.toNat (size wbits wsize).toNat)) :
    ∃ m' whave' wnext', run St (.entry m (some ⟨z, BitVec.ofNat 64 zo, [tag k]⟩)
          (some ⟨e, BitVec.ofNat 64 eo, [tag k]⟩) (some c)) = Outcome.ok (some 0#32, m') ∧
      Shape m' z zo s w ws wbits (size wbits wsize) whave' wnext' ∧
      wnext'.toNat < (size wbits wsize).toNat ∧ (size wbits wsize).toNat ≤ ws ∧ Inside m' k ∧
      Mem.Changes m m' (Touched s w (size wbits wsize).toNat) := by
  rw [run_jump _ (entry_step S.head I _ _), run_jump _ (if_end6_step S.head I _ _ _)]
  by_cases h0 : wsize = 0#32
  · subst h0
    obtain ⟨hb, hw⟩ := S.fits.1 rfl
    simp only [beq_self_eq_true, ite_true]
    obtain ⟨m1, e1, Sh1, I1, F1⟩ := if_then8_step S.toShape I _ _ _ hb
    rw [run_jump _ e1]
    have hsz : size wbits 0#32 = 1#32 <<< wbits := by simp [size]
    rw [hsz] at O ⊢
    have ht := toNat_shl1 hb
    have hp : 0 < 2 ^ wbits.toNat := Nat.two_pow_pos _
    obtain ⟨m2, wh, wn, e2, Sh2, hlt, I2, F2⟩ :=
      from_if_end12 Sh1 I1 (O.changes F1) (by simp) (by rw [ht]; exact hp) (by rw [ht]; exact hw)
    exact ⟨m2, wh, wn, e2, Sh2, hlt, by rw [ht]; exact hw, I2,
      F1.trans F2 fun _ _ h => by simp only [Touched] at *; omega⟩
  · have hne : (wsize == 0#32) = false := by simpa using h0
    simp only [hne, Bool.false_eq_true, ite_false]
    obtain ⟨hn, hw⟩ := S.fits.2 h0
    have hsz : size wbits wsize = wsize := by simp [size, h0]
    rw [hsz] at O ⊢
    have h1 : 0 < wsize.toNat := by
      have : wsize.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    obtain ⟨m', wh, wn, e', Sh', hlt, I', F'⟩ := from_if_end12 S.toShape I O hn h1 hw
    exact ⟨m', wh, wn, e', Sh', hlt, hw, I', F'⟩

/-! ### The theorem -/

/-- **`updatewindow` is memory-safe.** Called while no running call restricts memory, as outside any call or
inside one of a function with no `memory(...)` attribute, on a stream meeting `Stream`, with `copy` bytes behind
`end` or a whole window's worth, it returns 0 with no undefined behavior and no model stop. The only bytes it
changes are the window's first `size wbits wsize` and the state's `wsize`, `whave` and `wnext`, so nothing outside
the window and those fields is touched, nothing else about memory changes, and `Stream` holds again, with the
window's size set and `wnext` inside it, ready for the next call. -/
theorem updatewindow_safe {m : Mem} {copy : BitVec 32} (hu : m.Unrestricted)
    (S : Stream m z zo s w ws wbits wsize whave wnext)
    (O : Output m w e eo (min copy.toNat (size wbits wsize).toNat)) :
    ∃ m' whave' wnext',
      updatewindow (some ⟨z, BitVec.ofNat 64 zo, []⟩) (some ⟨e, BitVec.ofNat 64 eo, []⟩) (some copy) m =
        Outcome.ok (some 0#32, m') ∧
      Stream m' z zo s w ws wbits (size wbits wsize) whave' wnext' ∧
      wnext'.toNat < (size wbits wsize).toNat ∧
      Mem.Changes m.afterCall m' (Touched s w (size wbits wsize).toNat) := by
  have I : Inside m.enter m.nextCall := ⟨Mem.unrestricted_enter hu, Mem.isRunning_enter⟩
  -- Entering the call changes only the running calls, which `Stream` and `Output` don't mention.
  have same : Mem.SameObjects m m.enter := ⟨fun _ => rfl, rfl⟩
  have S' : Stream m.enter z zo s w ws wbits wsize whave wnext := ⟨S.toShape.same same, S.fits⟩
  have O' := O.same same
  obtain ⟨m1, wh, wn, e1, Sh1, hlt, hws, _, F1⟩ :=
    run_ok (m := m.enter) (k := m.nextCall) (c := copy) S' I O'
  obtain ⟨m2, e2, F2, same'⟩ := Mem.call_unrestricted
    (k := fun mm call => run St (.entry mm (some ⟨z, BitVec.ofNat 64 zo, [tag call]⟩)
      (some ⟨e, BitVec.ofNat 64 eo, [tag call]⟩) (some copy))) e1 F1
  have hw0 : (size wbits wsize).toNat ≠ 0 := by omega
  have hfits : Fits ws wbits (size wbits wsize) wn :=
    ⟨fun h => absurd (by simp [h]) hw0, fun _ => ⟨by omega, hws⟩⟩
  refine ⟨m2, wh, wn, ?_, ⟨?_, hfits⟩, hlt, F2⟩
  · simp only [updatewindow, noundef_some]
    exact e2
  · exact Sh1.same same'

/-! ### Across calls -/

/-- `updatewindow` once for each output in turn, as `inflate` calls it, stopping at the first that doesn't return. -/
noncomputable def updates (z zo : Nat) : List (Nat × Nat × BitVec 32) → Mem → Outcome Mem
  | [], m => Outcome.ok m
  | (e, eo, copy) :: rest, m =>
    andThen (updatewindow (some ⟨z, BitVec.ofNat 64 zo, []⟩) (some ⟨e, BitVec.ofNat 64 eo, []⟩) (some copy) m)
      fun r => updates z zo rest r.2

theorem size_size (h : 0 < (size wbits wsize).toNat) : size wbits (size wbits wsize) = size wbits wsize := by
  have : size wbits wsize ≠ 0#32 := fun e => by simp [e] at h
  show (if size wbits wsize = 0#32 then 1#32 <<< wbits else size wbits wsize) = size wbits wsize
  simp only [this, ite_false]

/-- **Across calls:** however many times `updatewindow` runs, each with room behind its own `end`, every call returns,
and nothing changes but the window's first `size wbits wsize` bytes and the three fields. -/
theorem updates_safe {calls : List (Nat × Nat × BitVec 32)} (hu : m.Unrestricted)
    (S : Stream m z zo s w ws wbits wsize whave wnext)
    (O : ∀ c, c ∈ calls → Output m w c.1 c.2.1 (min c.2.2.toNat (size wbits wsize).toNat)) :
    ∃ m', updates z zo calls m = Outcome.ok m' ∧
      Mem.Changes { m with nextCall := m.nextCall + calls.length } m' (Touched s w (size wbits wsize).toNat) := by
  induction calls generalizing m wsize whave wnext with
  | nil => exact ⟨m, rfl, by simpa using Mem.Changes.refl m _⟩
  | cons c rest ih =>
    obtain ⟨e, eo, copy⟩ := c
    obtain ⟨m1, wh, wn, e1, S1, hlt, F1⟩ := updatewindow_safe hu S (O _ (List.mem_cons_self ..))
    have hsz := size_size (wbits := wbits) (wsize := wsize) (by omega)
    have hu1 : m1.Unrestricted := F1.unrestricted hu
    have same : Mem.SameObjects m m.afterCall := ⟨fun _ => rfl, rfl⟩
    have O1 : ∀ c, c ∈ rest → Output m1 w c.1 c.2.1 (min c.2.2.toNat (size wbits (size wbits wsize)).toNat) := by
      intro c hc
      rw [hsz]
      exact ((O c (List.mem_cons_of_mem _ hc)).same same).changes F1
    obtain ⟨m2, e2, F2⟩ := ih hu1 S1 O1
    rw [hsz] at F2
    refine ⟨m2, by simp only [updates, e1, andThen_ok]; exact e2, ?_⟩
    have F := (F1.shift rest.length).trans F2 fun _ _ h => by rcases h with h | h <;> exact h
    have n : m.afterCall.nextCall + rest.length = m.nextCall + (rest.length + 1) := by
      show m.nextCall + 1 + rest.length = _
      omega
    have e : ({ m.afterCall with nextCall := m.afterCall.nextCall + rest.length } : Mem) =
        { m with nextCall := m.nextCall + (rest.length + 1) } :=
      congrArg (fun k => ({ m with nextCall := k } : Mem)) n
    rw [e] at F
    simpa using F

/-! ### The hypotheses can all hold

A theorem whose hypotheses can't all hold says nothing. This memory meets them: a stream as `inflateReset` leaves one
whose 32 KiB window was already allocated, with `wsize` 0, after a call of `inflate` has written 100 bytes. That's the
first branch of `Fits`. The memory `updatewindow_safe` gives back meets the second, with `wsize` set. -/

/-- An `inflate_state` with these fields and this window, and zeros elsewhere. -/
def stateBytes (wbits wsize whave wnext : BitVec 32) (w : Nat) (i : Nat) : Byte :=
  if 56 ≤ i ∧ i < 60 then Mem.intByte wbits (i - 56)
  else if 60 ≤ i ∧ i < 64 then Mem.intByte wsize (i - 60)
  else if 64 ≤ i ∧ i < 68 then Mem.intByte whave (i - 64)
  else if 68 ≤ i ∧ i < 72 then Mem.intByte wnext (i - 68)
  else if 72 ≤ i ∧ i < 80 then .ptr ⟨w, 0#64, []⟩ (i - 72)
  else .val 0#8

def streamAlloc : Alloc :=
  { size := 112, readonly := false,
    bytes := fun i => if 56 ≤ i ∧ i < 64 then .ptr ⟨2, 0#64, []⟩ (i - 56) else .val 0#8 }

def stateAlloc : Alloc :=
  { size := 7160, readonly := false, bytes := stateBytes 15#32 0#32 0#32 0#32 3, heap := true }

def windowAlloc : Alloc := { size := 32768, readonly := false, bytes := fun _ => .uninit, heap := true }

def outputAlloc : Alloc := { size := 100, readonly := false, bytes := fun _ => .val 7#8 }

/-- A `z_stream` in allocation 1, pointing to its `inflate_state` in 2, which points to a window of 32 KiB in 3, and
100 bytes of output in 4. The sizes are x86-64 Linux's, and the addresses `Mem.spacedOut`'s. -/
def initial : Mem where
  allocs b :=
    if b = 1 then some streamAlloc else if b = 2 then some stateAlloc else if b = 3 then some windowAlloc
    else if b = 4 then some outputAlloc else none
  next := 5
  base := Mem.spacedOut
  frame := []

theorem initial_object (b n : Nat) (a : Alloc) (ha : initial.allocs b = some a) (hs : a.size = n) (hb : b ≠ 0)
    (hb' : b < 2 ^ 31) (hn : n < 2 ^ 32) : initial.Object b n := by
  have e : (initial.base b).toNat = b * 4294967296 := by
    simp only [initial, Mem.spacedOut, BitVec.toNat_ofNat]; omega
  refine ⟨⟨a, ha, hs⟩, hb, by omega, ?_, by rw [e]; omega⟩
  intro h
  have := congrArg BitVec.toNat h
  rw [e, BitVec.toNat_zero] at this
  omega

theorem initial_aligned (b : Nat) : (initial.base b).toNat % 8 = 0 := by
  simp only [initial, Mem.spacedOut, BitVec.toNat_ofNat]
  omega

theorem initial_stream : Stream initial 1 0 2 3 32768 15#32 0#32 0#32 0#32 := by
  have field : ∀ (o : Nat) (v : BitVec 32),
      (∀ i, i < 4 → stateBytes 15#32 0#32 0#32 0#32 3 (o + i) = Mem.intByte v i) → initial.HoldsInt 2 o v :=
    fun o v h => ⟨stateAlloc, rfl, fun i hi => h i (by simpa using hi)⟩
  refine ⟨⟨⟨112, initial_object 1 112 streamAlloc rfl rfl (by decide) (by decide) (by decide), by decide⟩,
    initial_aligned 1, ⟨streamAlloc, rfl, ?_⟩,
    ⟨7160, initial_object 2 7160 stateAlloc rfl rfl (by decide) (by decide) (by decide), by decide⟩,
    ⟨stateAlloc, rfl, rfl⟩, initial_aligned 2, field 56 _ ?_, field 60 _ ?_, field 64 _ ?_, field 68 _ ?_,
    ⟨stateAlloc, rfl, ?_⟩, initial_object 3 32768 windowAlloc rfl rfl (by decide) (by decide) (by decide),
    ⟨windowAlloc, rfl, rfl⟩, by decide⟩, ⟨fun _ => ⟨by decide, by decide⟩, fun h => absurd rfl h⟩⟩
  all_goals
    intro i hi
    simp only [stateAlloc, streamAlloc, stateBytes]
    repeat' split
    all_goals first | omega | (congr 1; omega)

theorem initial_output : Output initial 3 4 100 (min (100#32).toNat (size 15#32 0#32).toNat) :=
  ⟨⟨100, initial_object 4 100 outputAlloc rfl rfl (by decide) (by decide) (by decide), by omega⟩, by decide,
    by decide⟩

/-- `updatewindow_safe` on that memory. -/
theorem initial_safe : ∃ m',
    updatewindow (some ⟨1, BitVec.ofNat 64 0, []⟩) (some ⟨4, BitVec.ofNat 64 100, []⟩) (some 100#32) initial =
      Outcome.ok (some 0#32, m') := by
  obtain ⟨m', _, _, h, _⟩ := updatewindow_safe (Mem.unrestricted_nil rfl) initial_stream initial_output
  exact ⟨m', h⟩

/-! ### Without some preconditions, the model stops on undefined behavior

Four of the preconditions aren't only what the proof needed: for each, a state that breaks it is undefined, for the
reason given, on the path its theorem picks out with a few more hypotheses. So the model catches each of these bugs.
Breaking one alone doesn't always matter: a call that copies nothing, say, reads and writes no window at all. -/

theorem run_ub {b : updatewindow.Block} {r : UB} (h : St b = Outcome.ub r) : run St b = Outcome.ub r := by
  rw [run, h]; rfl

theorem andThen_ub {α β : Type} (r : UB) (k : α → Outcome β) : andThen (Outcome.ub r) k = Outcome.ub r := rfl

/-- `updatewindow` is undefined when its blocks are. -/
theorem ub_of_run {copy : BitVec 32} {r : UB}
    (h : run St (.entry m.enter (some ⟨z, BitVec.ofNat 64 zo, [tag m.nextCall]⟩)
      (some ⟨e, BitVec.ofNat 64 eo, [tag m.nextCall]⟩) (some copy)) = Outcome.ub r) :
    updatewindow (some ⟨z, BitVec.ofNat 64 zo, []⟩) (some ⟨e, BitVec.ofNat 64 eo, []⟩) (some copy) m =
      Outcome.ub r := by
  simp only [updatewindow, noundef_some]
  exact Mem.call_stop (k := fun mm call => run St (.entry mm (some ⟨z, BitVec.ofNat 64 zo, [tag call]⟩)
    (some ⟨e, BitVec.ofNat 64 eo, [tag call]⟩) (some copy))) h

theorem inside_enter (hu : m.Unrestricted) : Inside m.enter m.nextCall :=
  ⟨Mem.unrestricted_enter hu, Mem.isRunning_enter⟩

/-- **A window smaller than `wsize`** says it is: copying a whole window writes past its end. -/
theorem window_too_small {copy : BitVec 32} (hu : m.Unrestricted) (Sh : Shape m z zo s w ws wbits wsize whave wnext)
    (hpos : 0 < ws) (hsmall : ws < wsize.toNat) (hcopy : wsize.toNat ≤ copy.toNat) (O : Output m w e eo wsize.toNat) :
    updatewindow (some ⟨z, BitVec.ofNat 64 zo, []⟩) (some ⟨e, BitVec.ofNat 64 eo, []⟩) (some copy) m =
      Outcome.ub .badAccess := by
  apply ub_of_run
  have same : Mem.SameObjects m m.enter := ⟨fun _ => rfl, rfl⟩
  have Sh' := Sh.same same
  have I := inside_enter hu
  obtain ⟨ne, Oe, hne⟩ := (O.same same).object
  have room := O.room
  have hlt := wsize.isLt
  have hz : (wsize == 0#32) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; subst h; simp at hsmall
  have hu : BitVec.ult copy wsize = false := by simp only [BitVec.ult, decide_eq_false_iff_not]; omega
  rw [run_jump _ (entry_step Sh'.head I _ _), run_jump _ (if_end6_step Sh'.head I _ _ _)]
  simp only [hz, Bool.false_eq_true, ite_false]
  rw [run_jump _ (if_end12_step _ _ _ _ _ _ _)]
  simp only [hu, Bool.false_eq_true, ite_false]
  apply run_ub
  have Ow := Sh'.windowObject
  obtain ⟨wa, hwa, hws⟩ := Ow.live
  have ng : Val.sub (some 0#64) (some (BitVec.ofNat 64 wsize.toNat)) (nsw := true) =
      some (0#64 - BitVec.ofNat 64 wsize.toNat) := Mem.neg_nsw (by omega)
  have gb := Oe.gep_back hne room [tag m.nextCall]
  have nw := Ow.nonnull (o := 0) (by omega) []
  have dw := fun (x : Outcome (Next updatewindow.Block (Val 32 × Mem))) =>
    Ow.dereferenceable (o := 0) (k := 1) (by omega) [] x
  have nd := Oe.nonnull (o := eo - wsize.toNat) (by omega) [tag m.nextCall]
  have de := fun (x : Outcome (Next updatewindow.Block (Val 32 × Mem))) =>
    Oe.dereferenceable (o := eo - wsize.toNat) (k := 1) (by omega) [tag m.nextCall] x
  have rg := range32 wsize.toNat hlt
  have mc : m.enter.memcpy (some ⟨w, 0#64, []⟩) (some ⟨e, BitVec.ofNat 64 (eo - wsize.toNat), [tag m.nextCall]⟩)
      (some (BitVec.ofNat 64 wsize.toNat)) = Outcome.ub .badAccess :=
    Mem.memcpy_past_end hwa (by omega) (by omega) (by simp; omega)
  simp only [Inflate.updatewindow.step, Mem.zext32, ng, gb, Mem.aligned_one, nw, dw, nd, de, rg, noundef_some, mc,
    andThen_ub]

/-- **A `wnext` past `wsize`**: `wsize - wnext` wraps around, so the copy isn't cut off at the window's end, and
writes past it. -/
theorem wnext_past_wsize {copy : BitVec 32} (hu : m.Unrestricted) (Sh : Shape m z zo s w ws wbits wsize whave wnext)
    (hpast : wsize.toNat < wnext.toNat) (hin : wnext.toNat ≤ ws) (hover : ws < wnext.toNat + copy.toNat)
    (hcopy : copy.toNat < wsize.toNat) (O : Output m w e eo copy.toNat) :
    updatewindow (some ⟨z, BitVec.ofNat 64 zo, []⟩) (some ⟨e, BitVec.ofNat 64 eo, []⟩) (some copy) m =
      Outcome.ub .badAccess := by
  apply ub_of_run
  have same : Mem.SameObjects m m.enter := ⟨fun _ => rfl, rfl⟩
  have Sh' := Sh.same same
  have I := inside_enter hu
  obtain ⟨ne, Oe, hne⟩ := (O.same same).object
  obtain ⟨ns, Os, hs⟩ := Sh'.stateObject
  have al := Sh'.stateAligned
  have room := O.room
  have hz : (wsize == 0#32) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; subst h; simp at hcopy
  have hu : BitVec.ult copy wsize = true := by simp only [BitVec.ult, decide_eq_true_eq]; omega
  rw [run_jump _ (entry_step Sh'.head I _ _), run_jump _ (if_end6_step Sh'.head I _ _ _)]
  simp only [hz, Bool.false_eq_true, ite_false]
  rw [run_jump _ (if_end12_step _ _ _ _ _ _ _)]
  simp only [hu, ite_true]
  apply run_ub
  have Ow := Sh'.windowObject
  obtain ⟨wa, hwa, hws⟩ := Ow.live
  have hwrap : (wsize - wnext).toNat = 2 ^ 32 - (wnext.toNat - wsize.toNat) := by
    rw [BitVec.toNat_sub]; have := wnext.isLt; omega
  have hd : dist wsize wnext copy = copy := by
    have : BitVec.ule (wsize - wnext) copy = false := by
      simp only [BitVec.ule, hwrap, decide_eq_false_iff_not]; have := wnext.isLt; omega
    simp [dist, this]
  have g68 : m.enter.gep (some ⟨s, 0#64, []⟩) (some 68#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 68, []⟩ := Os.gep (o := 0) (by omega) _
  have l68 : m.enter.loadInt 32 (some ⟨s, BitVec.ofNat 64 68, []⟩) 4 = Outcome.ok (some wnext) :=
    Os.loadInt Sh'.hwnext (by omega) (by omega) (.inr (by omega)) I.unrestricted (Mem.tagsAllow_nil _ _ _)
  have gw : m.enter.gep (some ⟨w, 0#64, []⟩) (some (BitVec.ofNat 64 wnext.toNat)) (inbounds := true) (nuw := true) =
      some ⟨w, BitVec.ofNat 64 wnext.toNat, []⟩ := by
    have := Ow.gep (o := 0) (k := wnext.toNat) (by omega) []
    simpa only [Nat.zero_add] using this
  have ng : Val.sub (some 0#64) (some (BitVec.ofNat 64 copy.toNat)) (nsw := true) =
      some (0#64 - BitVec.ofNat 64 copy.toNat) := Mem.neg_nsw (by have := copy.isLt; omega)
  have gb := Oe.gep_back hne room [tag m.nextCall]
  have nw := Ow.nonnull (o := wnext.toNat) (by omega) []
  have nd := Oe.nonnull (o := eo - copy.toNat) (by omega) [tag m.nextCall]
  have rg := range32 copy.toNat copy.isLt
  have mc : m.enter.memcpy (some ⟨w, BitVec.ofNat 64 wnext.toNat, []⟩)
      (some ⟨e, BitVec.ofNat 64 (eo - copy.toNat), [tag m.nextCall]⟩) (some (BitVec.ofNat 64 copy.toNat)) =
      Outcome.ub .badAccess :=
    Mem.memcpy_past_end hwa (by omega) (by have := copy.isLt; omega)
      (by simp only [Mem.toNat_ofNat_of_lt (show wnext.toNat < 2 ^ 63 by have := wnext.isLt; omega)]; omega)
  simp only [Inflate.updatewindow.step, g68, l68, andThen_ok, sub_some, umin_dist, hd, Mem.zext32, gw, ng, gb,
    Mem.aligned_one, nw, nd, rg, noundef_some, mc, andThen_ub]

/-- **An output buffer with fewer than `copy` bytes before `end`**: `end - copy` is before the buffer's start, so
`inbounds` makes it poison, and passing poison to `memcpy`, whose argument is `noundef`, is undefined. -/
theorem output_too_short {copy : BitVec 32} (hu : m.Unrestricted) (S : Stream m z zo s w ws wbits wsize whave wnext)
    (hz : wsize ≠ 0#32) (hcopy : copy.toNat < wsize.toNat) (hshort : eo < copy.toNat)
    (Oe : ∃ n, m.Object e n ∧ eo ≤ n) :
    updatewindow (some ⟨z, BitVec.ofNat 64 zo, []⟩) (some ⟨e, BitVec.ofNat 64 eo, []⟩) (some copy) m =
      Outcome.ub .noundefPoison := by
  apply ub_of_run
  have same : Mem.SameObjects m m.enter := ⟨fun _ => rfl, rfl⟩
  have Sh' := S.toShape.same same
  have I := inside_enter hu
  obtain ⟨ne, Oe, hne⟩ := Oe
  have Oe := same.object Oe
  obtain ⟨ns, Os, hs⟩ := Sh'.stateObject
  have al := Sh'.stateAligned
  obtain ⟨hn, hws⟩ := S.fits.2 hz
  have hz' : (wsize == 0#32) = false := by simpa using hz
  have hu : BitVec.ult copy wsize = true := by simp only [BitVec.ult, decide_eq_true_eq]; omega
  rw [run_jump _ (entry_step Sh'.head I _ _), run_jump _ (if_end6_step Sh'.head I _ _ _)]
  simp only [hz', Bool.false_eq_true, ite_false]
  rw [run_jump _ (if_end12_step _ _ _ _ _ _ _)]
  simp only [hu, ite_true]
  apply run_ub
  have Ow := Sh'.windowObject
  have hd := toNat_dist (c := copy) hn
  have g68 : m.enter.gep (some ⟨s, 0#64, []⟩) (some 68#64) (inbounds := true) (nuw := true) =
      some ⟨s, BitVec.ofNat 64 68, []⟩ := Os.gep (o := 0) (by omega) _
  have l68 : m.enter.loadInt 32 (some ⟨s, BitVec.ofNat 64 68, []⟩) 4 = Outcome.ok (some wnext) :=
    Os.loadInt Sh'.hwnext (by omega) (by omega) (.inr (by omega)) I.unrestricted (Mem.tagsAllow_nil _ _ _)
  have gw : m.enter.gep (some ⟨w, 0#64, []⟩) (some (BitVec.ofNat 64 wnext.toNat)) (inbounds := true) (nuw := true) =
      some ⟨w, BitVec.ofNat 64 wnext.toNat, []⟩ := by
    have := Ow.gep (o := 0) (k := wnext.toNat) (by omega) []
    simpa only [Nat.zero_add] using this
  have ng : Val.sub (some 0#64) (some (BitVec.ofNat 64 copy.toNat)) (nsw := true) =
      some (0#64 - BitVec.ofNat 64 copy.toNat) := Mem.neg_nsw (by have := copy.isLt; omega)
  have gb := Oe.gep_back_out hne hshort (by have := copy.isLt; omega) [tag m.nextCall]
  have nw := Ow.nonnull (o := wnext.toNat) (by omega) []
  have nn : m.enter.nonnull none = none := rfl
  simp only [Inflate.updatewindow.step, g68, l68, andThen_ok, sub_some, umin_dist, Mem.zext32, gw, ng, gb,
    Mem.aligned_one, nw, nn, noundef_some]
  rfl

/-- **A window that's been freed**: `state->window` still points where it was, and the copy's access to it is
undefined, since the allocation is gone. -/
theorem window_freed {copy : BitVec 32} (hu : m.Unrestricted) (H : Head m z zo s w wsize) (hgone : m.allocs w = none)
    (hz : wsize ≠ 0#32) (hcopy : wsize.toNat ≤ copy.toNat) (Oe : ∃ n, m.Object e n ∧ eo ≤ n)
    (room : wsize.toNat ≤ eo) :
    updatewindow (some ⟨z, BitVec.ofNat 64 zo, []⟩) (some ⟨e, BitVec.ofNat 64 eo, []⟩) (some copy) m =
      Outcome.ub .badAccess := by
  apply ub_of_run
  have I := inside_enter hu
  have same : Mem.SameObjects m m.enter := ⟨fun _ => rfl, rfl⟩
  have H' := H.same same
  have hz' : (wsize == 0#32) = false := by simpa using hz
  have hu : BitVec.ult copy wsize = false := by simp only [BitVec.ult, decide_eq_false_iff_not]; omega
  rw [run_jump _ (entry_step H' I _ _), run_jump _ (if_end6_step H' I _ _ _)]
  simp only [hz', Bool.false_eq_true, ite_false]
  rw [run_jump _ (if_end12_step _ _ _ _ _ _ _)]
  simp only [hu, Bool.false_eq_true, ite_false]
  apply run_ub
  obtain ⟨ne, Oe, hne⟩ := Oe
  have Oe := same.object Oe
  have ng : Val.sub (some 0#64) (some (BitVec.ofNat 64 wsize.toNat)) (nsw := true) =
      some (0#64 - BitVec.ofNat 64 wsize.toNat) := Mem.neg_nsw (by have := wsize.isLt; omega)
  have gb := Oe.gep_back hne room [tag m.nextCall]
  have nw : m.enter.nonnull (some ⟨w, 0#64, []⟩) = some ⟨w, 0#64, []⟩ := by
    simp [Mem.nonnull, H'.windowAddr]
  have dw := fun (x : Outcome (Next updatewindow.Block (Val 32 × Mem))) =>
    Mem.dereferenceable_gone (m := m.enter) (q := ⟨w, 0#64, []⟩) (n := 1) hgone x
  simp only [Inflate.updatewindow.step, Mem.zext32, ng, gb, Mem.aligned_one, nw, noundef_some, dw]

end UpdateWindow

#print axioms UpdateWindow.updatewindow_safe
#print axioms UpdateWindow.initial_safe
#print axioms UpdateWindow.window_too_small
#print axioms UpdateWindow.wnext_past_wsize
#print axioms UpdateWindow.output_too_short
#print axioms UpdateWindow.window_freed
