import IRLean.Mem

/-! A kit for proofs about emitted code. `simp only [foo.step, llvm_val, ...]` runs a block on
values known not to be poison, leaving the arithmetic for `bv_decide` or `omega`. -/

namespace IRLean

namespace Val
variable {w v : Nat} (x y : BitVec w)

@[llvm_val] theorem add_some : add (some x) (some y) = some (x + y) := by simp [add]
@[llvm_val] theorem and_some : and (some x) (some y) = some (x &&& y) := rfl
@[llvm_val] theorem xor_some : xor (some x) (some y) = some (x ^^^ y) := rfl
@[llvm_val] theorem or_some : or (some x) (some y) = some (x ||| y) := by simp [or]
@[llvm_val] theorem zext_some : zext v (some x) = some (x.setWidth v) := by simp [zext]
@[llvm_val] theorem icmpEq_some : icmpEq (some x) (some y) = some (BitVec.ofBool (x == y)) := by
  simp [icmpEq, icmp]
@[llvm_val] theorem icmpNe_some : icmpNe (some x) (some y) = some (BitVec.ofBool (x != y)) := by
  simp [icmpNe, icmp]
@[llvm_val] theorem icmpUlt_some : icmpUlt (some x) (some y) = some (BitVec.ofBool (BitVec.ult x y)) := by
  simp [icmpUlt, icmp]
@[llvm_val] theorem icmpUgt_some : icmpUgt (some x) (some y) = some (BitVec.ofBool (BitVec.ult y x)) := by
  simp [icmpUgt, icmp]
@[llvm_val] theorem mul_some : mul (some x) (some y) = some (x * y) := by simp [mul]
@[llvm_val] theorem trunc_some : trunc v (some x) = some (x.setWidth v) := by simp [trunc]
@[llvm_val] theorem lshr_some (h : BitVec.ult y (BitVec.ofNat w w) = true) :
    lshr (some x) (some y) = some (x >>> y) := by
  simp only [lshr, shiftOk]
  simp [show (y < BitVec.ofNat w w) from by simpa [BitVec.ult, BitVec.lt_def] using h]

end Val

/-- A branch on a known condition. -/
@[llvm_val] theorem br_ofBool (p : Bool) (t e : β) :
    (br (some (BitVec.ofBool p)) t e : Outcome (Next β ρ)) = jump (if p = true then t else e) := by
  cases p <;> simp [br]

/-- A `select` on a known condition. -/
@[llvm_val] theorem select_ofBool [HasPoison α] (p : Bool) (t e : α) :
    select (some (BitVec.ofBool p)) t e = if p = true then t else e := by
  cases p <;> simp [select]

@[llvm_val] theorem andThen_ok (x : α) (k : α → Outcome β) : andThen (Outcome.ok x) k = k x := rfl

@[llvm_val] theorem noundef_some (x : τ) (k : Outcome α) : noundef (some x) k = k := rfl

/-- `select c x false`, which is how `&&` comes out of the optimizer. -/
theorem select_and (a b : Bool) :
    select (some (BitVec.ofBool a)) (some (BitVec.ofBool b)) (some 0#1) = some (BitVec.ofBool (a && b)) := by
  cases a <;> cases b <;> simp [select]

/-! ### Branch conditions, as facts about natural numbers that `omega` can use -/

theorem beq_toNat {w : Nat} (a b : BitVec w) : (a == b) = decide (a.toNat = b.toNat) := by
  by_cases h : a = b
  · simp [h]
  · have : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp [h, this]

theorem bne_toNat {w : Nat} (a b : BitVec w) : (a != b) = !decide (a.toNat = b.toNat) := by
  rw [bne, beq_toNat]

theorem ult_toNat {w : Nat} (a b : BitVec w) : BitVec.ult a b = decide (a.toNat < b.toNat) := rfl

/-- `L + c'`, where `c'` stands for `-c`. Keep `c'` a variable: given the literal, `omega` writes a
proof that the kernel runs out of memory checking. -/
theorem toNat_dec {L : BitVec 64} {c' : Nat} (c : Nat) (h : c' = 18446744073709551616 - c)
    (hc : c ≤ L.toNat) (hc0 : 0 < c) : (L + BitVec.ofNat 64 c').toNat = L.toNat - c := by
  have := L.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem lshr_lit {x : BitVec 64} {k : Nat} (hk : k < 64) :
    Val.lshr (some x) (some (BitVec.ofNat 64 k)) = some (x >>> BitVec.ofNat 64 k) := by
  apply Val.lshr_some
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

theorem run_jump (step : β → Outcome (Next β ρ)) {b b' : β} (h : step b = jump b') :
    run step b = run step b' := by
  rw [run, h]; rfl

theorem run_ret (step : β → Outcome (Next β ρ)) {b : β} {r : ρ} (h : step b = ret r) :
    run step b = Outcome.ok r := by
  rw [run, h]; rfl

/-! ### Reading a buffer -/

/-- The pointer `i` bytes into a buffer, with the tags `t`. -/
abbrev bufPtr (t : List Tag) (block o i : Nat) : Ptr := ⟨block, BitVec.ofNat 64 (o + i), t⟩

/-- `n` initialized bytes at offset `o` of allocation `block`, holding `data`, that a pointer tagged `t` may
read. Every real allocation meets the size limits, which are LangRef's rules for an allocated object: it's
smaller than `2 ^ 63`, and neither it nor the pointer just past its end crosses the top of the address
space. `allowed`, `clean`, `tagsOld` and `callsOld` hold for any call from outside a function that promised
something about memory, and say what's needed for a call from inside one. -/
structure Reachable (m : Mem) (t : List Tag) (block o n : Nat) (data : Nat → BitVec 8) : Prop where
  alloc : ∃ a : Alloc, m.allocs block = some a ∧ o + n ≤ a.size ∧ a.size < 2 ^ 63 ∧
    ∀ i, i < n → a.bytes (o + i) = .val (data i)
  fits : (m.addr (bufPtr t block o 0)).toNat + n < 2 ^ 64
  /-- No running call or tag forbids reading it. -/
  allowed : ∀ a, m.allocs block = some a → ∀ off, m.check ⟨block, off, t⟩ a false = none
  /-- No running call or tag makes reading it give poison. -/
  clean : ∀ a, m.allocs block = some a → ∀ i, i < n → ∀ off,
    m.unwritten ⟨block, off, t⟩ a (o + i) = false
  tagsOld : ∀ x, x ∈ t → x.call < m.nextCall
  callsOld : ∀ c, c ∈ m.calls → c.id < m.nextCall

/-- The same, for a pointer that a function may also ask is null, as well as any call from outside a function
that promised something about memory allows. -/
structure Readable (m : Mem) (t : List Tag) (block o n : Nat) (data : Nat → BitVec 8) : Prop
    extends Reachable m t block o n data where
  /-- Asking whether a pointer tagged `t` is null is allowed. -/
  nullChecks : ∀ x, x ∈ t → x.noAddress = false ∨ x.nullCheck = true

/-- Memory after one call that promised something and left everything else as it found it. -/
abbrev Mem.afterCall (m : Mem) : Mem := { m with nextCall := m.nextCall + 1 }

/-- A call that only reads, with its pointer tagged `T`, leaves memory as `afterCall` says. -/
abbrev Mem.inCall (m : Mem) (e : Effects) : Mem :=
  { m with
    calls := { id := m.nextCall, effects := e, start := m.next, tracked := false } :: m.calls
    nextCall := m.nextCall + 1 }

theorem Mem.check_eq_none {m : Mem} {q : Ptr} {a : Alloc} {write : Bool} :
    m.check q a write = none ↔
      (∀ x, x ∈ q.tags → m.tagRule write x = none) ∧ ∀ c, c ∈ m.calls → Mem.callRule c q a write = none := by
  cases h : q.tags.findSome? (m.tagRule write) with
  | some e =>
    simp only [Mem.check, h, reduceCtorEq, false_iff]
    intro hx
    rw [List.findSome?_eq_none_iff.mpr hx.1] at h
    simp at h
  | none =>
    have hx := List.findSome?_eq_none_iff.mp h
    simp only [Mem.check, h, List.findSome?_eq_none_iff]
    exact ⟨fun hc => ⟨hx, hc⟩, fun hc => hc.2⟩

/-- Reading a constant through a pointer with no tags breaks no rule. -/
theorem Mem.check_constant {m : Mem} {q : Ptr} {a : Alloc} (hq : q.tags = []) (ha : a.readonly = true) :
    m.check q a false = none := by
  rw [Mem.check_eq_none]
  refine ⟨by simp [hq], fun c _ => ?_⟩
  simp [Mem.callRule, ha]

theorem Mem.unwritten_constant {m : Mem} {q : Ptr} {a : Alloc} {o : Nat} (ha : a.readonly = true) :
    m.unwritten q a o = false := by
  simp [Mem.unwritten, ha]

/-- Moving forward inside an allocation, in a layout where its address doesn't wrap. -/
theorem Mem.gep_forward {m : Mem} {q : Ptr} {a : Alloc} {k : Nat} (ha : m.allocs q.block = some a)
    (hq : q.offset.toNat + k ≤ a.size) (hmax : a.size < 2 ^ 64) (hfit : (m.addr q).toNat + k < 2 ^ 64)
    (hk : k < 2 ^ 63) :
    Mem.gep m (some q) (some (BitVec.ofNat 64 k)) (inbounds := true) (nuw := true) =
      some { q with offset := q.offset + BitVec.ofNat 64 k } := by
  have tk : (BitVec.ofNat 64 k).toNat = k := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hu : (m.addr q).uaddOverflow (BitVec.ofNat 64 k) = false := by
    simp only [BitVec.uaddOverflow, tk]
    simp only [decide_eq_false_iff_not, Nat.not_le, ge_iff_le]
    omega
  have hs : (BitVec.ofNat 64 k).msb = false := by
    simp only [BitVec.msb_eq_decide, tk, decide_eq_false_iff_not]
    omega
  have hmoved : (q.offset.toNat + k) % 18446744073709551616 ≤ a.size := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp only [Mem.gep, Mem.addressWraps, hu, hs, Bool.true_and, Bool.true_or, Bool.false_eq_true,
    ite_false, ha]
  by_cases h0 : BitVec.ofNat 64 k = 0#64
  · simp [h0]
  · simp [h0, hmoved, show q.offset.toNat ≤ a.size by omega]

namespace Reachable

variable {m : Mem} {t : List Tag} {block o n : Nat} {data : Nat → BitVec 8}

theorem load (B : Reachable m t block o n data) {i : Nat} (h : i < n) :
    Mem.loadInt 8 m (some (bufPtr t block o i)) 1 = Outcome.ok (some (data i)) := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := B.alloc
  have hlt : o + i < 2 ^ 64 := by omega
  have hb := hd i h
  have off : (BitVec.ofNat 64 (o + i)).toNat = o + i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
  have fits : ¬ o + i + 8 / 8 > a.size := by omega
  have hc := B.allowed a ha (BitVec.ofNat 64 (o + i))
  have hw := B.clean a ha i h (BitVec.ofNat 64 (o + i))
  simp [Mem.loadInt, Mem.access, ha, Mem.read, Mem.visible, hc, hw, Mem.collect, bufPtr, off, fits, hb,
    Outcome.ok]

/-- The address `i` bytes in, for `i` up to one past the end. -/
theorem toNat_addr (B : Reachable m t block o n data) {i : Nat} (h : i ≤ n) :
    (m.addr (bufPtr t block o i)).toNat = (m.addr (bufPtr t block o 0)).toNat + i := by
  obtain ⟨a, _, hsz, hmax, _⟩ := B.alloc
  have hf := B.fits
  by_cases hb : block = 0
  · subst hb
    simp only [Mem.addr, beq_self_eq_true, ite_true, BitVec.toNat_ofNat] at hf ⊢
    omega
  · have hb' : (block == 0) = false := by simpa using hb
    simp only [Mem.addr, hb', Bool.false_eq_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat]
      at hf ⊢
    omega

theorem gep (B : Reachable m t block o n data) {i k : Nat} (h : i + k ≤ n) :
    Mem.gep m (some (bufPtr t block o i)) (some (BitVec.ofNat 64 k)) (inbounds := true) (nuw := true) =
      some (bufPtr t block o (i + k)) := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := B.alloc
  have hoff : BitVec.ofNat 64 (o + i) + BitVec.ofNat 64 k = BitVec.ofNat 64 (o + (i + k)) := by
    rw [← Nat.add_assoc]; simp [BitVec.ofNat_add]
  have ho : (BitVec.ofNat 64 (o + i)).toNat = o + i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ht := B.toNat_addr (i := i) (by omega)
  have hf := B.fits
  have := Mem.gep_forward (m := m) (q := bufPtr t block o i) (a := a) (k := k) ha (by simp only [ho]; omega)
    (by omega) (by omega) (by omega)
  simpa [bufPtr, hoff] using this

/-- The same, for a `getelementptr` with no flags, which can't fail. -/
theorem gep_plain (m : Mem) (t : List Tag) (block o i k : Nat) :
    Mem.gep m (some (bufPtr t block o i)) (some (BitVec.ofNat 64 k)) =
      some (bufPtr t block o (i + k)) := by
  have hoff : BitVec.ofNat 64 (o + i) + BitVec.ofNat 64 k = BitVec.ofNat 64 (o + (i + k)) := by
    rw [← Nat.add_assoc]; simp [BitVec.ofNat_add]
  simp [Mem.gep, bufPtr, hoff]

/-- A buffer stays readable inside a call that may read through its arguments and only adds a tag that
allows it. -/
theorem enter (B : Reachable m t block o n data) {e : Effects} (he : e.arg = .read ∨ e.arg = .readwrite)
    {T : Tag} (hT : T.call = m.nextCall) (hn : T.readnone = false) (hw : T.writeonly = false)
    (hi : T.initializes = false) :
    Reachable (m.inCall e) (T :: t) block o n data := by
  have hold : ∀ c, c ∈ m.calls → (T.call == c.id) = false := fun c hc => by
    have := B.callsOld c hc
    simp only [beq_eq_false_iff_ne]; omega
  have hrun : ∀ x, x ∈ t → (m.inCall e).isRunning x.call = m.isRunning x.call := fun x hx => by
    have := B.tagsOld x hx
    simp only [Mem.isRunning, List.any_cons, Bool.or_eq_right_iff_imp, beq_iff_eq]
    omega
  have hacc : ∀ c, c ∈ m.calls → ∀ off a, Mem.callAccess c ⟨block, off, T :: t⟩ a = Mem.callAccess c ⟨block, off, t⟩ a := by
    intro c hc off a
    simp [Mem.callAccess, hold c hc]
  refine ⟨B.alloc, ?_, fun a ha off => ?_, fun a ha i h off => ?_, fun x hx => ?_, fun c hc => ?_⟩
  · simpa [Mem.addr] using B.fits
  · have hb := Mem.check_eq_none.mp (B.allowed a ha off)
    rw [Mem.check_eq_none]
    refine ⟨fun x hx => ?_, fun c hc => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · simp [Mem.tagRule, Mem.isRunning, hT, hn]
      · have h2 := hb.1 x hx
        simp only [Mem.tagRule] at h2 ⊢
        rw [hrun x hx]
        exact h2
    · rcases List.mem_cons.mp hc with rfl | hc
      · by_cases hs : (a.stack && decide (m.next ≤ block)) = true <;> rcases he with he | he <;>
          simp [Mem.callRule, Mem.callAccess, hs, hT, he]
      · have h2 := hb.2 c hc
        simp only [Mem.callRule] at h2 ⊢
        rw [hacc c hc]
        exact h2
  · have hb := B.clean a ha i h off
    simp only [Mem.unwritten, List.any_cons] at hb ⊢
    simp only [Bool.false_and, Bool.false_or]
    rw [List.any_eq_false] at hb ⊢
    intro c hc
    have h2 := hb c hc
    simp only [hacc c hc]
    simpa [hold c hc, hi, hw] using h2
  · rcases List.mem_cons.mp hx with rfl | hx
    · simp [hT]
    · have := B.tagsOld x hx
      simp only; omega
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · have := B.callsOld c hc
      simp only; omega

end Reachable

namespace Readable

variable {m : Mem} {t : List Tag} {block o n : Nat} {data : Nat → BitVec 8}

theorem load (B : Readable m t block o n data) {i : Nat} (h : i < n) :
    Mem.loadInt 8 m (some (bufPtr t block o i)) 1 = Outcome.ok (some (data i)) := B.toReachable.load h

theorem toNat_addr (B : Readable m t block o n data) {i : Nat} (h : i ≤ n) :
    (m.addr (bufPtr t block o i)).toNat = (m.addr (bufPtr t block o 0)).toNat + i := B.toReachable.toNat_addr h

theorem gep (B : Readable m t block o n data) {i k : Nat} (h : i + k ≤ n) :
    Mem.gep m (some (bufPtr t block o i)) (some (BitVec.ofNat 64 k)) (inbounds := true) (nuw := true) =
      some (bufPtr t block o (i + k)) := B.toReachable.gep h

theorem gep_plain (m : Mem) (t : List Tag) (block o i k : Nat) :
    Mem.gep m (some (bufPtr t block o i)) (some (BitVec.ofNat 64 k)) =
      some (bufPtr t block o (i + k)) := Reachable.gep_plain m t block o i k

/-- Asking whether a buffer's pointer is null breaks no promise. -/
theorem observeNull (B : Readable m t block o n data) (i : Nat) (k : Outcome α) :
    Mem.observeAddress (some (bufPtr t block o i)) true k = k := by
  have h : t.any (fun x => x.noAddress && !(true && x.nullCheck)) = false := by
    rw [List.any_eq_false]
    intro x hx
    rcases B.nullChecks x hx with h | h <;> simp [h]
  simp only [Mem.observeAddress, h, Bool.false_eq_true, ite_false]

/-- A buffer stays readable inside a call that may read through its arguments and only adds a tag that
allows it. -/
theorem enter (B : Readable m t block o n data) {e : Effects} (he : e.arg = .read ∨ e.arg = .readwrite)
    {T : Tag} (hT : T.call = m.nextCall) (hn : T.readnone = false) (hw : T.writeonly = false)
    (hi : T.initializes = false) (hc : T.noAddress = false ∨ T.nullCheck = true) :
    Readable (m.inCall e) (T :: t) block o n data :=
  { Reachable.enter B.toReachable he hT hn hw hi with
    nullChecks := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hc
      · exact B.nullChecks x hx }

/-- A global holding bytes is `Readable`, so its hypotheses can all hold at once. -/
theorem ofGlobal (m : Mem) (block : Nat) (init : Array Nat) (hcalls : m.calls = [])
    (hbytes : ∀ i (h : i < init.size), init[i] ≤ 255) (hsize : init.size < 2 ^ 63)
    (hfits : ((m.addGlobal block init.size false init).addr (bufPtr [] block 0 0)).toNat + init.size < 2 ^ 64) :
    Readable (m.addGlobal block init.size false init) [] block 0 init.size
      (fun i => BitVec.ofNat 8 (init[i]?.getD 0)) := by
  have hc : (m.addGlobal block init.size false init).calls = [] := hcalls
  refine ⟨⟨⟨{ size := init.size, readonly := false, bytes := Mem.globalBytes init },
    by simp [Mem.addGlobal], by simp, hsize, fun i hi => ?_⟩, hfits, fun a _ off => ?_, fun a _ i _ off => ?_,
    by simp, by simp [hc]⟩, by simp⟩
  · have h := hbytes i hi
    simp [Mem.globalBytes, hi, Nat.not_lt.mpr h]
  · simp [Mem.check, hc]
  · simp [Mem.unwritten, hc]

end Readable

namespace Table

/-! A global table of 32-bit entries, whose bytes the code reads directly. -/

def bytes4 (v : Nat) : List Nat := [v % 256, v / 256 % 256, v / 65536 % 256, v / 16777216 % 256]

theorem length_flatMap_range (g : Nat → List Nat) (hg : ∀ e, (g e).length = 4) (n : Nat) :
    ((List.range n).flatMap g).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [hg]
    omega

theorem getElem?_flatMap_range (g : Nat → List Nat) (hg : ∀ e, (g e).length = 4) {n x j : Nat}
    (hx : x < n) (hj : j < 4) : ((List.range n).flatMap g)[4 * x + j]? = (g x)[j]? := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases h : x < n
    · rw [List.getElem?_append_left (by rw [length_flatMap_range g hg]; omega), ih h]
    · have e : x = n := by omega
      subst e
      rw [List.getElem?_append_right (by rw [length_flatMap_range g hg]; omega),
        length_flatMap_range g hg]
      simp

theorem length_bytes4 (v : Nat) : (bytes4 v).length = 4 := rfl

/-- A table's entry, in the bytes of its global. -/
theorem lookup {init : Array Nat} {off n : Nat} {f : Nat → Nat}
    (h : (init.toList.drop off).take (4 * n) = (List.range n).flatMap fun e => bytes4 (f e))
    {x j : Nat} (hx : x < n) (hj : j < 4) : init[off + (4 * x + j)]? = (bytes4 (f x))[j]? := by
  have h1 := getElem?_flatMap_range (fun e => bytes4 (f e)) (fun e => length_bytes4 _) hx hj
  rw [← h, List.getElem?_take, ite_eq_left (by omega), List.getElem?_drop] at h1
  simpa using h1

theorem load_entry {m : Mem} {block s off n x v : Nat} {init : Array Nat} {f : Nat → Nat}
    (hA : m.allocs block = some { size := s, readonly := true, bytes := Mem.globalBytes init })
    (h : (init.toList.drop off).take (4 * n) = (List.range n).flatMap fun e => bytes4 (f e))
    (hx : x < n) (hv : f x = v) (hlt : v < 4294967296) (hs : off + 4 * n ≤ s) (hmax : s < 2 ^ 64)
    (halign : (m.addr ⟨block, BitVec.ofNat 64 (off + 4 * x), []⟩).toNat % 4 = 0) :
    Mem.loadInt 32 m (some ⟨block, BitVec.ofNat 64 (off + 4 * x), []⟩) 4 =
      Outcome.ok (some (BitVec.ofNat 32 v)) := by
  have l0 := lookup h hx (j := 0) (by omega)
  have l1 := lookup h hx (j := 1) (by omega)
  have l2 := lookup h hx (j := 2) (by omega)
  have l3 := lookup h hx (j := 3) (by omega)
  have hoff : (BitVec.ofNat 64 (off + 4 * x)).toNat = off + 4 * x := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have fits : ¬ off + 4 * x + 32 / 8 > s := by omega
  have b0 : init[off + 4 * x + 0]? = some (v % 256) := by subst hv; simpa [bytes4] using l0
  have b1 : init[off + 4 * x + 1]? = some (v / 256 % 256) := by subst hv; simpa [bytes4, Nat.add_assoc] using l1
  have b2 : init[off + 4 * x + 2]? = some (v / 65536 % 256) := by subst hv; simpa [bytes4, Nat.add_assoc] using l2
  have b3 : init[off + 4 * x + 3]? = some (v / 16777216 % 256) := by subst hv; simpa [bytes4, Nat.add_assoc] using l3
  have g0 : ¬ (v % 256 > 255) := by omega
  have g1 : ¬ (v / 256 % 256 > 255) := by omega
  have g2 : ¬ (v / 65536 % 256 > 255) := by omega
  have g3 : ¬ (v / 16777216 % 256 > 255) := by omega
  have total : v % 256 + 256 * (v / 256 % 256 + 256 * (v / 65536 % 256 + 256 * (v / 16777216 % 256 + 256 * 0))) = v := by
    omega
  have t0 : (BitVec.ofNat 8 (v % 256)).toNat = v % 256 := by simp [BitVec.toNat_ofNat]
  have t1 : (BitVec.ofNat 8 (v / 256 % 256)).toNat = v / 256 % 256 := by simp [BitVec.toNat_ofNat]
  have t2 : (BitVec.ofNat 8 (v / 65536 % 256)).toNat = v / 65536 % 256 := by simp [BitVec.toNat_ofNat]
  have t3 : (BitVec.ofNat 8 (v / 16777216 % 256)).toNat = v / 16777216 % 256 := by simp [BitVec.toNat_ofNat]
  have hc : m.check ⟨block, BitVec.ofNat 64 (off + 4 * x), []⟩
      { size := s, readonly := true, bytes := Mem.globalBytes init } false = none :=
    Mem.check_constant rfl rfl
  simp only [Mem.loadInt, Mem.access, hA, hoff, fits, ite_false, halign, Mem.read, Mem.visible]
  have hw : ∀ o', m.unwritten ⟨block, BitVec.ofNat 64 (off + 4 * x), []⟩
      { size := s, readonly := true, bytes := Mem.globalBytes init } o' = false :=
    fun _ => Mem.unwritten_constant rfl
  have e0 : Mem.globalBytes init (off + 4 * x + 0) = .val (BitVec.ofNat 8 (v % 256)) := by
    simp only [Mem.globalBytes, b0, g0, ite_false]
  have e1 : Mem.globalBytes init (off + 4 * x + 1) = .val (BitVec.ofNat 8 (v / 256 % 256)) := by
    simp only [Mem.globalBytes, b1, g1, ite_false]
  have e2 : Mem.globalBytes init (off + 4 * x + 2) = .val (BitVec.ofNat 8 (v / 65536 % 256)) := by
    simp only [Mem.globalBytes, b2, g2, ite_false]
  have e3 : Mem.globalBytes init (off + 4 * x + 3) = .val (BitVec.ofNat 8 (v / 16777216 % 256)) := by
    simp only [Mem.globalBytes, b3, g3, ite_false]
  have c : ((4 : Nat) != 1 && (0 : Nat) != 0) = false := rfl
  simp only [List.range, List.range.loop, List.map, c, Bool.false_eq_true, ite_false, hoff, hc, hw, e0, e1, e2,
    e3, Mem.collect, t0, t1, t2, t3, total]

theorem addr_align {m : Mem} {block k : Nat} (hb : block ≠ 0) (ha : (m.base block).toNat % 4 = 0)
    : (m.addr ⟨block, BitVec.ofNat 64 (4 * k), []⟩).toNat % 4 = 0 := by
  have h : (block == 0) = false := by simpa using hb
  simp only [Mem.addr, h, Bool.false_eq_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mul4 {x : BitVec 64} (hx : x.toNat < 256) :
    Val.mul (some x) (some 4#64) (nuw := true) (nsw := true) = some (BitVec.ofNat 64 (4 * x.toNat)) := by
  have h' : x < 256#64 := by simpa [BitVec.lt_def] using hx
  have h1 : x.umulOverflow 4#64 = false := by bv_decide
  have h2 : x.smulOverflow 4#64 = false := by bv_decide
  have e : x * 4#64 = BitVec.ofNat 64 (4 * x.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  simp [Val.mul, h1, h2, e]

/-- Reads an entry of a table of 256 at offset `off` of a read-only global, as the optimizer leaves that. -/
theorem load {m : Mem} {P : Ptr} {init : Array Nat} {s off : Nat} {f : Nat → Nat} {x : BitVec 64}
    (hA : m.allocs P.block = some { size := s, readonly := true, bytes := Mem.globalBytes init })
    (hP : P.offset = BitVec.ofNat 64 off) (hPt : P.tags = []) (hb : P.block ≠ 0)
    (h : (init.toList.drop off).take 1024 = (List.range 256).flatMap fun e => bytes4 (f e))
    (hs : off + 1024 ≤ s) (hmax : s < 2 ^ 64) (h4 : off % 4 = 0)
    (ha : (m.base P.block).toNat % 4 = 0) (hfit : (m.base P.block).toNat + s < 2 ^ 64)
    (hx : x.toNat < 256) (hlt : f x.toNat < 4294967296) :
    Mem.loadInt 32 m
        (Mem.gep m (some P) (Val.mul (some x) (some 4#64) (nuw := true) (nsw := true))
          (inbounds := true) (nuw := true)) 4 =
      Outcome.ok (some (BitVec.ofNat 32 (f x.toNat))) := by
  have hal : (m.addr ⟨P.block, BitVec.ofNat 64 (off + 4 * x.toNat), []⟩).toNat % 4 = 0 := by
    have e : off + 4 * x.toNat = 4 * (off / 4 + x.toNat) := by omega
    rw [e]
    exact addr_align hb ha
  have hload := load_entry (n := 256) hA h hx rfl hlt (by omega) hmax hal
  have toff : (BitVec.ofNat 64 off).toNat = off := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have td : (BitVec.ofNat 64 (4 * x.toNat)).toNat = 4 * x.toNat := by
    simp only [BitVec.toNat_ofNat]; omega
  have hsum : BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * x.toNat) = BitVec.ofNat 64 (off + 4 * x.toNat) := by
    simp [BitVec.ofNat_add]
  have hb' : (P.block == 0) = false := by simpa using hb
  have haddr : (m.addr P).toNat + 4 * x.toNat < 2 ^ 64 := by
    simp only [Mem.addr, hb', Bool.false_eq_true, ite_false, BitVec.toNat_add, hP, toff]
    omega
  have hgep : Mem.gep m (some P) (some (BitVec.ofNat 64 (4 * x.toNat))) (inbounds := true) (nuw := true) =
      some ⟨P.block, BitVec.ofNat 64 (off + 4 * x.toNat), []⟩ := by
    rw [Mem.gep_forward hA (by simp only [hP, toff]; omega) hmax haddr (by omega), hP, hsum]
    cases P; simp_all
  rw [mul4 hx, hgep, hload]

end Table

end IRLean
