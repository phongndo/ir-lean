import Kit

/-! Arrays of 64-bit words in memory, which is how `llvm::APInt` holds a number too big for one. -/

set_option linter.unusedSimpArgs false

namespace IRLean

/-- The bytes of an array of words, least significant first. -/
def wordBytes (w : Nat → BitVec 64) (i : Nat) : BitVec 8 := BitVec.ofNat 8 ((w (i / 8)).toNat >>> (8 * (i % 8)))

/-- `n` words at offset `o` of allocation `block`, holding `w`, that a pointer tagged `t` may read. -/
structure Words (m : Mem) (t : List Tag) (block o n : Nat) (w : Nat → BitVec 64) : Prop where
  bytes : Reachable m t block o (8 * n) (wordBytes w)
  align : (m.addr (bufPtr t block o 0)).toNat % 8 = 0

namespace Words

variable {m : Mem} {t : List Tag} {block o n : Nat} {w : Nat → BitVec 64}

theorem bytes_sum (x : BitVec 64) :
    (BitVec.ofNat 8 (x.toNat >>> (8 * 0))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 1))).toNat + 256 *
      ((BitVec.ofNat 8 (x.toNat >>> (8 * 2))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 3))).toNat + 256 *
      ((BitVec.ofNat 8 (x.toNat >>> (8 * 4))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 5))).toNat + 256 *
      ((BitVec.ofNat 8 (x.toNat >>> (8 * 6))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 7))).toNat + 256 * 0))))))) =
      x.toNat := by
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  omega

/-- Reads a word. -/
theorem load (W : Words m t block o n w) {i : Nat} (h : i < n) :
    Mem.loadInt 64 m (some (bufPtr t block o (8 * i))) 8 = Outcome.ok (some (w i)) := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := W.bytes.alloc
  have hoff : (BitVec.ofNat 64 (o + 8 * i)).toNat = o + 8 * i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have fits : ¬ o + 8 * i + 64 / 8 > a.size := by omega
  have hc := W.bytes.allowed a ha (BitVec.ofNat 64 (o + 8 * i))
  have hal : (m.addr (bufPtr t block o (8 * i))).toNat % 8 = 0 := by
    rw [W.bytes.toNat_addr (by omega)]
    have := W.align
    omega
  have hb : ∀ j, j < 8 → m.visible (bufPtr t block o (8 * i)) a (o + 8 * i + j) =
      .val (BitVec.ofNat 8 ((w i).toNat >>> (8 * j))) := by
    intro j hj
    have hw := W.bytes.clean a ha (8 * i + j) (by omega) (BitVec.ofNat 64 (o + 8 * i))
    have hv := hd (8 * i + j) (by omega)
    have e1 : o + (8 * i + j) = o + 8 * i + j := by omega
    rw [e1] at hw hv
    have e2 : (8 * i + j) / 8 = i := by omega
    have e3 : (8 * i + j) % 8 = j := by omega
    simp only [Mem.visible, bufPtr, hw, Bool.false_eq_true, ite_false, hv, wordBytes, e2, e3]
  simp only [Mem.loadInt, Mem.access, ha, bufPtr, hoff, fits, Mem.read]
  have hal' : (m.addr { block := block, offset := BitVec.ofNat 64 (o + 8 * i), tags := t }).toNat % 8 = 0 := hal
  have hc' := hc
  simp only [List.range, List.range.loop, List.map]
  have e0 := hb 0 (by omega)
  have e1 := hb 1 (by omega)
  have e2 := hb 2 (by omega)
  have e3 := hb 3 (by omega)
  have e4 := hb 4 (by omega)
  have e5 := hb 5 (by omega)
  have e6 := hb 6 (by omega)
  have e7 := hb 7 (by omega)
  simp only [bufPtr] at e0 e1 e2 e3 e4 e5 e6 e7
  have hne : ((8 : Nat) != 1 && (m.addr { block := block, offset := BitVec.ofNat 64 (o + 8 * i), tags := t }).toNat % 8 != 0) = false := by
    rw [hal']; rfl
  simp only [hne, Bool.false_eq_true, ite_false, hc', hoff, e0, e1, e2, e3, e4, e5, e6, e7, Mem.collect]
  have hsum := bytes_sum (w i)
  simp only [hsum, Outcome.ok, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Finds a word by its index, as the optimizer leaves that. -/
theorem index (W : Words m t block o n w) {idx : BitVec 64} (h : idx.toNat < n) :
    Mem.gep m (some (bufPtr t block o 0)) (Val.mul (some idx) (some 8#64) (nuw := true) (nsw := true))
      (inbounds := true) (nuw := true) = some (bufPtr t block o (8 * idx.toNat)) := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := W.bytes.alloc
  have hsmall : idx < 1152921504606846976#64 := by
    show idx.toNat < _
    simp only [BitVec.toNat_ofNat]
    omega
  have hmul : Val.mul (some idx) (some 8#64) (nuw := true) (nsw := true) = some (BitVec.ofNat 64 (8 * idx.toNat)) := by
    rw [Val.mul_ok (by bv_decide)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  rw [hmul]
  have := W.bytes.gep (i := 0) (k := 8 * idx.toNat) (by omega)
  rwa [Nat.zero_add] at this

/-- The same, for an index that's a loop counter. -/
theorem index' (W : Words m t block o n w) {i : Nat} (h : i < n) :
    Mem.gep m (some (bufPtr t block o 0)) (Val.mul (some (BitVec.ofNat 64 i)) (some 8#64) (nuw := true) (nsw := true))
      (inbounds := true) (nuw := true) = some (bufPtr t block o (8 * i)) := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := W.bytes.alloc
  have hi : (BitVec.ofNat 64 i).toNat = i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have := W.index (idx := BitVec.ofNat 64 i) (by rw [hi]; exact h)
  rwa [hi] at this

/-- A word array stays readable inside a call that may read through its arguments and only adds a tag that allows it. -/
theorem enter (W : Words m t block o n w) {e : Effects} (he : e.arg = .read ∨ e.arg = .readwrite)
    {T : Tag} (hT : T.call = m.nextCall) (hn : T.readnone = false) (hw : T.writeonly = false)
    (hi : T.initializes = false) :
    Words (m.inCall e) (T :: t) block o n w :=
  ⟨W.bytes.enter he hT hn hw hi, W.align⟩

end Words

theorem add_one {i : Nat} (h : i < 2 ^ 61) :
    Val.add (some (BitVec.ofNat 64 i)) (some 1#64) (nuw := true) (nsw := true) = some (BitVec.ofNat 64 (i + 1)) := by
  have hi : (BitVec.ofNat 64 i).toNat = i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hs : BitVec.ofNat 64 i < 2305843009213693952#64 := by
    show (BitVec.ofNat 64 i).toNat < _
    rw [hi]
    simpa using h
  generalize hx : BitVec.ofNat 64 i = x at hs
  rw [Val.add_ok (by bv_decide), ← hx]
  simp [BitVec.ofNat_add]

/-! ### Writing -/

/-- Memory with `n` words at offset `o` of `block` set to `f`, and nothing else changed. -/
def Mem.setWords (m : Mem) (block o n : Nat) (f : Nat → BitVec 64) : Mem :=
  match m.allocs block with
  | some a => m.setAlloc block (some { a with
      bytes := fun i => if o ≤ i ∧ i < o + 8 * n then .val (wordBytes f (i - o)) else a.bytes i })
  | none => m

/-- Something to write to: no running call tracks writes, and neither a tag on the pointer nor a promise stops this one. -/
structure Writable (m : Mem) (t : List Tag) (block : Nat) : Prop where
  notConst : ∀ a, m.allocs block = some a → a.readonly = false
  allowed : ∀ a, m.allocs block = some a → ∀ off, m.check ⟨block, off, t⟩ a true = none
  untracked : ∀ c, c ∈ m.calls → c.tracked = false

theorem Mem.ext' {x y : Mem} (h1 : x.allocs = y.allocs) (h2 : x.next = y.next) (h3 : x.base = y.base) (h4 : x.frame = y.frame)
    (h5 : x.failAlloc = y.failAlloc) (h6 : x.calls = y.calls) (h7 : x.nextCall = y.nextCall) : x = y := by
  cases x
  cases y
  simp_all

namespace Words

variable {m : Mem} {t : List Tag} {block o n : Nat} {w f : Nat → BitVec 64}

theorem check_same {q : Ptr} {a a' : Alloc} {write : Bool} (hr : a'.readonly = a.readonly) (hs : a'.stack = a.stack) :
    m.check q a' write = m.check q a write := by
  have hc : ∀ c, Mem.callRule c q a' write = Mem.callRule c q a write := by
    intro c
    simp only [Mem.callRule, Mem.callAccess, hr, hs]
  simp only [Mem.check, hc]

/-- Words written are there to read, and the tags that could read them still can. -/
theorem set (W : Words m t block o n w) (V : Writable m t block) (f : Nat → BitVec 64) :
    Words (m.setWords block o n f) t block o n f := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := W.bytes.alloc
  have hset : m.setWords block o n f = m.setAlloc block (some { a with
      bytes := fun i => if o ≤ i ∧ i < o + 8 * n then .val (wordBytes f (i - o)) else a.bytes i }) := by
    simp only [Mem.setWords, ha]
  rw [hset]
  have hcalls : (m.setAlloc block (some { a with
      bytes := fun i => if o ≤ i ∧ i < o + 8 * n then .val (wordBytes f (i - o)) else a.bytes i })).calls = m.calls := rfl
  have hnew : (m.setAlloc block (some { a with
      bytes := fun i => if o ≤ i ∧ i < o + 8 * n then .val (wordBytes f (i - o)) else a.bytes i })).allocs block =
      some { a with bytes := fun i => if o ≤ i ∧ i < o + 8 * n then .val (wordBytes f (i - o)) else a.bytes i } := by
    simp [Mem.setAlloc]
  refine ⟨⟨⟨_, hnew, hsz, hmax, fun i hi => ?_⟩, W.bytes.fits, fun a' ha' off => ?_, fun a' ha' i hi off => ?_,
    W.bytes.tagsOld, W.bytes.callsOld⟩, W.align⟩
  · simp only
    rw [ite_eq_left ⟨by omega, by omega⟩]
    simp
  · rw [hnew] at ha'
    cases ha'
    have := W.bytes.allowed a ha off
    rw [← this]
    exact check_same rfl rfl
  · rw [hnew] at ha'
    cases ha'
    have hu : ∀ c, c ∈ m.calls → c.tracked = false := V.untracked
    simp only [Mem.unwritten, hcalls]
    rw [List.any_eq_false]
    intro c hc
    simp [hu c hc]

/-- An array with word `i` changed. -/
def setWord (f : Nat → BitVec 64) (i : Nat) (v : BitVec 64) : Nat → BitVec 64 := fun j => if j = i then v else f j

theorem storeInt_eq {S : Mem} {q : Ptr} {a' : Alloc} (hA : S.allocs q.block = some a') (hfit : q.offset.toNat + 8 ≤ a'.size)
    (hal : (S.addr q).toNat % 8 = 0) (hro : a'.readonly = false) (hc : S.check q a' true = none) (v : BitVec 64) :
    Mem.storeInt S (some q) (some v) 8 = Outcome.ok (S.write q a' 8 fun i => Mem.intByte v i) := by
  have hne : ((8 : Nat) != 1 && (S.addr q).toNat % 8 != 0) = false := by
    rw [hal]; rfl
  have hf : ¬ q.offset.toNat + 64 / 8 > a'.size := by omega
  simp only [Mem.storeInt, Mem.access, hA, hf, hne, Bool.false_eq_true, ite_false, hro, hc, Nat.reduceDiv]

/-- Stores a word. -/
theorem store (W : Words m t block o n w) (V : Writable m t block) {i : Nat} (hi : i < n) (f : Nat → BitVec 64) (v : BitVec 64) :
    Mem.storeInt (m.setWords block o n f) (some (bufPtr t block o (8 * i))) (some v) 8 =
      Outcome.ok (m.setWords block o n (setWord f i v)) := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := W.bytes.alloc
  have hal : (m.addr (bufPtr t block o (8 * i))).toNat % 8 = 0 := by
    rw [W.bytes.toNat_addr (by omega)]
    have := W.align
    omega
  have hoff : (BitVec.ofNat 64 (o + 8 * i)).toNat = o + 8 * i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hset : ∀ g : Nat → BitVec 64, m.setWords block o n g = m.setAlloc block (some { a with
      bytes := fun x => if o ≤ x ∧ x < o + 8 * n then .val (wordBytes g (x - o)) else a.bytes x }) := by
    intro g
    simp only [Mem.setWords, ha]
  have hro := V.notConst a ha
  have hc := V.allowed a ha (BitVec.ofNat 64 (o + 8 * i))
  rw [hset f, hset (setWord f i v)]
  generalize hb : (fun x => if o ≤ x ∧ x < o + 8 * n then Byte.val (wordBytes f (x - o)) else a.bytes x) = old
  have hcheck : (m.setAlloc block (some { a with bytes := old })).check
      ⟨block, BitVec.ofNat 64 (o + 8 * i), t⟩ { a with bytes := old } true = none := by
    rw [← hc]
    have hrule : (m.setAlloc block (some { a with bytes := old })).tagRule true = m.tagRule true := rfl
    simp only [Mem.check]
    rw [hrule]
    rfl
  rw [storeInt_eq (S := m.setAlloc block (some { a with bytes := old })) (q := bufPtr t block o (8 * i))
    (a' := { a with bytes := old }) (by simp [Mem.setAlloc])
    (by simp only [hoff]; omega) hal hro hcheck v]
  have hcalls : ∀ (l : List Call) (g : Call → Call), (∀ c, c ∈ l → g c = c) → l.map g = l := by
    intro l g h
    induction l with
    | nil => rfl
    | cons c l ih =>
      simp only [List.map_cons, h c (List.mem_cons_self), ih (fun x hx => h x (List.mem_cons_of_mem c hx))]
  simp only [Mem.write, Mem.setAlloc, Outcome.ok, hoff]
  rw [hcalls m.calls _ (fun c hc => by simp [V.untracked c hc])]
  congr 3
  funext b'
  by_cases hb' : b' = block
  · subst hb'
    simp only [beq_self_eq_true, ite_true, Option.some.injEq, Alloc.mk.injEq, true_and, and_true]
    congr 2
    funext x
    subst hb
    by_cases h1 : o + 8 * i ≤ x ∧ x < o + 8 * i + 8
    · have h2 : o ≤ x ∧ x < o + 8 * n := ⟨by omega, by omega⟩
      have e1 : (x - o) / 8 = i := by omega
      have e2 : (x - o) % 8 = x - (o + 8 * i) := by omega
      rw [ite_eq_left h1, ite_eq_left h2]
      simp only [wordBytes, setWord, e1, e2, ite_true, Mem.intByte]
    · rw [ite_eq_right h1]
      dsimp only
      by_cases h2 : o ≤ x ∧ x < o + 8 * n
      · have e1 : (x - o) / 8 ≠ i := by omega
        rw [ite_eq_left h2, ite_eq_left h2]
        simp only [wordBytes, setWord, e1, ite_false]
      · rw [ite_eq_right h2, ite_eq_right h2]
  · simp [hb']

theorem base_setWords (block o n : Nat) (f : Nat → BitVec 64) : (m.setWords block o n f).base = m.base := by
  simp only [Mem.setWords]
  split <;> rfl

/-- Writing a word through a pointer, whatever the running calls do about it, leaves the allocations as `setWords` says. -/
theorem write_allocs {s : Alloc} (hs : m.allocs block = some s) (hoff : (BitVec.ofNat 64 (o + 8 * 0)).toNat = o + 8 * 0)
    (t : List Tag) (v : BitVec 64) :
    (m.write (bufPtr t block o (8 * 0)) s 8 (fun i => Mem.intByte v i)).allocs =
      (m.setWords block o 1 (fun _ => v)).allocs := by
  simp only [Mem.write, bufPtr, hoff, Mem.setAlloc, Mem.setWords, hs]
  funext b
  by_cases hb : b = block
  · subst hb
    simp only [beq_self_eq_true, ite_true, Option.some.injEq, Alloc.mk.injEq, true_and, and_true]
    funext x
    by_cases h1 : o ≤ x ∧ x < o + 8 * 1
    · have h1' : o + 8 * 0 ≤ x ∧ x < o + 8 * 0 + 8 := ⟨by omega, by omega⟩
      rw [ite_eq_left h1', ite_eq_left h1]
      have e : (x - o) % 8 = x - (o + 8 * 0) := by omega
      simp only [wordBytes, e, Mem.intByte]
    · have h1' : ¬ (o + 8 * 0 ≤ x ∧ x < o + 8 * 0 + 8) := by omega
      rw [ite_eq_right h1', ite_eq_right h1]
  · simp [hb]

/-- Setting words doesn't change another allocation, or what a pointer may do with it. -/
theorem Reachable_set {t' : List Tag} {block' o' n' : Nat} {data : Nat → BitVec 8}
    (B : Reachable m t' block' o' n' data) (hb : block' ≠ block) (f : Nat → BitVec 64) :
    Reachable (m.setWords block o n f) t' block' o' n' data := by
  have hsame : (m.setWords block o n f).allocs block' = m.allocs block' ∧ (m.setWords block o n f).calls = m.calls ∧
      (m.setWords block o n f).base = m.base ∧ (m.setWords block o n f).nextCall = m.nextCall := by
    simp only [Mem.setWords]
    split
    · simp [Mem.setAlloc, hb]
    · simp
  obtain ⟨h1, h2, h3, h4⟩ := hsame
  obtain ⟨halloc, hfits, hallowed, hclean, htags, hold⟩ := B
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]; exact halloc
  · simpa [Mem.addr, h3] using hfits
  · intro a ha off
    rw [h1] at ha
    have hrule : (m.setWords block o n f).tagRule false = m.tagRule false := by
      funext x
      unfold Mem.tagRule Mem.isRunning
      rw [h2]
    have := hallowed a ha off
    simp only [Mem.check] at this ⊢
    rw [hrule, h2]
    exact this
  · intro a ha i hi off
    rw [h1] at ha
    have := hclean a ha i hi off
    simpa [Mem.unwritten, h2] using this
  · rw [h4]; exact htags
  · rw [h2, h4]; exact hold

/-- A word array in another allocation stays as it is when words are set. -/
theorem set_other {t' : List Tag} {block' o' n' : Nat} {x : Nat → BitVec 64}
    (W : Words m t' block' o' n' x) (hb : block' ≠ block) (f : Nat → BitVec 64) :
    Words (m.setWords block o n f) t' block' o' n' x :=
  ⟨Reachable_set W.bytes hb f, by simpa [Mem.addr, base_setWords] using W.align⟩

/-- Only the first `n` words count. -/
theorem setWords_congr {f g : Nat → BitVec 64} (h : ∀ j, j < n → f j = g j) :
    m.setWords block o n f = m.setWords block o n g := by
  simp only [Mem.setWords]
  split
  · congr 3
    funext x
    by_cases hx : o ≤ x ∧ x < o + 8 * n
    · have e : (x - o) / 8 < n := by omega
      rw [ite_eq_left hx, ite_eq_left hx]
      simp only [wordBytes, h _ e]
    · rw [ite_eq_right hx, ite_eq_right hx]
  · rfl

/-- Setting words to what they already are changes nothing. -/
theorem setWords_self (W : Words m t block o n w) : m.setWords block o n w = m := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := W.bytes.alloc
  simp only [Mem.setWords, ha, Mem.setAlloc]
  have hallocs : (fun b => if (b == block) = true then some { a with
      bytes := fun x => if o ≤ x ∧ x < o + 8 * n then Byte.val (wordBytes w (x - o)) else a.bytes x } else m.allocs b) = m.allocs := by
    funext b
    by_cases hb : b = block
    · subst hb
      simp only [beq_self_eq_true, ite_true, ha, Option.some.injEq]
      cases a with
      | mk size readonly bytes heap stack =>
        simp only [Alloc.mk.injEq, and_true, true_and]
        funext x
        by_cases hx : o ≤ x ∧ x < o + 8 * n
        · rw [ite_eq_left hx]
          have := hd (x - o) (by omega)
          rw [show o + (x - o) = x by omega] at this
          exact this.symm
        · rw [ite_eq_right hx]
    · simp [hb]
  rw [hallocs]

/-- Setting words inside a call is the same as setting them before it. -/
theorem setWords_inCall (e : Effects) (f : Nat → BitVec 64) :
    (m.inCall e).setWords block o n f = (m.setWords block o n f).inCall e := by
  simp only [Mem.setWords, Mem.inCall]
  split <;> rfl

end Words

/-- The number an array of `n` words holds, least significant word first. -/
def wordsValue (w : Nat → BitVec 64) : Nat → Nat
  | 0 => 0
  | n + 1 => wordsValue w n + (w n).toNat * 2 ^ (64 * n)

theorem wordsValue_lt (w : Nat → BitVec 64) (n : Nat) : wordsValue w n < 2 ^ (64 * n) := by
  induction n with
  | zero => simp [wordsValue]
  | succ n ih =>
    have hp : 2 ^ (64 * (n + 1)) = 18446744073709551616 * 2 ^ (64 * n) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    have hw := (w n).isLt
    have hm : ((w n).toNat + 1) * 2 ^ (64 * n) ≤ 18446744073709551616 * 2 ^ (64 * n) :=
      Nat.mul_le_mul_right _ hw
    rw [Nat.succ_mul] at hm
    simp only [wordsValue]
    omega

theorem sub_one {i : Nat} (h : i < 2 ^ 61) :
    Val.add (some (BitVec.ofNat 64 (i + 1))) (some 18446744073709551615#64) (nsw := true) = some (BitVec.ofNat 64 i) := by
  have hi : (BitVec.ofNat 64 i).toNat = i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hs : BitVec.ofNat 64 i < 2305843009213693952#64 := by
    show (BitVec.ofNat 64 i).toNat < _
    rw [hi]
    simpa using h
  have e : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 i + 1#64 := by simp [BitVec.ofNat_add]
  rw [e]
  generalize BitVec.ofNat 64 i = x at hs ⊢
  have hadd : Val.add (some (x + 1#64)) (some 18446744073709551615#64) (nsw := true) = some (x + 1#64 + 18446744073709551615#64) := by
    apply Val.add_ok
    bv_decide
  have hx : x + 1#64 + 18446744073709551615#64 = x := by bv_decide
  rw [hadd, hx]

/-- A number's words above `i` being the same as another's means the rest decides how they compare. -/
theorem wordsValue_lt_of_top {w x : Nat → BitVec 64} {i : Nat} (hlt : (w i).toNat < (x i).toNat) (n : Nat) :
    (∀ j, i < j → j < i + 1 + n → w j = x j) → wordsValue w (i + 1 + n) < wordsValue x (i + 1 + n) := by
  induction n with
  | zero =>
    intro _
    have hw := wordsValue_lt w i
    have hm : ((w i).toNat + 1) * 2 ^ (64 * i) ≤ (x i).toNat * 2 ^ (64 * i) := Nat.mul_le_mul_right _ hlt
    rw [Nat.succ_mul] at hm
    simp only [wordsValue]
    omega
  | succ n ih =>
    intro h
    have h1 := ih (fun j hj hj' => h j hj (by omega))
    have e : i + 1 + (n + 1) = (i + 1 + n) + 1 := rfl
    rw [e]
    simp only [wordsValue]
    rw [h (i + 1 + n) (by omega) (by omega)]
    omega

theorem wordsValue_congr {w x : Nat → BitVec 64} (n : Nat) (h : ∀ j, j < n → w j = x j) : wordsValue w n = wordsValue x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wordsValue]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem wordsValue_eq_zero (w : Nat → BitVec 64) (n : Nat) : wordsValue w n = 0 ↔ ∀ j, j < n → w j = 0#64 := by
  induction n with
  | zero => simp [wordsValue]
  | succ n ih =>
    have hp : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
    simp only [wordsValue]
    constructor
    · intro h j hj
      have h1 : wordsValue w n = 0 := by omega
      have h2 : (w n).toNat * 2 ^ (64 * n) = 0 := by omega
      have h3 : (w n).toNat = 0 := by
        rcases Nat.mul_eq_zero.mp h2 with h | h
        · exact h
        · omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact (ih.mp h1) j hj
      · exact BitVec.eq_of_toNat_eq (by simpa using h3)
    · intro h
      have h1 := ih.mpr (fun j hj => h j (by omega))
      rw [h1, h n (by omega)]
      simp

end IRLean
