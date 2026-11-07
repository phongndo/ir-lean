import Crc.crc32_z
import CrcSpec

/-! zlib's `crc32_z`, as clang compiles it at `-O2`, proved safe and correct against RFC 1952.
`tests/proofs.sh` regenerates `Crc` from zlib's own source.

The code is the braided version: at each step five lanes each take in a word, with table reads doing
320 bit steps at once, and the last block combines the lanes. This works because CRC steps are linear
over xor. -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

open IRLean Crc

namespace CrcProof

/-! ### Running the blocks, from the end backward -/

variable {m : Mem} {ts : List Tag}

/-- A word's round of `crc_word`, folded back into steps. -/
theorem round_word' (x : BitVec 64) :
    (x >>> 8#64) ^^^ (entryV 8 (x &&& 255#64)).setWidth 64 = steps 8 x := by
  rw [zext_entry 8 (by have := and255 x; omega), round_word]

/-- The same, when the optimizer has moved the round's last step in among the next word's bytes. -/
theorem round_mid (y x : BitVec 64) :
    y ^^^ (entryV 8 (x &&& 255#64)).setWidth 64 ^^^ x >>> 8#64 = y ^^^ steps 8 x := by
  rw [BitVec.xor_assoc, BitVec.xor_comm ((entryV 8 _).setWidth 64), round_word']

theorem toNat_and7 (x : BitVec 64) : (x &&& 7#64).toNat = x.toNat % 8 := by
  have := Nat.and_two_pow_sub_one_eq_mod x.toNat 3
  simp [BitVec.toNat_and]
  simpa using this

/-- A byte's round. -/
theorem round_byte (x : BitVec 64) (b : BitVec 8) :
    (x >>> 8#64) ^^^ (entryV 8 ((b ^^^ x.setWidth 8).setWidth 64)).setWidth 64 =
      steps 8 (x ^^^ b.setWidth 64) := by
  rw [zext_entry 8 (by have := zext8 (b ^^^ x.setWidth 8); omega), ← round_word (x ^^^ b.setWidth 64)]
  have e1 : (x ^^^ b.setWidth 64) >>> 8#64 = x >>> 8#64 := by bv_decide
  have e2 : (x ^^^ b.setWidth 64) &&& 255#64 = (b ^^^ x.setWidth 8).setWidth 64 := by bv_decide
  rw [e1, e2]

theorem spec_byte (s0 : BitVec 64) (d : Nat → BitVec 8) (i : Nat) :
    steps 8 (spec s0 d i ^^^ (d i).setWidth 64) = spec s0 d (i + 1) := rfl

theorem spec_lt {s0 : BitVec 64} (hs : s0.toNat < 4294967296) (d : Nat → BitVec 8) (i : Nat) :
    (spec s0 d i).toNat < 4294967296 := by
  induction i with
  | zero => exact hs
  | succ i ih =>
    apply steps_lt
    have h : spec s0 d i < 4294967296#64 := by rw [BitVec.lt_def]; simpa using ih
    have h2 : spec s0 d i ^^^ (d i).setWidth 64 < 4294967296#64 := by bv_decide
    simpa [BitVec.lt_def] using h2

theorem range32 {x : BitVec 64} (h : x.toNat < 4294967296) :
    Val.range 0#64 4294967296#64 (some x) = some x := by
  have h' : BitVec.ult (x - 0#64) (4294967296#64 - 0#64) = true := by
    simp [BitVec.ult]; omega
  simp only [Val.range, h', ite_true]

theorem udiv40 (L : BitVec 64) : Val.udiv (some L) (some 40#64) = Outcome.ok (some (L / 40#64)) := by
  simp [Val.udiv]

/-- `div - 1`, whose `nsw` holds because a byte count over 40 is well below the sign bit. -/
theorem dec1_nsw {D : BitVec 64} (h : D.toNat < 4611686018427387904) :
    Val.add (some D) (some 18446744073709551615#64) (nsw := true) =
      some (D + 18446744073709551615#64) := by
  have h' : D < 4611686018427387904#64 := by simpa [BitVec.lt_def] using h
  have : D.saddOverflow 18446744073709551615#64 = false := by bv_decide
  simp [Val.add, this]

theorem trunc32 {x : BitVec 64} (h : x.toNat < 4294967296) :
    Val.trunc 32 (some x) (nuw := true) = some (x.setWidth 32) := by
  have e : (x.setWidth 32).setWidth 64 = x := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    omega
  simp [Val.trunc, e]

/-- Looking at the buffer pointer's address breaks no promise. -/
theorem Tables.observe {m : Mem} {ts : List Tag} (T : Tables m ts) (block o i : Nat) (k : Outcome α) :
    Mem.observeAddress (some (bufPtr ts block o i)) false k = k := by
  have h : ts.any (fun x => x.noAddress && !(false && x.nullCheck)) = false := by
    rw [List.any_eq_false]
    intro x hx
    simp [T.addressFree x hx]
  simp only [Mem.observeAddress, h, Bool.false_eq_true, ite_false]

local notation "St" => Crc.crc32_z.step

/-- Runs one block: evaluates it on known values, folding the CRC rounds as they appear, and leaves
each branch condition as a fact about natural numbers. -/
syntax "exec " term ", " term : tactic
macro_rules
  | `(tactic| exec $b, $t) =>
    `(tactic| (rw [run]; simp (disch := omega) only [Crc.crc32_z.step, llvm_val, Val.trunc_some, lshr_lit,
        crc_and $t:term, crc_byte $t:term, braid0 $t:term, braid1 $t:term, braid2 $t:term,
        braid3 $t:term, braid4 $t:term, braid5 $t:term, braid6 $t:term, braid7 $t:term,
        Readable.load $b:term, Readable.gep $b:term, Readable.gep_plain, load64 $b:term,
        round_word', round_mid, round_byte, spec_byte, steps_steps, braid_lane, zext_xor32, select_and,
        toNat_and7, Mem.toVal, Tables.observe $t:term, udiv40, Val.mul_some, dec1_nsw, trunc32,
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        jump, ret, andThen, Outcome.ok, beq_toNat, bne_toNat, ult_toNat, decide_eq_true_eq,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.add_assoc]))

variable {block o n : Nat} {d : Nat → BitVec 8} {s0 : BitVec 64}

theorem while_end299_run (hs : s0.toNat < 4294967296) :
    run St (.while_end299 m (some (spec s0 d n))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have h := spec_lt hs d n
  have h1 : spec s0 d n < 4294967296#64 := by rw [BitVec.lt_def]; simpa using h
  have h2 : (spec s0 d n ^^^ 4294967295#64) < 4294967296#64 := by bv_decide
  have h3 : (spec s0 d n ^^^ 4294967295#64).toNat < 4294967296 := by simpa [BitVec.lt_def] using h2
  rw [run]
  simp only [Crc.crc32_z.step, llvm_val, jump, andThen, Outcome.ok]
  rw [run]
  simp only [Crc.crc32_z.step, range32 h3, ret, andThen, Outcome.ok]
  rfl

/-- The last bytes, one at a time, in the seven blocks clang unrolled them to. -/
theorem while_body289_6_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i : Nat} (hi : i + 7 = n) :
    run St (.while_body289_6 m (some (bufPtr ts block o i)) (some (spec s0 d (i + 6)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  subst hi
  exact while_end299_run hs

theorem while_body289_5_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 5 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289_5 m (some L) (some (bufPtr ts block o i)) (some (spec s0 d (i + 5)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 6 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_6_run B T hs (by omega)

theorem while_body289_4_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 4 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289_4 m (some L) (some (bufPtr ts block o i)) (some (spec s0 d (i + 4)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 5 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_5_run B T hs h0 (by omega) hi

theorem while_body289_3_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 3 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289_3 m (some L) (some (bufPtr ts block o i)) (some (spec s0 d (i + 3)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 4 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_4_run B T hs h0 (by omega) hi

theorem while_body289_2_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 2 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289_2 m (some L) (some (bufPtr ts block o i)) (some (spec s0 d (i + 2)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 3 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_3_run B T hs h0 (by omega) hi

theorem while_body289_1_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 1 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289_1 m (some L) (some (bufPtr ts block o i)) (some (spec s0 d (i + 1)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 2 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_2_run B T hs h0 (by omega) hi

theorem while_body289_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hL : 0 < L.toNat) (hi : i + L.toNat = n) :
    run St (.while_body289 m (some L) (some (bufPtr ts block o i)) (some (spec s0 d i))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i + 1 = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_1_run B T hs h0 (by omega) hi

theorem while_cond287_preheader_run (B : Readable m ts block o n d) (T : Tables m ts)
    (hs : s0.toNat < 4294967296) {i : Nat} {L : BitVec 64} (h0 : L.toNat ≤ 7) (hi : i + L.toNat = n) :
    run St (.while_cond287_preheader m (some L) (some (bufPtr ts block o i)) (some (spec s0 d i))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · have e : i = n := by omega
    subst e
    exact while_end299_run hs
  · exact while_body289_run B T hs h0 (by omega) hi

/-- Eight bytes at a time, while there are that many. -/
theorem while_body220_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    (r : Nat) :
    ∀ (i : Nat) (L : BitVec 64), 8 ≤ L.toNat → L.toNat < 8 * (r + 1) → i + L.toNat = n →
      run St (.while_body220 m (some (spec s0 d i)) (some (bufPtr ts block o i)) (some L)) =
        Outcome.ok (some (finish (spec s0 d n)), m) := by
  induction r with
  | zero => intro i L h8 hr; omega
  | succ r ih =>
    intro i L h8 hr hi
    have hdec : (L + 18446744073709551608#64).toNat = L.toNat - 8 :=
      toNat_dec 8 rfl (by omega) (by omega)
    exec B, T
    split
    · exact ih (i + 8) _ (by omega) (by omega) (by omega)
    · exact while_cond287_preheader_run B T hs (by omega) (by omega)

theorem if_end216_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (hi : i + L.toNat = n) :
    run St (.if_end216 m (some L) (some (bufPtr ts block o i)) (some (spec s0 d i))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  exec B, T
  split
  · exact while_body220_run B T hs (L.toNat / 8) i L (by omega) (by omega) hi
  · exact while_cond287_preheader_run B T hs (by omega) hi

theorem aligned_add {i k : Nat} (h : (m.addr (bufPtr ts block o i)).toNat % 8 = 0) (hk : k % 8 = 0)
    (hk' : k < 2 ^ 64) : (m.addr (bufPtr ts block o (i + k))).toNat % 8 = 0 := by
  rw [addr_bufPtr, addr_mod8 _ hk']
  omega

/-- The last block of the braid: combine the lanes. -/
theorem while_end80_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i : Nat} {L c0 c1 c2 c3 c4 : BitVec 64} (hi : i + 40 + L.toNat = n)
    (ha : (m.addr (bufPtr ts block o i)).toNat % 8 = 0) (h : Lanes s0 d i c0 c1 c2 c3 c4) :
    run St (.while_end80 m (some c2) (some c1) (some c3) (some c0) (some c4)
        (some (bufPtr ts block o i)) (some L)) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have a1 := aligned_add (k := 8) ha rfl (by decide)
  have a2 := aligned_add (k := 16) ha rfl (by decide)
  have a3 := aligned_add (k := 24) ha rfl (by decide)
  have a4 := aligned_add (k := 32) ha rfl (by decide)
  exec B, T
  rw [lanes_finish h]
  exact if_end216_run B T hs (by omega)

theorem mul40 {D : BitVec 64} (h : 40 * D.toNat < 2 ^ 64) :
    Val.mul (some D) (some 40#64) (nuw := true) = some (BitVec.ofNat 64 (40 * D.toNat)) := by
  have e : D * 40#64 = BitVec.ofNat 64 (40 * D.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  have hno : D.umulOverflow 40#64 = false := by
    simp only [BitVec.umulOverflow, BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le, ge_iff_le]
    omega
  simp [Val.mul, hno, e]

theorem bufPtr_back {j c : Nat} (hc : c + 40 = 18446744073709551616) (h : 40 ≤ j) :
    bufPtr ts block o (j + c) = bufPtr ts block o (j - 40) := by
  have e : o + (j + c) = o + (j - 40) + 2 ^ 64 := by omega
  have hb : BitVec.ofNat 64 (o + (j + c)) = BitVec.ofNat 64 (o + (j - 40)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [e, Nat.add_mod_right]
  simp only [bufPtr, hb]

/-- Leaving the loop: the code works out the pointer to the last block by going to the end of the
blocks and back one. -/
theorem while_end80_loopexit_run (B : Readable m ts block o n d) (T : Tables m ts)
    (hs : s0.toNat < 4294967296) {i i0 : Nat} {D L : BitVec 64} {C0 C1 C2 C3 C4 : BitVec 32}
    (hi0 : i0 + 40 * D.toNat = i + 40) (hD : 40 * D.toNat < 2 ^ 64) (hn : i + 40 + L.toNat = n)
    (ha : (m.addr (bufPtr ts block o i)).toNat % 8 = 0)
    (h : Lanes s0 d i (C0.setWidth 64) (C1.setWidth 64) (C2.setWidth 64) (C3.setWidth 64) (C4.setWidth 64)) :
    run St (.while_end80_loopexit m (some (bufPtr ts block o i0)) (some D) (some L) (some C0) (some C1)
        (some C2) (some C3) (some C4)) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have g := bufPtr_back (ts := ts) (block := block) (o := o) (j := i0 + 40 * D.toNat) (c := 18446744073709551576)
    rfl (by omega)
  rw [show i0 + 40 * D.toNat - 40 = i by omega] at g
  rw [run]
  simp only [Crc.crc32_z.step, mul40 hD, llvm_val, Readable.gep_plain, jump, andThen, Outcome.ok, g]
  exact while_end80_run B T hs hn ha h

theorem lanes_step32 {i : Nat} {C0 C1 C2 C3 C4 : BitVec 32}
    (h : Lanes s0 d i (C0.setWidth 64) (C1.setWidth 64) (C2.setWidth 64) (C3.setWidth 64) (C4.setWidth 64)) :
    Lanes s0 d (i + 40)
      (((steps 320 (word d i ^^^ C0.setWidth 64)).setWidth 32).setWidth 64)
      (((steps 320 (word d (i + 8) ^^^ C1.setWidth 64)).setWidth 32).setWidth 64)
      (((steps 320 (word d (i + 16) ^^^ C2.setWidth 64)).setWidth 32).setWidth 64)
      (((steps 320 (word d (i + 24) ^^^ C3.setWidth 64)).setWidth 32).setWidth 64)
      (((steps 320 (word d (i + 32) ^^^ C4.setWidth 64)).setWidth 32).setWidth 64) := by
  simp only [zext_steps320]
  exact lanes_step h

/-- The main loop, five words at a time: `r + 1` iterations left, then the last block. -/
theorem while_body15_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {D L : BitVec 64} (hD : 40 * D.toNat < 2 ^ 64) (hn : i0 + 40 * D.toNat + L.toNat = n)
    (r : Nat) :
    ∀ (i : Nat) (dec : BitVec 64) (C0 C1 C2 C3 C4 : BitVec 32), dec.toNat = r + 1 →
      i + 40 * (r + 1) + 40 = i0 + 40 * D.toNat → (m.addr (bufPtr ts block o i)).toNat % 8 = 0 →
      Lanes s0 d i (C0.setWidth 64) (C1.setWidth 64) (C2.setWidth 64) (C3.setWidth 64) (C4.setWidth 64) →
      run St (.while_body15 m (some dec) (some (bufPtr ts block o i)) (some C4) (some C0) (some C3)
          (some C1) (some C2) (some (bufPtr ts block o i0)) (some D) (some L)) =
        Outcome.ok (some (finish (spec s0 d n)), m) := by
  induction r with
  | zero =>
    intro i dec C0 C1 C2 C3 C4 hdec hi ha h
    have a1 := aligned_add (k := 8) ha rfl (by decide)
    have a2 := aligned_add (k := 16) ha rfl (by decide)
    have a3 := aligned_add (k := 24) ha rfl (by decide)
    have a4 := aligned_add (k := 32) ha rfl (by decide)
    have a5 := aligned_add (k := 40) ha rfl (by decide)
    have hd : (dec + 18446744073709551615#64).toNat = dec.toNat - 1 :=
      toNat_dec 1 rfl (by omega) (by omega)
    have h' := lanes_step32 h
    exec B, T
    split
    · exact while_end80_loopexit_run B T hs (by omega) hD (by omega) a5 h'
    · omega
  | succ r ih =>
    intro i dec C0 C1 C2 C3 C4 hdec hi ha h
    have a1 := aligned_add (k := 8) ha rfl (by decide)
    have a2 := aligned_add (k := 16) ha rfl (by decide)
    have a3 := aligned_add (k := 24) ha rfl (by decide)
    have a4 := aligned_add (k := 32) ha rfl (by decide)
    have a5 := aligned_add (k := 40) ha rfl (by decide)
    have hd : (dec + 18446744073709551615#64).toNat = dec.toNat - 1 :=
      toNat_dec 1 rfl (by omega) (by omega)
    have h' := lanes_step32 h
    exec B, T
    split
    · omega
    · exact ih (i + 40) _ _ _ _ _ _ (by omega) (by omega) a5 h'

theorem toNat_div40 (L : BitVec 64) : (L / 40#64).toNat = L.toNat / 40 := by
  simp [BitVec.toNat_udiv]

/-- What's left over after whole blocks of 40. -/
theorem toNat_left {L : BitVec 64} :
    ((L / 40#64) * 18446744073709551576#64 + L).toNat = L.toNat % 40 := by
  have hK : 18446744073709551576#64 = -(40#64) := by decide
  have e : (L / 40#64) * 18446744073709551576#64 + L = L - (L / 40#64) * 40#64 := by
    rw [hK, BitVec.mul_neg, BitVec.sub_eq_add_neg, BitVec.add_comm]
  have hD := toNat_div40 L
  have hmul : ((L / 40#64) * 40#64).toNat = 40 * (L.toNat / 40) := by
    simp only [BitVec.toNat_mul, hD, BitVec.toNat_ofNat]
    omega
  have hle : (L / 40#64) * 40#64 ≤ L := by
    rw [BitVec.le_def, hmul]; omega
  rw [e, BitVec.toNat_sub_of_le hle, hmul]
  omega

/-- Past the alignment loop, the braid proper. -/
theorem while_end_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i : Nat} {L : BitVec 64} (hL : 40 ≤ L.toNat) (hi : i + L.toNat = n)
    (ha : (m.addr (bufPtr ts block o i)).toNat % 8 = 0) :
    run St (.while_end m (some L) (some (bufPtr ts block o i)) (some (spec s0 d i))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hD := toNat_div40 L
  have hleft := toNat_left (L := L)
  have hX := spec_lt hs d i
  have hLt := L.isLt
  have hb : (L / 40#64).toNat < 4611686018427387904 := by omega
  have hdec : (L / 40#64 + 18446744073709551615#64).toNat = (L / 40#64).toNat - 1 :=
    toNat_dec 1 rfl (by omega) (by omega)
  exec B, T
  split
  · exact while_end80_run B T hs (by omega) ha (lanes_start s0 d i)
  · have hl : Lanes s0 d i (((spec s0 d i).setWidth 32).setWidth 64) ((0#32).setWidth 64)
        ((0#32).setWidth 64) ((0#32).setWidth 64) ((0#32).setWidth 64) := by
      have e : ((spec s0 d i).setWidth 32).setWidth 64 = spec s0 d i := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth]
        omega
      rw [e]
      exact lanes_start s0 d i
    exec B, T
    exact while_body15_run B T hs (D := L / 40#64) (by omega) (by omega) ((L / 40#64).toNat - 2) i _ _ _ _ _ _
      (by omega) (by omega) ha hl

/-- The byte loop that gets the pointer to a multiple of eight, unrolled into eight blocks. The eighth
can't be reached: one of the eight addresses before it is a multiple of eight. -/
theorem while_body_7_run {i0 : Nat} {R : Outcome (Val 64 × Mem)} {L : Val 64} {p : PtrVal} {x : Val 64}
    (hA : (m.addr (bufPtr ts block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr ts block o i0)).toNat % 8 + 7 < 8) :
    run St (.while_body_7 m (some (bufPtr ts block o i0)) L p x) = R := by
  omega

theorem while_body_6_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr ts block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr ts block o i0)).toNat % 8 + 6 < 8) :
    run St (.while_body_6 m (some (bufPtr ts block o i0)) (some L) (some (bufPtr ts block o (i0 + 6))) (some (spec s0 d (i0 + 6)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551609#64).toNat = L.toNat - 7 := toNat_dec 7 rfl (by omega) (by omega)
  have haddr := addr_bufPtr (ts := ts) m block o i0 7
  have hm := addr_mod8 (m.addr (bufPtr ts block o i0)) (k := 7) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_7_run hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_5_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr ts block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr ts block o i0)).toNat % 8 + 5 < 8) :
    run St (.while_body_5 m (some (bufPtr ts block o i0)) (some L) (some (bufPtr ts block o (i0 + 5))) (some (spec s0 d (i0 + 5)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551610#64).toNat = L.toNat - 6 := toNat_dec 6 rfl (by omega) (by omega)
  have haddr := addr_bufPtr (ts := ts) m block o i0 6
  have hm := addr_mod8 (m.addr (bufPtr ts block o i0)) (k := 6) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_6_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_4_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr ts block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr ts block o i0)).toNat % 8 + 4 < 8) :
    run St (.while_body_4 m (some (bufPtr ts block o i0)) (some L) (some (bufPtr ts block o (i0 + 4))) (some (spec s0 d (i0 + 4)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551611#64).toNat = L.toNat - 5 := toNat_dec 5 rfl (by omega) (by omega)
  have haddr := addr_bufPtr (ts := ts) m block o i0 5
  have hm := addr_mod8 (m.addr (bufPtr ts block o i0)) (k := 5) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_5_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_3_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr ts block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr ts block o i0)).toNat % 8 + 3 < 8) :
    run St (.while_body_3 m (some (bufPtr ts block o i0)) (some L) (some (bufPtr ts block o (i0 + 3))) (some (spec s0 d (i0 + 3)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551612#64).toNat = L.toNat - 4 := toNat_dec 4 rfl (by omega) (by omega)
  have haddr := addr_bufPtr (ts := ts) m block o i0 4
  have hm := addr_mod8 (m.addr (bufPtr ts block o i0)) (k := 4) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_4_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_2_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr ts block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr ts block o i0)).toNat % 8 + 2 < 8) :
    run St (.while_body_2 m (some (bufPtr ts block o i0)) (some L) (some (bufPtr ts block o (i0 + 2))) (some (spec s0 d (i0 + 2)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551613#64).toNat = L.toNat - 3 := toNat_dec 3 rfl (by omega) (by omega)
  have haddr := addr_bufPtr (ts := ts) m block o i0 3
  have hm := addr_mod8 (m.addr (bufPtr ts block o i0)) (k := 3) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_3_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_1_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr ts block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr ts block o i0)).toNat % 8 + 1 < 8) :
    run St (.while_body_1 m (some (bufPtr ts block o i0)) (some L) (some (bufPtr ts block o (i0 + 1))) (some (spec s0 d (i0 + 1)))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551614#64).toNat = L.toNat - 2 := toNat_dec 2 rfl (by omega) (by omega)
  have haddr := addr_bufPtr (ts := ts) m block o i0 2
  have hm := addr_mod8 (m.addr (bufPtr ts block o i0)) (k := 2) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_2_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_body_run (B : Readable m ts block o n d) (T : Tables m ts) (hs : s0.toNat < 4294967296)
    {i0 : Nat} {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : i0 + L.toNat = n)
    (hA : (m.addr (bufPtr ts block o i0)).toNat % 8 ≠ 0) (hj : (m.addr (bufPtr ts block o i0)).toNat % 8 + 0 < 8) :
    run St (.while_body m (some (bufPtr ts block o i0)) (some L) (some (spec s0 d i0))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hdec : (L + 18446744073709551615#64).toNat = L.toNat - 1 := toNat_dec 1 rfl (by omega) (by omega)
  have haddr := addr_bufPtr (ts := ts) m block o i0 1
  have hm := addr_mod8 (m.addr (bufPtr ts block o i0)) (k := 1) (by omega)
  rw [← haddr] at hm
  exec B, T
  split
  · exact while_body_1_run B T hs hL hi hA (by omega)
  · exact while_end_run B T hs (by omega) (by omega) (by omega)

theorem while_cond_preheader_run (B : Readable m ts block o n d) (T : Tables m ts)
    (hs : s0.toNat < 4294967296) {L : BitVec 64} (hL : 47 ≤ L.toNat) (hi : L.toNat = n) :
    run St (.while_cond_preheader m (some (bufPtr ts block o 0)) (some L) (some (spec s0 d 0))) =
      Outcome.ok (some (finish (spec s0 d n)), m) := by
  have hi' : 0 + L.toNat = n := by omega
  exec B, T
  split
  · exact while_end_run B T hs (by omega) hi' (by omega)
  · exact while_body_run B T hs hL hi' (by omega) (by omega)

/-- The function's body, in whatever call it's running in. -/
theorem crc32_z_run {crc len : BitVec 64} (B : Readable m ts block o len.toNat d) (T : Tables m ts)
    (hnn : m.addr (bufPtr ts block o 0) ≠ 0#64) :
    run St (.entry m (some crc) (some (bufPtr ts block o 0)) (some len)) =
      Outcome.ok (some (finish (spec (start crc) d len.toNat)), m) := by
  have hnn' : (m.addr (bufPtr ts block o 0)).toNat ≠ 0 := fun e => hnn (BitVec.eq_of_toNat_eq e)
  have hnull : m.addr Ptr.null = 0#64 := rfl
  have hs : (start crc).toNat < 4294967296 := by
    have h : start crc < 4294967296#64 := by simp only [start]; bv_decide
    simpa [BitVec.lt_def] using h
  have h0 : (crc &&& 4294967295#64) ^^^ 4294967295#64 = spec (start crc) d 0 := rfl
  rw [run]
  simp only [Crc.crc32_z.step, Readable.observeNull B, Mem.toVal, hnull, llvm_val, beq_toNat, decide_eq_true_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, jump, andThen, Outcome.ok]
  split
  · omega
  · rw [run]
    simp only [Crc.crc32_z.step, llvm_val, ult_toNat, decide_eq_true_eq, h0,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, jump, andThen, Outcome.ok]
    split
    · exact while_cond_preheader_run B T hs (by omega) rfl
    · exact if_end216_run B T hs (Nat.zero_add _)

/-- What `crc32_z`'s `memory(...)` says. -/
abbrev crcEffects : Effects := { other := .read, arg := .read, inaccessible := .none, errno := .read }

/-- Reading `len` bytes of a buffer, `crc32_z` returns the CRC of RFC 1952 and leaves memory as it
found it, apart from counting the call. Being `ok` also says it never hits undefined behavior or poison on
the way, including by breaking what its attributes promise. -/
theorem crc32_z_correct {crc len : BitVec 64} (B : Readable m ts block o len.toNat d) (T : Tables m ts)
    (hnn : m.addr (bufPtr ts block o 0) ≠ 0#64) :
    crc32_z (some crc) (some (bufPtr ts block o 0)) (some len) m =
      Outcome.ok (some (finish (spec (start crc) d len.toNat)), m.afterCall) := by
  have B' := B.enter (e := crcEffects) (T := { call := m.nextCall }) (Or.inl rfl) rfl rfl rfl rfl (Or.inl rfl)
  have T' : Tables (m.inCall crcEffects) ({ call := m.nextCall } :: ts) :=
    ⟨T.crc, T.braid, T.crcAlign, T.braidAlign, T.crcFits, T.braidFits, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact T.addressFree x hx⟩
  have hnn' : (m.inCall crcEffects).addr (bufPtr ({ call := m.nextCall } :: ts) block o 0) ≠ 0#64 := hnn
  have h := crc32_z_run (crc := crc) B' T' hnn'
  simp only [crc32_z, noundef_some, Mem.call, Mem.tag, Option.map]
  rw [show run Crc.crc32_z.step _ = _ from h]
  rfl

/-- zlib's documented way to get the initial value: a null buffer gives 0. -/
theorem crc32_z_null (crc len : BitVec 64) :
    crc32_z (some crc) (some Ptr.null) (some len) m = Outcome.ok (some 0#64, m.afterCall) := by
  simp only [crc32_z, noundef_some, Mem.call, Mem.tag, Option.map]
  rw [run]
  simp only [Crc.crc32_z.step, Mem.observeAddress, List.any_cons, List.any_nil, Bool.false_and, Bool.or_false,
    Bool.false_eq_true, ite_false, Mem.toVal, llvm_val, jump, andThen, Outcome.ok, Ptr.null, Mem.addr,
    beq_self_eq_true, ite_true]
  rw [run]
  simp [Crc.crc32_z.step, ret, Outcome.ok, Val.range, BitVec.ult]

/-- The spec gives the published check value of CRC-32, for "123456789". -/
example : finish (spec (start 0#64) (fun i => BitVec.ofNat 8
    ([49, 50, 51, 52, 53, 54, 55, 56, 57].getD i 0)) 9) = 0xCBF43926#64 := by decide +kernel

/-- The theorem on a real buffer, which shows its hypotheses can all hold at once. -/
theorem crc32_z_check_value :
    let init : Array Nat := #[49, 50, 51, 52, 53, 54, 55, 56, 57]
    let m := Crc.initial.addGlobal 100 init.size false init
    crc32_z (some 0#64) (some (bufPtr [] 100 0 0)) (some 9#64) m =
      Outcome.ok (some 0xCBF43926#64, m.afterCall) := by
  intro init m
  have B := Readable.ofGlobal Crc.initial 100 init rfl (by decide) (by decide) (by decide)
  have T : Tables m [] := ⟨rfl, rfl, by decide, by decide, by decide, by decide, by simp⟩
  have hnn : m.addr (bufPtr [] 100 0 0) ≠ 0#64 := by decide
  rw [crc32_z_correct (len := 9#64) B T hnn]
  congr 3
  decide +kernel

end CrcProof
