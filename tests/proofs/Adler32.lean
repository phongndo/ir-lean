import Zlib

/-! zlib's `adler32_z`, as clang compiles it at `-O2`, proved safe and correct against RFC 1950.
`tests/proofs.sh` regenerates `Zlib` from zlib's own source. -/

open IRLean Zlib

namespace Adler

/-- RFC 1950's definition of the checksum after `i` bytes of `d`. -/
def spec (a0 b0 : Nat) (d : Nat → BitVec 8) : Nat → Nat × Nat
  | 0 => (a0, b0)
  | i + 1 =>
    let s := spec a0 b0 d i
    let a := (s.1 + (d i).toNat) % 65521
    (a, (s.2 + a) % 65521)

/-- How the two sums combine into the 32-bit checksum. -/
def result (s : Nat × Nat) : BitVec 64 :=
  (BitVec.ofNat 64 s.2 <<< 16#64) ||| BitVec.ofNat 64 s.1

/-- The loop invariant: after `i` bytes, `x` and `y` agree with the spec modulo 65521, and are small
because only `k` bytes have gone in since they were last reduced. -/
structure Inv (a0 b0 : Nat) (d : Nat → BitVec 8) (i : Nat) (x y : BitVec 64) (k : Nat) : Prop where
  ax : x.toNat % 65521 = (spec a0 b0 d i).1
  ay : y.toNat % 65521 = (spec a0 b0 d i).2
  bx : x.toNat ≤ 65520 + 255 * k
  byy : y.toNat ≤ 65520 + k * 1481280
  hk : k ≤ 5552

variable {a0 b0 : Nat} {d : Nat → BitVec 8} {i k : Nat} {x y : BitVec 64}

/-- Adding a byte and then the new low sum. The two forms are the orders the unrolled loops use. -/
theorem Inv.stepL (h : Inv a0 b0 d i x y k) (hk : k < 5552) :
    Inv a0 b0 d (i + 1) (x + (d i).setWidth 64) (x + (d i).setWidth 64 + y) (k + 1) := by
  have ⟨ax, ay, bx, byy, _⟩ := h
  have hz : ((d i).setWidth 64).toNat = (d i).toNat := by simp [BitVec.toNat_setWidth]; omega
  have hd := (d i).isLt
  have hx : (x + (d i).setWidth 64).toNat = x.toNat + (d i).toNat := by
    rw [BitVec.toNat_add, hz]; omega
  have hy : (x + (d i).setWidth 64 + y).toNat = x.toNat + (d i).toNat + y.toNat := by
    rw [BitVec.toNat_add, hx]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hx]; simp only [spec]; omega
  · rw [hy]; simp only [spec]; omega
  · omega
  · omega
  · omega

theorem Inv.stepR (h : Inv a0 b0 d i x y k) (hk : k < 5552) :
    Inv a0 b0 d (i + 1) (x + (d i).setWidth 64) (y + (x + (d i).setWidth 64)) (k + 1) := by
  have := Inv.stepL h hk
  rwa [BitVec.add_comm (x + (d i).setWidth 64) y] at this

/-- Reducing both sums starts the count over. -/
theorem Inv.reduce (h : Inv a0 b0 d i x y k) :
    Inv a0 b0 d i (x % 65521#64) (y % 65521#64) 0 := by
  have ⟨ax, ay, _, _, _⟩ := h
  have hx : (x % 65521#64).toNat = x.toNat % 65521 := by simp [BitVec.toNat_umod]
  have hy : (y % 65521#64).toNat = y.toNat % 65521 := by simp [BitVec.toNat_umod]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rw [hx] | rw [hy] | skip
  · omega
  · omega
  · omega
  · omega
  · omega

local notation "St" => Zlib.adler32_z.step

theorem urem_P (x : BitVec 64) :
    Val.urem (some x) (some 65521#64) = Outcome.ok (some (x % 65521#64)) := by
  simp [Val.urem]

variable {m : Mem} {ts : List Tag} {block o n : Nat}

/-- `len - 16`, whose `nsw` the compiler added: it holds because `len` is small. -/
theorem sub16 {L : BitVec 64} (h : L.toNat ≤ 5551) :
    Val.add (some L) (some 18446744073709551600#64) (nsw := true) =
      some (L + 18446744073709551600#64) := by
  have hL : L ≤ 5551#64 := by simpa [BitVec.le_def] using h
  have : L.saddOverflow 18446744073709551600#64 = false := by bv_decide
  simp [Val.add, this]

/-- The inner counter's decrement, also `nsw`. -/
theorem dec32 {N : BitVec 32} (h : N.toNat ≤ 347) :
    Val.add (some N) (some 4294967295#32) (nsw := true) = some (N + 4294967295#32) := by
  have hN : N ≤ 347#32 := by simpa [BitVec.le_def] using h
  have : N.saddOverflow 4294967295#32 = false := by bv_decide
  simp [Val.add, this]

/-- `samesign` holds because both operands are small. -/
theorem ugt15 {L : BitVec 64} (h : L.toNat ≤ 5551) :
    Val.icmpUgt (some L) (some 15#64) (samesign := true) =
      some (BitVec.ofBool (BitVec.ult 15#64 L)) := by
  have hL : L ≤ 5551#64 := by simpa [BitVec.le_def] using h
  have : L.msb = false := by bv_decide
  have m15 : (15#64).msb = false := rfl
  simp [Val.icmpUgt, Val.icmp, this, m15]

/-- Runs one block: evaluates it on known values, leaving each branch condition as a fact about
natural numbers. -/
syntax "exec " term : tactic
macro_rules
  | `(tactic| exec $b) =>
    `(tactic| (rw [run]; simp (disch := omega) only [Zlib.adler32_z.step, llvm_val, urem_P,
        sub16, dec32, ugt15,
        Readable.load $b:term, Readable.gep $b:term, Readable.gep_plain,
        jump, ret, andThen, Outcome.ok, beq_toNat, ult_toNat, decide_eq_true_eq,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]))

theorem cleanup_run (v : BitVec 64) :
    run St (.cleanup m (some v)) = Outcome.ok (some v, m) := by
  rw [run]; simp [Zlib.adler32_z.step, ret, Outcome.ok]

theorem shl16 {y : BitVec 64} (hy : y.toNat < 65521) :
    Val.shl (some y) (some 16#64) (nuw := true) (nsw := true) = some (y <<< 16#64) := by
  have hy' : y < 65521#64 := by simpa [BitVec.lt_def] using hy
  have h1 : y <<< 16 >>> 16 = y := by bv_decide
  have h2 : (y <<< 16).sshiftRight 16 = y := by bv_decide
  simp [Val.shl, Val.shiftOk, h1, h2]

theorem if_end188_run {x y : BitVec 64} (hx : x.toNat < 65521) (hy : y.toNat < 65521) :
    run St (.if_end188 m (some x) (some y)) = Outcome.ok (some ((y <<< 16#64) ||| x), m) := by
  have hx' : x < 65521#64 := by simpa [BitVec.lt_def] using hx
  have hy' : y < 65521#64 := by simpa [BitVec.lt_def] using hy
  have h3 : y <<< 16 &&& x = 0#64 := by bv_decide
  rw [run]
  simp [Zlib.adler32_z.step, jump, Outcome.ok, shl16 hy, Val.or, h3]
  exact cleanup_run _

/-- Any small enough, already reduced pair of sums gives the spec's result. -/
theorem result_of (hx : x.toNat % 65521 = (spec a0 b0 d i).1) (hy : y.toNat % 65521 = (spec a0 b0 d i).2)
    (hx' : x.toNat < 65521) (hy' : y.toNat < 65521) :
    (y <<< 16#64) ||| x = result (spec a0 b0 d i) := by
  have e1 : BitVec.ofNat 64 (spec a0 b0 d i).1 = x := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  have e2 : BitVec.ofNat 64 (spec a0 b0 d i).2 = y := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  simp [result, e1, e2]

theorem while_end185_run (h : Inv a0 b0 d i x y k) :
    run St (.while_end185 m (some x) (some y)) =
      Outcome.ok (some (result (spec a0 b0 d i)), m) := by
  have hr := h.reduce
  have hx : (x % 65521#64).toNat < 65521 := by simp [BitVec.toNat_umod]; omega
  have hy : (y % 65521#64).toNat < 65521 := by simp [BitVec.toNat_umod]; omega
  rw [run]
  simp only [Zlib.adler32_z.step, urem_P, andThen, jump, Outcome.ok]
  rw [if_end188_run hx hy, result_of hr.ax hr.ay hx hy]
  rfl

section TailLoops

theorem toNat_and3 (L : BitVec 64) : (L &&& 3#64).toNat = L.toNat % 4 := by
  have := Nat.and_two_pow_sub_one_eq_mod L.toNat 2
  simp [BitVec.toNat_and]
  simpa using this

theorem toNat_inc {j : BitVec 64} (hj : j.toNat < 4) : (j + 1#64).toNat = j.toNat + 1 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

variable {n : Nat}

/-- The four-byte loop, once what's left is a multiple of four. -/
theorem while_body180_run (B : Readable m ts block o n d) (r : Nat) :
    ∀ (i k : Nat) (x y len : BitVec 64), len.toNat ≤ 4 * r → 0 < len.toNat → len.toNat % 4 = 0 →
      i + len.toNat = n → k + len.toNat ≤ 5552 → Inv a0 b0 d i x y k →
      run St (.while_body180 m (some y) (some len) (some (bufPtr ts block o i)) (some x)) =
        Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  induction r with
  | zero => intro i k x y len hr h0; omega
  | succ r ih =>
    intro i k x y len hr h0 h4 hi hk h
    have h4' := h.stepL (by omega) |>.stepL (by omega) |>.stepL (by omega) |>.stepL (by omega)
    have hdec : (len + 18446744073709551612#64).toNat = len.toNat - 4 :=
      toNat_dec 4 rfl (by omega) (by omega)
    exec B
    split
    · have e : i + 4 = n := by omega
      subst e
      exact while_end185_run h4'
    · exact ih (i + 4) (k + 4) _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) h4'

/-- Where the odd bytes' loop leaves: the four-byte loop, or nothing left. -/
theorem prol_exit_run (B : Readable m ts block o n d) (h : Inv a0 b0 d i x y k) {len L : BitVec 64}
    (hlen : len.toNat = L.toNat - L.toNat % 4) (hi : i + len.toNat = n)
    (hk : k + len.toNat ≤ 5552) :
    run St (.while_body180_prol_loopexit m (some x) (some y) (some y) (some len)
        (some (bufPtr ts block o i)) (some x) (some L)) =
      Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  exec B
  split
  · have e : i = n := by omega
    subst e
    exact while_end185_run h
  · exact while_body180_run B (len.toNat / 4) i k x y len (by omega) (by omega) (by omega) hi hk h

/-- The odd bytes' loop, with `j` of `t` iterations done. -/
theorem while_body180_prol_run (B : Readable m ts block o n d) {L t : BitVec 64}
    (ht : t.toNat = L.toNat % 4) (r : Nat) :
    ∀ (i k : Nat) (x y len j : BitVec 64), j.toNat + r + 1 = t.toNat →
      len.toNat = L.toNat - j.toNat → i + len.toNat = n → k + len.toNat ≤ 5552 →
      Inv a0 b0 d i x y k →
      run St (.while_body180_prol m (some y) (some len) (some (bufPtr ts block o i)) (some x) (some j)
          (some L) (some t)) =
        Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  induction r with
  | zero =>
    intro i k x y len j hj hlen hi hk h
    have h1 := h.stepL (by omega)
    have hdec : (len + 18446744073709551615#64).toNat = len.toNat - 1 :=
      toNat_dec 1 rfl (by omega) (by omega)
    have hinc := toNat_inc (j := j) (by omega)
    exec B
    split
    · exact prol_exit_run B h1 (by omega) (by omega) (by omega)
    · omega
  | succ r ih =>
    intro i k x y len j hj hlen hi hk h
    have h1 := h.stepL (by omega)
    have hdec : (len + 18446744073709551615#64).toNat = len.toNat - 1 :=
      toNat_dec 1 rfl (by omega) (by omega)
    have hinc := toNat_inc (j := j) (by omega)
    exec B
    split
    · omega
    · exact ih (i + 1) (k + 1) _ _ _ _ (by omega) (by omega) (by omega) (by omega) h1

/-- The tail of the function: anything left, one to four bytes at a time. -/
theorem while_body180_preheader_run (B : Readable m ts block o n d) (h : Inv a0 b0 d i x y k)
    {len : BitVec 64} (h0 : 0 < len.toNat) (hi : i + len.toNat = n) (hk : k + len.toNat ≤ 5552) :
    run St (.while_body180_preheader m (some y) (some len) (some (bufPtr ts block o i)) (some x)) =
      Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  have hand := toNat_and3 len
  have hz : (0#64).toNat = 0 := rfl
  exec B
  split
  · rw [run]
    simp only [Zlib.adler32_z.step, llvm_val, ult_toNat, decide_eq_true_eq, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod, jump, Outcome.ok]
    split
    · omega
    · exact while_body180_run B (len.toNat / 4) i k x y len (by omega) (by omega) (by omega) hi hk h
  · exact while_body180_prol_run B hand (len.toNat % 4 - 1) i k x y len 0#64
      (by omega) (by omega) hi hk h

/-- Past the sixteen-byte loop: stop, or go on with the tail. -/
theorem while_cond177_preheader_run (B : Readable m ts block o n d) (h : Inv a0 b0 d i x y k)
    {len : BitVec 64} (hi : i + len.toNat = n) (hk : k + len.toNat ≤ 5552) :
    run St (.while_cond177_preheader m (some len) (some x) (some y) (some (bufPtr ts block o i))) =
      Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  exec B
  split
  · have e : i = n := by omega
    subst e
    exact while_end185_run h
  · exact while_body180_preheader_run B h (by omega) hi hk

/-- The sixteen rounds an unrolled loop does: `add`, then the new low sum on the right. -/
syntax "sixteen " term " as " ident : tactic
macro_rules
  | `(tactic| sixteen $h as $out) =>
    `(tactic| have $out := (Inv.stepL $h (by omega) |>.stepR (by omega) |>.stepR (by omega)
        |>.stepR (by omega) |>.stepR (by omega) |>.stepR (by omega) |>.stepR (by omega)
        |>.stepR (by omega) |>.stepR (by omega) |>.stepR (by omega) |>.stepR (by omega)
        |>.stepR (by omega) |>.stepR (by omega) |>.stepR (by omega) |>.stepR (by omega)
        |>.stepR (by omega)))

/-- The sixteen-byte loop for what's left after the 5552-byte blocks. -/
theorem while_body109_run (B : Readable m ts block o n d) (r : Nat) :
    ∀ (i k : Nat) (x y len : BitVec 64), 16 ≤ len.toNat → len.toNat ≤ 5551 → len.toNat < 16 * (r + 1) →
      i + len.toNat = n → k + len.toNat ≤ 5552 → Inv a0 b0 d i x y k →
      run St (.while_body109 m (some y) (some len) (some (bufPtr ts block o i)) (some x)) =
        Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  induction r with
  | zero => intro i k x y len h16 _ hr; omega
  | succ r ih =>
    intro i k x y len h16 hs hr hi hk h
    sixteen h as h16'
    have hdec : (len + 18446744073709551600#64).toNat = len.toNat - 16 :=
      toNat_dec 16 rfl (by omega) (by omega)
    exec B
    split
    · exact ih (i + 16) (k + 16) _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) h16'
    · exact while_cond177_preheader_run B h16' (by omega) (by omega)

/-- After the 5552-byte blocks: stop, or finish what's left. -/
theorem while_end103_run (B : Readable m ts block o n d) (h : Inv a0 b0 d i x y 0) {len : BitVec 64}
    (hs : len.toNat ≤ 5551) (hi : i + len.toNat = n) :
    run St (.while_end103 m (some len) (some (bufPtr ts block o i)) (some x) (some y)) =
      Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  have hx := h.bx
  have hy := h.byy
  exec B
  split
  · have e : i = n := by omega
    subst e
    rw [if_end188_run (by omega) (by omega), result_of h.ax h.ay (by omega) (by omega)]
    rfl
  · exec B
    split
    · exec B
      exact while_body109_run B (len.toNat / 16) i 0 x y len (by omega) hs (by omega) hi (by omega) h
    · exact while_body180_preheader_run B h (by omega) hi (by omega)

/-- Like `toNat_dec`. Writing the literal directly gives omega a proof the kernel can't check. -/
theorem toNat_dec32 {N : BitVec 32} {c' : Nat} (h : c' = 4294967295) (hN : 1 ≤ N.toNat) :
    (N + BitVec.ofNat 32 c').toNat = N.toNat - 1 := by
  have := N.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The inner loop of a block: `c + 1` more groups of sixteen bytes, then `do_end`. -/
theorem do_body_run (B : Readable m ts block o n d) (len0 : Val 64) (buf0 : PtrVal)
    {R : Outcome (Val 64 × Mem)} (c : Nat) :
    ∀ (i k : Nat) (x y : BitVec 64) (N : BitVec 32), N.toNat = c + 1 → c + 1 ≤ 347 →
      i + 16 * (c + 1) ≤ n → k + 16 * (c + 1) ≤ 5552 → Inv a0 b0 d i x y k →
      (∀ x' y', Inv a0 b0 d (i + 16 * (c + 1)) x' y' (k + 16 * (c + 1)) →
        run St (.do_end m len0 buf0 (some x') (some y')) = R) →
      run St (.do_body m (some x) (some (bufPtr ts block o i)) (some y) (some N) len0 buf0) = R := by
  induction c with
  | zero =>
    intro i k x y N hN hc hi hk h next
    sixteen h as h16
    have hdec := toNat_dec32 (N := N) rfl (by omega)
    exec B
    split
    · exact next _ _ h16
    · omega
  | succ c ih =>
    intro i k x y N hN hc hi hk h next
    sixteen h as h16
    have hdec := toNat_dec32 (N := N) rfl (by omega)
    exec B
    split
    · omega
    · refine ih (i + 16) (k + 16) _ _ _ (by omega) (by omega) (by omega) (by omega) h16 ?_
      intro x' y' hf
      have e1 : i + 16 + 16 * (c + 1) = i + 16 * (c + 1 + 1) := by omega
      have e2 : k + 16 + 16 * (c + 1) = k + 16 * (c + 1 + 1) := by omega
      rw [e1, e2] at hf
      exact next x' y' hf

/-- The outer loop: while at least 5552 bytes remain, take a block of 5552 and reduce. -/
theorem while_body33_run (B : Readable m ts block o n d) (r : Nat) :
    ∀ (i : Nat) (x y len : BitVec 64), 5552 ≤ len.toNat → len.toNat < 5552 * (r + 1) →
      i + len.toNat = n → Inv a0 b0 d i x y 0 →
      run St (.while_body33 m (some y) (some len) (some (bufPtr ts block o i)) (some x)) =
        Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  induction r with
  | zero => intro i x y len hm hr; omega
  | succ r ih =>
    intro i x y len hm hr hi h
    have hdec : (len + 18446744073709546064#64).toNat = len.toNat - 5552 :=
      toNat_dec 5552 rfl (by omega) (by omega)
    rw [run]
    simp only [Zlib.adler32_z.step, jump, Outcome.ok]
    refine do_body_run B _ _ 346 i 0 x y 347#32 rfl (by omega) (by omega) (by omega) h ?_
    intro x' y' hf
    have hf' := hf.reduce
    exec B
    split
    · exact ih (i + 5552) _ _ _ (by omega) (by omega) (by omega) hf'
    · exact while_end103_run B hf' (by omega) (by omega)

/-! ### Short input, and the single byte -/

/-- One conditional subtraction reduces a sum below twice the modulus. -/
theorem reduce_once {v : BitVec 64} (h : v.toNat < 131042) :
    select (some (BitVec.ofBool (BitVec.ult 65520#64 v))) (some (v + 18446744073709486095#64)) (some v) =
      some (v % 65521#64) := by
  have hm : (v % 65521#64).toNat = v.toNat % 65521 := by simp [BitVec.toNat_umod]
  by_cases c : 65520 < v.toNat
  · have hd : (v + 18446744073709486095#64).toNat = v.toNat - 65521 :=
      toNat_dec 65521 rfl (by omega) (by omega)
    have e : v + 18446744073709486095#64 = v % 65521#64 := by
      apply BitVec.eq_of_toNat_eq; omega
    rw [select_ofBool, ult_toNat]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, decide_eq_true_eq, c, ↓reduceIte, e]
  · have e : v = v % 65521#64 := by
      apply BitVec.eq_of_toNat_eq; omega
    have c' : ¬ (65520 < v.toNat) := c
    rw [select_ofBool, ult_toNat]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, decide_eq_true_eq, c', ↓reduceIte]
    rw [← e]

theorem while_end_run (h : Inv a0 b0 d i x y k) (hk : k ≤ 256) :
    run St (.while_end m (some x) (some y)) =
      Outcome.ok (some (result (spec a0 b0 d i)), m) := by
  have hb := h.bx
  have hr := h.reduce
  have hxr : (x % 65521#64).toNat < 65521 := by have := hr.bx; omega
  have hyr : (y % 65521#64).toNat < 65521 := by have := hr.byy; omega
  rw [run]
  simp (disch := omega) only [Zlib.adler32_z.step, Val.icmpUgt_some, Val.add_some, urem_P, shl16,
    reduce_once, Val.or_some, andThen, jump, Outcome.ok]
  rw [cleanup_run, result_of hr.ax hr.ay hxr hyr]
  rfl

/-- The same four-byte loop for short input, which exits to `while_end`. -/
theorem while_body_run (B : Readable m ts block o n d) (r : Nat) :
    ∀ (i k : Nat) (x y len : BitVec 64), len.toNat ≤ 4 * r → 0 < len.toNat → len.toNat % 4 = 0 →
      i + len.toNat = n → k + len.toNat ≤ 15 → Inv a0 b0 d i x y k →
      run St (.while_body m (some y) (some len) (some (bufPtr ts block o i)) (some x)) =
        Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  induction r with
  | zero => intro i k x y len hr h0; omega
  | succ r ih =>
    intro i k x y len hr h0 h4 hi hk h
    have h4' := h.stepL (by omega) |>.stepL (by omega) |>.stepL (by omega) |>.stepL (by omega)
    have hdec : (len + 18446744073709551612#64).toNat = len.toNat - 4 :=
      toNat_dec 4 rfl (by omega) (by omega)
    exec B
    split
    · have e : i + 4 = n := by omega
      subst e
      exact while_end_run h4' (by omega)
    · exact ih (i + 4) (k + 4) _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) h4'


theorem short_exit_run (B : Readable m ts block o n d) (h : Inv a0 b0 d i x y k) {len L : BitVec 64}
    (hlen : len.toNat = L.toNat - L.toNat % 4) (hi : i + len.toNat = n)
    (hk : k + len.toNat ≤ 15) :
    run St (.while_body_prol_loopexit m (some x) (some y) (some y) (some len)
        (some (bufPtr ts block o i)) (some x) (some L)) =
      Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  exec B
  split
  · have e : i = n := by omega
    subst e
    exact while_end_run h (by omega)
  · exact while_body_run B (len.toNat / 4) i k x y len (by omega) (by omega) (by omega) hi hk h


theorem while_body_prol_run (B : Readable m ts block o n d) {L t : BitVec 64}
    (ht : t.toNat = L.toNat % 4) (r : Nat) :
    ∀ (i k : Nat) (x y len j : BitVec 64), j.toNat + r + 1 = t.toNat →
      len.toNat = L.toNat - j.toNat → i + len.toNat = n → k + len.toNat ≤ 15 →
      Inv a0 b0 d i x y k →
      run St (.while_body_prol m (some y) (some len) (some (bufPtr ts block o i)) (some x) (some j)
          (some L) (some t)) =
        Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  induction r with
  | zero =>
    intro i k x y len j hj hlen hi hk h
    have h1 := h.stepL (by omega)
    have hdec : (len + 18446744073709551615#64).toNat = len.toNat - 1 :=
      toNat_dec 1 rfl (by omega) (by omega)
    have hinc := toNat_inc (j := j) (by omega)
    exec B
    split
    · exact short_exit_run B h1 (by omega) (by omega) (by omega)
    · omega
  | succ r ih =>
    intro i k x y len j hj hlen hi hk h
    have h1 := h.stepL (by omega)
    have hdec : (len + 18446744073709551615#64).toNat = len.toNat - 1 :=
      toNat_dec 1 rfl (by omega) (by omega)
    have hinc := toNat_inc (j := j) (by omega)
    exec B
    split
    · omega
    · exact ih (i + 1) (k + 1) _ _ _ _ (by omega) (by omega) (by omega) (by omega) h1

/-- Short input: fewer than sixteen bytes, at least one. -/
theorem while_body_preheader_run (B : Readable m ts block o n d) (h : Inv a0 b0 d i x y k)
    {len : BitVec 64} (h0 : 0 < len.toNat) (hi : i + len.toNat = n) (hk : k + len.toNat ≤ 15) :
    run St (.while_body_preheader m (some (bufPtr ts block o i)) (some len) (some y) (some x)) =
      Outcome.ok (some (result (spec a0 b0 d n)), m) := by
  have hand := toNat_and3 len
  have hz : (0#64).toNat = 0 := rfl
  exec B
  split
  · exec B
    split
    · omega
    · exact while_body_run B (len.toNat / 4) i k x y len (by omega) (by omega) (by omega) hi hk h
  · exact while_body_prol_run B hand (len.toNat % 4 - 1) i k x y len 0#64
      (by omega) (by omega) hi hk h

theorem small_add {u v : BitVec 64} (hu : u.toNat < 4294967296) (hv : v.toNat < 4294967296) :
    Val.add (some u) (some v) (nuw := true) (nsw := true) = some (u + v) := by
  have hu' : u < 4294967296#64 := by simpa [BitVec.lt_def] using hu
  have hv' : v < 4294967296#64 := by simpa [BitVec.lt_def] using hv
  have h1 : u.uaddOverflow v = false := by bv_decide
  have h2 : u.saddOverflow v = false := by bv_decide
  simp [Val.add, h1, h2]

theorem small_ugt {v : BitVec 64} (hv : v.toNat < 4294967296) :
    Val.icmpUgt (some v) (some 65520#64) (samesign := true) =
      some (BitVec.ofBool (BitVec.ult 65520#64 v)) := by
  have hv' : v < 4294967296#64 := by simpa [BitVec.lt_def] using hv
  have h1 : v.msb = false := by bv_decide
  have h2 : (65520#64).msb = false := rfl
  simp [Val.icmpUgt, Val.icmp, h1, h2]

theorem small_sub {v : BitVec 64} (hv : v.toNat < 4294967296) :
    Val.add (some v) (some 18446744073709486095#64) (nsw := true) =
      some (v + 18446744073709486095#64) := by
  have hv' : v < 4294967296#64 := by simpa [BitVec.lt_def] using hv
  have h1 : v.saddOverflow 18446744073709486095#64 = false := by bv_decide
  simp [Val.add, h1]

theorem small_shl {v : BitVec 64} (hv : v.toNat < 4294967296) :
    Val.shl (some v) (some 16#64) (nsw := true) = some (v <<< 16#64) := by
  have hv' : v < 4294967296#64 := by simpa [BitVec.lt_def] using hv
  have h1 : (v <<< 16).sshiftRight 16 = v := by bv_decide
  simp [Val.shl, Val.shiftOk, h1]

theorem small_shl_sub {v : BitVec 64} (hv : v.toNat < 4294967296) :
    Val.add (some (v <<< 16#64)) (some 18446744069415567360#64) (nsw := true) =
      some ((v <<< 16#64) + 18446744069415567360#64) := by
  have hv' : v < 4294967296#64 := by simpa [BitVec.lt_def] using hv
  have h1 : (v <<< 16).saddOverflow 18446744069415567360#64 = false := by bv_decide
  simp [Val.add, h1]

/-- The same reduction, done on the sum after shifting it into place. -/
theorem reduce_shl {v : BitVec 64} (h : v.toNat < 131042) :
    select (some (BitVec.ofBool (BitVec.ult 65520#64 v)))
        (some ((v <<< 16#64) + 18446744069415567360#64)) (some (v <<< 16#64)) =
      some ((v % 65521#64) <<< 16#64) := by
  have e : (v <<< 16#64) + 18446744069415567360#64 = (v + 18446744073709486095#64) <<< 16#64 := by
    bv_decide
  have r := reduce_once h
  by_cases c : BitVec.ult 65520#64 v = true
  · simp only [c, select_ofBool, ite_true, Option.some.injEq] at r ⊢
    rw [e, r]
  · simp only [c, select_ofBool, ite_false, Option.some.injEq, Bool.false_eq_true] at r ⊢
    rw [← r]

/-- zlib's fast path for exactly one byte. -/
theorem if_then_run (B : Readable m ts block o n d) (hn : 0 < n) {a b : BitVec 64}
    (ha : a.toNat < 65521) (hb : b.toNat < 65521) :
    run St (.if_then m (some (bufPtr ts block o 0)) (some b) (some a)) =
      Outcome.ok (some (result (spec a.toNat b.toNat d 1)), m) := by
  have hz : ((d 0).setWidth 64).toNat = (d 0).toNat := by simp [BitVec.toNat_setWidth]; omega
  have hd := (d 0).isLt
  have hA : (a + (d 0).setWidth 64).toNat = a.toNat + (d 0).toNat := by
    rw [BitVec.toNat_add, hz]; omega
  generalize hz' : a + (d 0).setWidth 64 = A at hA
  have hS : (A % 65521#64).toNat = A.toNat % 65521 := by simp [BitVec.toNat_umod]
  have hB : (A % 65521#64 + b).toNat = (A % 65521#64).toNat + b.toNat := by
    rw [BitVec.toNat_add]; omega
  generalize hS' : A % 65521#64 = S at hS hB
  have hY : ((S + b) % 65521#64).toNat = (S + b).toNat % 65521 := by simp [BitVec.toNat_umod]
  have hsz : ((d 0).setWidth 64).toNat < 4294967296 := by omega
  rw [run]
  simp (disch := omega) only [Zlib.adler32_z.step, Readable.load B, andThen, Outcome.ok, Val.zext_some,
    small_add, small_ugt, small_sub, small_shl, small_shl_sub, hz', reduce_once, hS', reduce_shl,
    Val.icmpUgt_some, Val.or_some, jump]
  rw [cleanup_run]
  refine congrArg (fun v => (Outcome.ok (some v, m) : Outcome (Val 64 × Mem))) ?_
  apply result_of
  · simp only [spec]; omega
  · simp only [spec]; omega
  · omega
  · omega

end TailLoops

/-- The function's body, in whatever call it's running in. -/
theorem adler32_z_run {adler len : BitVec 64} {m : Mem} {block o : Nat}
    (B : Readable m ts block o len.toNat d) (hnn : m.addr (bufPtr ts block o 0) ≠ 0#64)
    (ha : (adler &&& 65535#64).toNat = a0) (hb : ((adler >>> 16#64) &&& 65535#64).toNat = b0)
    (ha' : a0 < 65521) (hb' : b0 < 65521) :
    run St (.entry m (some adler) (some (bufPtr ts block o 0)) (some len)) =
      Outcome.ok (some (result (spec a0 b0 d len.toNat)), m) := by
  have hshr : Val.lshr (some adler) (some 16#64) = some (adler >>> 16#64) := by
    simp [Val.lshr, Val.shiftOk]
  have hnn' : (m.addr (bufPtr ts block o 0)).toNat ≠ 0 := fun e => hnn (BitVec.eq_of_toNat_eq e)
  have hnull : m.addr Ptr.null = 0#64 := rfl
  have h0 : Inv a0 b0 d 0 (adler &&& 65535#64) ((adler >>> 16#64) &&& 65535#64) 0 :=
    ⟨by simp only [spec]; omega, by simp only [spec]; omega, by omega, by omega, by omega⟩
  rw [run]
  simp only [Zlib.adler32_z.step, hshr, llvm_val, beq_toNat, decide_eq_true_eq, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod, jump, Outcome.ok]
  split
  · rename_i h1
    subst ha hb
    rw [h1]
    exact if_then_run B (by omega) ha' hb'
  · rw [run]
    simp only [Zlib.adler32_z.step, Readable.observeNull B, Mem.toVal, hnull, llvm_val, beq_toNat,
      decide_eq_true_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, jump, Outcome.ok]
    split
    · omega
    · exec B
      split
      · exec B
        split
        · rename_i h1
          rw [h1]
          exact while_end_run h0 (by omega)
        · exact while_body_preheader_run B h0 (by omega) (by omega) (by omega)
      · exec B
        split
        · exact while_body33_run B (len.toNat / 5552) 0 _ _ _ (by omega) (by omega) (by omega) h0
        · exec B
          exact while_body109_run B (len.toNat / 16) 0 0 _ _ _ (by omega) (by omega) (by omega)
            (by omega) (by omega) h0

/-- What `adler32_z`'s `memory(...)` says. -/
abbrev adlerEffects : Effects := { other := .none, arg := .read, inaccessible := .none, errno := .none }

/-- What `adler32_z`'s attributes promise about `buf`. -/
abbrev adlerTag (m : Mem) : Tag :=
  { call := m.nextCall, readonly := true, nofree := true, expires := true, noAddress := true, nullCheck := true }

/-- Reading `len` bytes of a buffer, `adler32_z` returns the RFC 1950 checksum and leaves memory as
it found it, apart from counting the call. Being `ok` also says it never hits undefined behavior or poison
on the way, including by breaking what its attributes promise. -/
theorem adler32_z_correct {adler len : BitVec 64} {m : Mem} {block o : Nat}
    (B : Readable m ts block o len.toNat d) (hnn : m.addr (bufPtr ts block o 0) ≠ 0#64)
    (ha : (adler &&& 65535#64).toNat = a0) (hb : ((adler >>> 16#64) &&& 65535#64).toNat = b0)
    (ha' : a0 < 65521) (hb' : b0 < 65521) :
    adler32_z (some adler) (some (bufPtr ts block o 0)) (some len) m =
      Outcome.ok (some (result (spec a0 b0 d len.toNat)), m.afterCall) := by
  have B' := B.enter (e := adlerEffects) (T := adlerTag m) (Or.inl rfl) rfl rfl rfl rfl (Or.inr rfl)
  have hnn' : (m.inCall adlerEffects).addr (bufPtr (adlerTag m :: ts) block o 0) ≠ 0#64 := hnn
  have h := adler32_z_run B' hnn' ha hb ha' hb'
  simp only [adler32_z, noundef_some, Mem.call, Mem.tag, Option.map]
  rw [show run Zlib.adler32_z.step _ = _ from h]
  rfl

/-- The spec gives the published checksum of "Wikipedia". -/
example : result (spec 1 0 (fun i => BitVec.ofNat 8
    ([87, 105, 107, 105, 112, 101, 100, 105, 97].getD i 0)) 9) = 0x11E60398#64 := by decide

/-- The theorem on a real buffer, which shows its hypotheses can all hold at once. -/
theorem adler32_z_check_value :
    let init : Array Nat := #[87, 105, 107, 105, 112, 101, 100, 105, 97]
    let m := Zlib.initial.addGlobal 100 init.size false init
    adler32_z (some 1#64) (some (bufPtr [] 100 0 0)) (some 9#64) m =
      Outcome.ok (some 0x11E60398#64, m.afterCall) := by
  intro init m
  have B := Readable.ofGlobal Zlib.initial 100 init rfl (by decide) (by decide) (by decide)
  have hnn : m.addr (bufPtr [] 100 0 0) ≠ 0#64 := by decide
  rw [adler32_z_correct (len := 9#64) (a0 := 1) (b0 := 0) B hnn (by decide) (by decide) (by decide)
    (by decide)]
  congr 3
  decide +kernel

end Adler

#print axioms Adler.adler32_z_correct
#print axioms Adler.adler32_z_check_value
