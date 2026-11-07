import Std.Tactic.BVDecide

/-! What compiler-rt's shift-and-subtract division keeps true, as arithmetic on natural numbers: `k` bits of the
dividend `n` are still in the top of `q`, the quotient so far is `2 * Q + c`, and the remainder so far is `r`. -/

namespace Llvm.Div

theorem toNat_and_one {w : Nat} (x : BitVec w) (hw : 1 < w) : (x &&& BitVec.ofNat w 1).toNat = x.toNat % 2 := by
  have h : (1 : Nat) % 2 ^ w = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, h]
  exact Nat.and_one_is_mod _

/-- The loop's invariant, with `k` bits of `n` left to bring down. -/
structure Inv (w n d k r q c Q : Nat) : Prop where
  hk : k ≤ w
  hr : r < d
  hq : q = (n % 2 ^ k) * 2 ^ (w - k) + Q
  hQ : Q < 2 ^ (w - k)
  hc : c ≤ 1
  heq : n / 2 ^ k = (2 * Q + c) * d + r

/-- One step of the loop, as arithmetic: bring a bit down and subtract if the remainder is big enough. -/
theorem Inv.step {w n d k r q c Q : Nat} (h : Inv w n d (k + 1) r q c Q) :
    let b := q / 2 ^ (w - 1)
    let r1 := 2 * r + b
    Inv w n d k (if d ≤ r1 then r1 - d else r1) (2 * q % 2 ^ w + c) (if d ≤ r1 then 1 else 0) (2 * Q + c) := by
  obtain ⟨hk, hr, hq, hQ, hc, heq⟩ := h
  intro b r1
  have hw : w = k + 1 + (w - (k + 1)) := by omega
  generalize hu : w - (k + 1) = u at *
  have e1 : w - k = u + 1 := by omega
  have e2 : w - 1 = k + u := by omega
  have pk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have pu : 2 ^ (u + 1) = 2 * 2 ^ u := by rw [Nat.pow_succ, Nat.mul_comm]
  have pw : 2 ^ w = 2 * (2 ^ k * 2 ^ u) := by
    rw [hw, Nat.add_right_comm, Nat.pow_succ, Nat.pow_add]
    exact Nat.mul_comm _ _
  have pw1 : 2 ^ (w - 1) = 2 ^ k * 2 ^ u := by rw [e2, Nat.pow_add]
  generalize hp : 2 ^ k = p at *
  generalize hv : 2 ^ u = v at *
  have hp0 : 0 < p := hp ▸ Nat.two_pow_pos k
  have hv0 : 0 < v := hv ▸ Nat.two_pow_pos u
  have hqk : q = (n % (2 * p)) * v + Q := by rw [hq, pk]
  -- Split off the bit that comes down.
  have hsplit : n % (2 * p) = n % p + p * (n / p % 2) := by rw [Nat.mul_comm 2 p, Nat.mod_mul]
  have hdiv : n / p = 2 * (n / (2 * p)) + n / p % 2 := by
    rw [Nat.mul_comm 2 p, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (n / p) 2
    omega
  have heq' : n / (2 * p) = (2 * Q + c) * d + r := by rw [← pk]; exact heq
  generalize hbit : n / p % 2 = bit at *
  have hbit1 : bit ≤ 1 := by omega
  have ha : n % p < p := Nat.mod_lt _ hp0
  generalize haeq : n % p = a at *
  -- `q` is the bit, on top of what's below it.
  have hT : a * v + Q < p * v := by
    have : (a + 1) * v ≤ p * v := Nat.mul_le_mul_right v (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have hqT : q = bit * (p * v) + (a * v + Q) := by
    rw [hqk, hsplit]
    grind
  have hb : b = bit := by
    show q / 2 ^ (w - 1) = bit
    rw [pw1, hqT, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.mul_pos hp0 hv0), Nat.div_eq_of_lt hT]
    omega
  have hq2 : 2 * q % 2 ^ w = a * (2 * v) + 2 * Q := by
    rw [pw, hqT]
    have e : 2 * (bit * (p * v) + (a * v + Q)) = 2 * (a * v + Q) + bit * (2 * (p * v)) := by grind
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    grind
  have hr1 : r1 = 2 * r + bit := by simp only [r1, hb]
  have hnew : n / p = 2 * ((2 * Q + c) * d) + r1 := by rw [hdiv, heq', hr1]; omega
  have hsum : (2 * (2 * Q + c) + 1) * d = 2 * ((2 * Q + c) * d) + d := by grind
  have hzero : (2 * (2 * Q + c) + 0) * d = 2 * ((2 * Q + c) * d) := by grind
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · split <;> omega
  · rw [hq2, e1, pu, hp, haeq]; grind
  · rw [e1, pu]; omega
  · split <;> omega
  · rw [hp]
    split
    · rw [hsum, hnew]; omega
    · rw [hzero, hnew]

/-- At the end, the quotient and remainder are what they should be. -/
theorem Inv.finish {w n d r q c Q : Nat} (h : Inv w n d 0 r q c Q) :
    n / d = 2 * Q + c ∧ n % d = r ∧ q = Q := by
  obtain ⟨_, hr, hq, _, _, heq⟩ := h
  simp only [Nat.pow_zero, Nat.div_one, Nat.mod_one, Nat.zero_mul, Nat.zero_add] at hq heq
  have hd : 0 < d := by omega
  subst heq
  refine ⟨?_, ?_, hq⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hr]; omega
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]


namespace W32

variable {n d r q c r' q' c' : BitVec 32} {k : Nat}

/-- The invariant for values, and what keeps the loop's comparison from overflowing: a divisor with its top bit set only
gets one step, on a remainder of the size the start of the loop gives it. -/
structure St (n d : BitVec 32) (k : Nat) (r q c : BitVec 32) : Prop where
  inv : ∃ Q, Inv 32 n.toNat d.toNat k r.toNat q.toNat c.toNat Q
  safe : 0 < k → d.msb = true → k = 1 ∧ 1073741824#32 ≤ r ∧ r < 2147483648#32

theorem toNat_and_one (x : BitVec 32) : (x &&& 1#32).toNat = x.toNat % 2 :=
  Div.toNat_and_one x (by omega)

theorem St.congr (h : St n d k r q c) (hr : r' = r) (hq : q' = q) (hc : c' = c) : St n d k r' q' c' := by
  subst hr hq hc; exact h

theorem St.carry_le (h : St n d k r q c) : c ≤ 1#32 := by
  obtain ⟨_, hi⟩ := h.inv
  simpa [BitVec.le_def] using hi.hc

theorem St.lt (h : St n d k r q c) : r < d := by
  obtain ⟨_, hi⟩ := h.inv
  simpa [BitVec.lt_def] using hi.hr

/-- One step of the loop on values. -/
theorem St.iter (h : St n d (k + 1) r q c) :
    let r1 := (r <<< 1#32) ||| (q >>> 31#32)
    let s := d + (r1 ^^^ 4294967295#32)
    St n d k (r1 - if s.slt 0#32 = true then d else 0#32) ((q <<< 1#32) ||| c) (s >>> 31#32) := by
  intro r1 s
  obtain ⟨Q, hi⟩ := h.inv
  have hlt := h.lt
  have hc := h.carry_le
  have hsafe := h.safe (by omega)
  have hsmall : d.msb = false ∨ (1073741824#32 ≤ r ∧ r < 2147483648#32) := by
    cases hm : d.msb
    · exact Or.inl rfl
    · exact Or.inr (hsafe hm).2
  have hs : (s.slt 0#32 = true) ↔ d ≤ r1 := by
    simp only [s, r1]
    rcases hsmall with hm | hm
    · have : d < 2147483648#32 := by bv_decide
      bv_decide
    · have := hm.1; have := hm.2; bv_decide
  have hcarry : s >>> 31#32 = if d ≤ r1 then 1#32 else 0#32 := by
    simp only [s, r1]
    rcases hsmall with hm | hm
    · have : d < 2147483648#32 := by bv_decide
      split <;> bv_decide
    · have := hm.1; have := hm.2; split <;> bv_decide
  have hr1 : r1 = (r + r) + (q >>> 31#32) := by simp only [r1]; bv_decide
  have hrsmall : r < 2147483648#32 := by
    rcases hsmall with hm | hm
    · bv_decide
    · exact hm.2
  have hrN : r.toNat < 2 ^ 31 := by simpa [BitVec.lt_def] using hrsmall
  have hbN : (q >>> 31#32).toNat = q.toNat / 2 ^ 31 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hbit : q.toNat / 2 ^ 31 ≤ 1 := by have := q.isLt; omega
  have hr1N : r1.toNat = 2 * r.toNat + q.toNat / 2 ^ 31 := by
    rw [hr1, BitVec.toNat_add, BitVec.toNat_add, hbN]
    omega
  have hqN : ((q <<< 1#32) ||| c).toNat = 2 * q.toNat % 2 ^ 32 + c.toNat := by
    have e : (q <<< 1#32) ||| c = (q + q) + c := by bv_decide
    have hcN : c.toNat ≤ 1 := by simpa [BitVec.le_def] using hc
    rw [e, BitVec.toNat_add, BitVec.toNat_add]
    have := q.isLt
    omega
  have hle : (d ≤ r1) ↔ d.toNat ≤ r1.toNat := by simp [BitVec.le_def]
  have stepped := hi.step
  simp only at stepped
  refine ⟨⟨2 * Q + c.toNat, ?_⟩, ?_⟩
  · have hrr : (r1 - if s.slt 0#32 = true then d else 0#32).toNat =
        if d.toNat ≤ 2 * r.toNat + q.toNat / 2 ^ (32 - 1) then 2 * r.toNat + q.toNat / 2 ^ (32 - 1) - d.toNat
        else 2 * r.toNat + q.toNat / 2 ^ (32 - 1) := by
      simp only [show 32 - 1 = 31 from rfl]
      by_cases hd : d ≤ r1
      · rw [ite_eq_left (hs.mpr hd), BitVec.toNat_sub_of_le hd, hr1N]
        have := hle.mp hd
        rw [hr1N] at this
        rw [ite_eq_left this]
      · rw [ite_eq_right (fun e => hd (hs.mp e))]
        have h' : ¬ d.toNat ≤ 2 * r.toNat + q.toNat / 2 ^ 31 := by rw [← hr1N]; exact fun e => hd (hle.mpr e)
        rw [ite_eq_right h']
        simpa using hr1N
    have hcc : (s >>> 31#32).toNat =
        if d.toNat ≤ 2 * r.toNat + q.toNat / 2 ^ (32 - 1) then 1 else 0 := by
      simp only [show 32 - 1 = 31 from rfl]
      rw [hcarry]
      by_cases hd : d ≤ r1
      · have := hle.mp hd
        rw [hr1N] at this
        simp [hd, this]
      · have h' : ¬ d.toNat ≤ 2 * r.toNat + q.toNat / 2 ^ 31 := by rw [← hr1N]; exact fun e => hd (hle.mpr e)
        simp [hd, h']
    rw [hrr, hqN, hcc]
    exact stepped
  · intro hk hm
    have := (hsafe hm).1
    omega

/-- What the loop leaves, once no bits are left to bring down. -/
theorem St.finish (h : St n d 0 r q c) : c ||| (q <<< 1#32) = n / d ∧ r = n % d := by
  obtain ⟨Q, hi⟩ := h.inv
  obtain ⟨hdiv, hmod, hq⟩ := hi.finish
  have hc := h.carry_le
  have hcN : c.toNat ≤ 1 := hi.hc
  have hdpos : 0 < d.toNat := by have := hi.hr; omega
  constructor
  · have e : c ||| (q <<< 1#32) = (q + q) + c := by bv_decide
    rw [e]
    apply BitVec.eq_of_toNat_eq
    have hlt : n.toNat / d.toNat < 2 ^ 32 := by
      have := n.isLt
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_udiv, hdiv] at *
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod, hmod]

/-- Where the loop starts: `n`'s top bits are the first remainder, and the rest wait at the top of `q`. -/
theorem St.start {s : Nat} (hs : s ≤ 32) (hrd : n >>> s < d)
    (hsafe : 0 < s → d.msb = true → s = 1 ∧ 1073741824#32 ≤ n >>> s ∧ n >>> s < 2147483648#32) :
    St n d s (n >>> s) (n <<< (32 - s)) 0#32 := by
  refine ⟨⟨0, hs, by simpa [BitVec.lt_def] using hrd, ?_, by simp [Nat.two_pow_pos], by simp, ?_⟩, hsafe⟩
  · simp only [BitVec.toNat_shiftLeft, Nat.add_zero]
    have e : (2 : Nat) ^ 32 = 2 ^ s * 2 ^ (32 - s) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [Nat.shiftLeft_eq, e, Nat.mul_mod_mul_right]
  · simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end W32

namespace W64

variable {n d r q c r' q' c' : BitVec 64} {k : Nat}

/-- The invariant for values, and what keeps the loop's comparison from overflowing: a divisor with its top bit set only
gets one step, on a remainder of the size the start of the loop gives it. -/
structure St (n d : BitVec 64) (k : Nat) (r q c : BitVec 64) : Prop where
  inv : ∃ Q, Inv 64 n.toNat d.toNat k r.toNat q.toNat c.toNat Q
  safe : 0 < k → d.msb = true → k = 1 ∧ 4611686018427387904#64 ≤ r ∧ r < 9223372036854775808#64

theorem toNat_and_one (x : BitVec 64) : (x &&& 1#64).toNat = x.toNat % 2 :=
  Div.toNat_and_one x (by omega)

theorem St.congr (h : St n d k r q c) (hr : r' = r) (hq : q' = q) (hc : c' = c) : St n d k r' q' c' := by
  subst hr hq hc; exact h

theorem St.carry_le (h : St n d k r q c) : c ≤ 1#64 := by
  obtain ⟨_, hi⟩ := h.inv
  simpa [BitVec.le_def] using hi.hc

theorem St.lt (h : St n d k r q c) : r < d := by
  obtain ⟨_, hi⟩ := h.inv
  simpa [BitVec.lt_def] using hi.hr

/-- One step of the loop on values. -/
theorem St.iter (h : St n d (k + 1) r q c) :
    let r1 := (r <<< 1#64) ||| (q >>> 63#64)
    let s := d + (r1 ^^^ 18446744073709551615#64)
    St n d k (r1 - if s.slt 0#64 = true then d else 0#64) ((q <<< 1#64) ||| c) (s >>> 63#64) := by
  intro r1 s
  obtain ⟨Q, hi⟩ := h.inv
  have hlt := h.lt
  have hc := h.carry_le
  have hsafe := h.safe (by omega)
  have hsmall : d.msb = false ∨ (4611686018427387904#64 ≤ r ∧ r < 9223372036854775808#64) := by
    cases hm : d.msb
    · exact Or.inl rfl
    · exact Or.inr (hsafe hm).2
  have hs : (s.slt 0#64 = true) ↔ d ≤ r1 := by
    simp only [s, r1]
    rcases hsmall with hm | hm
    · have : d < 9223372036854775808#64 := by bv_decide
      bv_decide
    · have := hm.1; have := hm.2; bv_decide
  have hcarry : s >>> 63#64 = if d ≤ r1 then 1#64 else 0#64 := by
    simp only [s, r1]
    rcases hsmall with hm | hm
    · have : d < 9223372036854775808#64 := by bv_decide
      split <;> bv_decide
    · have := hm.1; have := hm.2; split <;> bv_decide
  have hr1 : r1 = (r + r) + (q >>> 63#64) := by simp only [r1]; bv_decide
  have hrsmall : r < 9223372036854775808#64 := by
    rcases hsmall with hm | hm
    · bv_decide
    · exact hm.2
  have hrN : r.toNat < 2 ^ 63 := by simpa [BitVec.lt_def] using hrsmall
  have hbN : (q >>> 63#64).toNat = q.toNat / 2 ^ 63 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hbit : q.toNat / 2 ^ 63 ≤ 1 := by have := q.isLt; omega
  have hr1N : r1.toNat = 2 * r.toNat + q.toNat / 2 ^ 63 := by
    rw [hr1, BitVec.toNat_add, BitVec.toNat_add, hbN]
    omega
  have hqN : ((q <<< 1#64) ||| c).toNat = 2 * q.toNat % 2 ^ 64 + c.toNat := by
    have e : (q <<< 1#64) ||| c = (q + q) + c := by bv_decide
    have hcN : c.toNat ≤ 1 := by simpa [BitVec.le_def] using hc
    rw [e, BitVec.toNat_add, BitVec.toNat_add]
    have := q.isLt
    omega
  have hle : (d ≤ r1) ↔ d.toNat ≤ r1.toNat := by simp [BitVec.le_def]
  have stepped := hi.step
  simp only at stepped
  refine ⟨⟨2 * Q + c.toNat, ?_⟩, ?_⟩
  · have hrr : (r1 - if s.slt 0#64 = true then d else 0#64).toNat =
        if d.toNat ≤ 2 * r.toNat + q.toNat / 2 ^ (64 - 1) then 2 * r.toNat + q.toNat / 2 ^ (64 - 1) - d.toNat
        else 2 * r.toNat + q.toNat / 2 ^ (64 - 1) := by
      simp only [show 64 - 1 = 63 from rfl]
      by_cases hd : d ≤ r1
      · rw [ite_eq_left (hs.mpr hd), BitVec.toNat_sub_of_le hd, hr1N]
        have := hle.mp hd
        rw [hr1N] at this
        rw [ite_eq_left this]
      · rw [ite_eq_right (fun e => hd (hs.mp e))]
        have h' : ¬ d.toNat ≤ 2 * r.toNat + q.toNat / 2 ^ 63 := by rw [← hr1N]; exact fun e => hd (hle.mpr e)
        rw [ite_eq_right h']
        simpa using hr1N
    have hcc : (s >>> 63#64).toNat =
        if d.toNat ≤ 2 * r.toNat + q.toNat / 2 ^ (64 - 1) then 1 else 0 := by
      simp only [show 64 - 1 = 63 from rfl]
      rw [hcarry]
      by_cases hd : d ≤ r1
      · have := hle.mp hd
        rw [hr1N] at this
        simp [hd, this]
      · have h' : ¬ d.toNat ≤ 2 * r.toNat + q.toNat / 2 ^ 63 := by rw [← hr1N]; exact fun e => hd (hle.mpr e)
        simp [hd, h']
    rw [hrr, hqN, hcc]
    exact stepped
  · intro hk hm
    have := (hsafe hm).1
    omega

/-- What the loop leaves, once no bits are left to bring down. -/
theorem St.finish (h : St n d 0 r q c) : c ||| (q <<< 1#64) = n / d ∧ r = n % d := by
  obtain ⟨Q, hi⟩ := h.inv
  obtain ⟨hdiv, hmod, hq⟩ := hi.finish
  have hc := h.carry_le
  have hcN : c.toNat ≤ 1 := hi.hc
  have hdpos : 0 < d.toNat := by have := hi.hr; omega
  constructor
  · have e : c ||| (q <<< 1#64) = (q + q) + c := by bv_decide
    rw [e]
    apply BitVec.eq_of_toNat_eq
    have hlt : n.toNat / d.toNat < 2 ^ 64 := by
      have := n.isLt
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_udiv, hdiv] at *
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod, hmod]

/-- Where the loop starts: `n`'s top bits are the first remainder, and the rest wait at the top of `q`. -/
theorem St.start {s : Nat} (hs : s ≤ 64) (hrd : n >>> s < d)
    (hsafe : 0 < s → d.msb = true → s = 1 ∧ 4611686018427387904#64 ≤ n >>> s ∧ n >>> s < 9223372036854775808#64) :
    St n d s (n >>> s) (n <<< (64 - s)) 0#64 := by
  refine ⟨⟨0, hs, by simpa [BitVec.lt_def] using hrd, ?_, by simp [Nat.two_pow_pos], by simp, ?_⟩, hsafe⟩
  · simp only [BitVec.toNat_shiftLeft, Nat.add_zero]
    have e : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [Nat.shiftLeft_eq, e, Nat.mul_mod_mul_right]
  · simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end W64

end Llvm.Div
