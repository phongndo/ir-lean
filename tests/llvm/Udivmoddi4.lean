import CrtUdivmoddi4
import Kit
import Div
import Words

/-! compiler-rt's `__udivmoddi4`, the 64-bit division that 32-bit targets call. It has a path for each special case, and otherwise
the same shift-and-subtract loop as `Div.lean`, kept in two halves of a register each. -/

set_option linter.unusedSimpArgs false

namespace Llvm.Udivmoddi4

open IRLean Llvm.Div.W64

/-- Where the remainder goes: a pointer that may be asked if it's null, and what storing through it does. -/
structure RemOut (m : Mem) (rem : Ptr) (isNull : Bool) (store : BitVec 64 → Mem) : Prop where
  observe : ∀ {α : Type} (k : Outcome α), Mem.observeAddress (some rem) true k = k
  null : (m.addr rem == m.addr Ptr.null) = isNull
  stored : isNull = false → ∀ r, Mem.storeInt m (some rem) (some r) 8 = Outcome.ok (store r)

local macro "usimp " O:term : tactic => `(tactic| llvm_simp [CrtUdivmoddi4._udivmoddi4.step, CrtUdivmoddi4._udivmoddi4.G0.step,
  CrtUdivmoddi4._udivmoddi4.G1.step, CrtUdivmoddi4._udivmoddi4.G2.step, RemOut.observe $O, RemOut.null $O, toVal_some])

local macro "ustep " O:term : tactic => `(tactic| (rw [run]; usimp $O))

/-- Memory afterward. -/
def after (m : Mem) (isNull : Bool) (store : BitVec 64 → Mem) (r : BitVec 64) : Mem := if isNull then m else store r

variable {m : Mem} {rem : Ptr} {isNull : Bool} {store : BitVec 64 → Mem} {a b : BitVec 64}

/-! ### Arithmetic for the special cases -/

theorem small (h : a >>> 32#64 = 0#64) : a.toNat < 2 ^ 32 := by
  have h' : a >>> (32#64).toNat = 0#64 := h
  have := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at this ⊢
  omega

theorem toNat_low {a : BitVec 64} (h : a.toNat < 2 ^ 32) : (a.setWidth 32).toNat = a.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt h

theorem low_div (ha : a >>> 32#64 = 0#64) (hb : b >>> 32#64 = 0#64) :
    (a.setWidth 32 / b.setWidth 32).setWidth 64 = a / b ∧ (a.setWidth 32 % b.setWidth 32).setWidth 64 = a % b := by
  have sa := small ha
  have sb := small hb
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_udiv, BitVec.toNat_udiv, toNat_low sa, toNat_low sb]
    have := Nat.div_le_self a.toNat b.toNat
    exact Nat.mod_eq_of_lt (by omega)
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_umod, BitVec.toNat_umod, toNat_low sa, toNat_low sb]
    have := Nat.mod_le a.toNat b.toNat
    exact Nat.mod_eq_of_lt (by omega)

theorem less (h : a < b) : a / b = 0#64 ∧ a % b = a := by
  have h' : a.toNat < b.toNat := h
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_udiv, Nat.div_eq_of_lt h']
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_umod, Nat.mod_eq_of_lt h']

theorem high_div (ha : a &&& 4294967295#64 = 0#64) (hb : b &&& 4294967295#64 = 0#64) :
    ((a >>> 32#64).setWidth 32 / (b >>> 32#64).setWidth 32).setWidth 64 = a / b ∧
    ((a >>> 32#64).setWidth 32 % (b >>> 32#64).setWidth 32).setWidth 64 <<< 32#64 = a % b := by
  have ea : ((a >>> 32#64).setWidth 32).setWidth 64 <<< 32#64 = a := by bv_decide
  have eb : ((b >>> 32#64).setWidth 32).setWidth 64 <<< 32#64 = b := by bv_decide
  generalize (a >>> 32#64).setWidth 32 = A at *
  generalize (b >>> 32#64).setWidth 32 = B at *
  have hA := A.isLt
  have hB := B.isLt
  have tz : ∀ X : BitVec 32, (X.setWidth 64 <<< 32#64).toNat = X.toNat * 2 ^ 32 := by
    intro X
    have hX := X.isLt
    show (X.setWidth 64 <<< (32#64).toNat).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  subst ea eb
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, tz, tz, Nat.mul_div_mul_right _ _ (by decide), BitVec.toNat_setWidth, BitVec.toNat_udiv]
    have := Nat.div_le_self A.toNat B.toNat
    exact Nat.mod_eq_of_lt (by omega)
  · rw [show (A % B).setWidth 64 <<< 32#64 = _ from rfl]
    apply BitVec.eq_of_toNat_eq
    rw [tz, BitVec.toNat_umod, BitVec.toNat_umod, tz, tz, Nat.mul_mod_mul_right]

theorem pow2_div {k : Nat} (hk : k < 64) : a / (1#64 <<< k) = a >>> k ∧ a % (1#64 <<< k) = a &&& ((1#64 <<< k) - 1#64) := by
  have hp : (2 : Nat) ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hk
  have ht : (1#64 <<< k).toNat = 2 ^ k := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.one_mul]
    exact Nat.mod_eq_of_lt hp
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, ht, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · apply BitVec.eq_of_toNat_eq
    have h1 : 1#64 ≤ 1#64 <<< k := by
      show (1#64).toNat ≤ (1#64 <<< k).toNat
      rw [ht]
      exact Nat.two_pow_pos k
    rw [BitVec.toNat_umod, ht, BitVec.toNat_and, BitVec.toNat_sub_of_le h1, ht]
    exact (Nat.and_two_pow_sub_one_eq_mod _ _).symm

/-! ### The loop -/

theorem start32 {sr : BitVec 32} (h1 : 1#32 ≤ sr) (h2 : sr ≤ 63#32) (hrd : a >>> sr < b)
    (hsafe : b.msb = true → sr = 1#32 ∧ 4611686018427387904#64 ≤ a >>> sr ∧ a >>> sr < 9223372036854775808#64) :
    St a b sr.toNat (a >>> sr) (a <<< (64#32 - sr)) 0#64 := by
  have h2N : sr.toNat ≤ 63 := h2
  have hrest : (64#32 - sr).toNat = 64 - sr.toNat := by
    rw [BitVec.toNat_sub_of_le (by bv_decide)]
    rfl
  have h := St.start (n := a) (d := b) (s := sr.toNat) (by omega) hrd (fun _ hm => by
    obtain ⟨e1, e2, e3⟩ := hsafe hm
    exact ⟨by rw [e1]; rfl, e2, e3⟩)
  rw [← hrest] at h
  exact h

theorem for_end_run (O : RemOut m rem isNull store) {q r c : BitVec 64} {qh ql : BitVec 32} (hq : qh ++ ql = q) (hc : c ≤ 1#64)
    (hres : c ||| (q <<< 1#64) = a / b) (hr : r = a % b) :
    run CrtUdivmoddi4._udivmoddi4.step (.g2 (.for_end m (some rem) (some qh) (some ql) (some c) (some r))) =
      Outcome.ok (some (a / b), after m isNull store (a % b)) := by
  have hval : (BitVec.setWidth 64 ql <<< 1#64 ||| BitVec.setWidth 64 qh <<< 33#64) ||| c = a / b := by
    rw [← hres, ← hq]
    bv_decide
  ustep O
  apply ite_cases <;> intro hn
  · have hn' : isNull = true := by simpa using hn
    subst hn'
    ustep O
    try ustep O
    rw [hval]
    rfl
  · have hn' : isNull = false := by simpa using hn
    subst hn'
    ustep O
    rw [O.stored rfl r]
    usimp O
    repeat ustep O
    rw [hval, hr]
    rfl

/-- The loop, with `k + 1` steps to go. It's a definition so `bv_decide` doesn't try to look inside it, as the hypothesis of the
induction. -/
def LoopOK (m : Mem) (rem : Ptr) (isNull : Bool) (store : BitVec 64 → Mem) (a b : BitVec 64) (k : Nat) : Prop :=
  ∀ (c rl rh ql qh sr : BitVec 32), sr.toNat = k + 1 → St a b (k + 1) (rh ++ rl) (qh ++ ql) (c.setWidth 64) →
    run CrtUdivmoddi4._udivmoddi4.step
      (.g2 (.for_body m (some c) (some sr) (some rl) (some rh) (some ql) (some qh) (some b) (some rem))) =
    Outcome.ok (some (a / b), after m isNull store (a % b))

theorem loop (O : RemOut m rem isNull store) (k : Nat) : LoopOK m rem isNull store a b k := by
  induction k with
  | zero =>
    intro c rl rh ql qh sr hsr hS
    have hc := hS.carry_le
    have hc' : c ≤ 1#32 := by bv_decide
    have hsr1 : sr = 1#32 := BitVec.eq_of_toNat_eq hsr
    subst hsr1
    have h1 := hS.iter
    simp only at h1
    have h2 : St a b 0 ((BitVec.setWidth 64 (rh <<< 1#32 ||| rl >>> 31#32) <<< 32#64 |||
        BitVec.setWidth 64 (rl <<< 1#32 ||| qh >>> 31#32)) -
          if (b + ((BitVec.setWidth 64 (rh <<< 1#32 ||| rl >>> 31#32) <<< 32#64 |||
            BitVec.setWidth 64 (rl <<< 1#32 ||| qh >>> 31#32)) ^^^ 18446744073709551615#64)).slt 0#64 = true then b else 0#64)
        ((qh <<< 1#32 ||| ql >>> 31#32) ++ (c ||| ql <<< 1#32))
        ((b + ((BitVec.setWidth 64 (rh <<< 1#32 ||| rl >>> 31#32) <<< 32#64 |||
        BitVec.setWidth 64 (rl <<< 1#32 ||| qh >>> 31#32)) ^^^ 18446744073709551615#64)) >>> 63#64) := by
      apply h1.congr <;> bv_decide
    clear h1 hS
    ustep O
    rw [ite_eq_left (by decide)]
    exact for_end_run O rfl h2.carry_le h2.finish.1 h2.finish.2
  | succ k ih =>
    intro c rl rh ql qh sr hsr hS
    have hc := hS.carry_le
    have hc' : c ≤ 1#32 := by bv_decide
    have hsr' : (sr + 4294967295#32).toNat = k + 1 := by
      rw [BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      have := sr.isLt
      omega
    have hne : (sr + 4294967295#32 == 0#32) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e
      rw [e] at hsr'
      simp at hsr'
    obtain ⟨Q, hi⟩ := hS.inv
    have hsr64 : sr.toNat ≤ 64 := by have := hi.hk; omega
    have hsrb : sr ≤ 64#32 := hsr64
    have hsr0 : 2#32 ≤ sr := by
      show 2 ≤ sr.toNat
      omega
    clear hi Q
    have h1 := hS.iter
    simp only at h1
    ustep O
    rw [hne]
    simp only [Bool.false_eq_true, ite_false]
    apply ih _ _ _ _ _ _ hsr'
    apply h1.congr <;> bv_decide

/-! ### Every path -/

/-- Runs what's left of a path to its end, for a remainder that may be null. -/
local macro "ufinish " O:term "," hq:term "," hr:term : tactic => `(tactic| (
  apply ite_cases <;> intro hn
  · have hn' : isNull = true := by simpa using hn
    subst hn'
    repeat ustep $O
    rw [$hq:term]
    rfl
  · have hn' : isNull = false := by simpa using hn
    subst hn'
    ustep $O
    rw [RemOut.stored $O rfl]
    usimp $O
    repeat ustep $O
    rw [$hq:term, $hr:term]
    rfl))

/-- Into the loop, given what it starts from. -/
theorem enter_body (O : RemOut m rem isNull store) {sr r0 r19 q0 q15 : BitVec 32} (h1 : 1#32 ≤ sr) (h2 : sr ≤ 63#32)
    (hr : r19 ++ r0 = a >>> sr) (hq : q15 ++ q0 = a <<< (64#32 - sr)) (hrd : a >>> sr < b)
    (hsafe : b.msb = true → sr = 1#32 ∧ 4611686018427387904#64 ≤ a >>> sr ∧ a >>> sr < 9223372036854775808#64) :
    run CrtUdivmoddi4._udivmoddi4.step
      (.g2 (.for_body m (some 0#32) (some sr) (some r0) (some r19) (some q0) (some q15) (some b) (some rem))) =
    Outcome.ok (some (a / b), after m isNull store (a % b)) := by
  have hS := start32 h1 h2 hrd hsafe
  have h1N : 1 ≤ sr.toNat := h1
  have hk : sr.toNat = (sr.toNat - 1) + 1 := by omega
  rw [hk] at hS
  apply loop O (sr.toNat - 1) _ _ _ _ _ _ hk
  apply hS.congr hr hq
  rfl

theorem enter_loop (O : RemOut m rem isNull store) {sr r0 r19 q0 q15 : BitVec 32} (h1 : 1#32 ≤ sr) (h2 : sr ≤ 63#32)
    (hr : r19 ++ r0 = a >>> sr) (hq : q15 ++ q0 = a <<< (64#32 - sr)) (hrd : a >>> sr < b)
    (hsafe : b.msb = true → sr = 1#32 ∧ 4611686018427387904#64 ≤ a >>> sr ∧ a >>> sr < 9223372036854775808#64) :
    run CrtUdivmoddi4._udivmoddi4.step
      (.g2 (.for_body_preheader m (some sr) (some r0) (some r19) (some q0) (some q15) (some b) (some rem))) =
    Outcome.ok (some (a / b), after m isNull store (a % b)) := by
  ustep O
  exact enter_body O h1 h2 hr hq hrd hsafe

/-- The code when `a` and `b` are both small or `b` is above `a`'s top half. -/
theorem path_small (O : RemOut m rem isNull store) (ha : a >>> 32#64 = 0#64) (hb0 : b ≠ 0#64) :
    run CrtUdivmoddi4._udivmoddi4.step
      (.g0 (.if_then m (some a) (some rem) (some (a.setWidth 32)) (some (b.setWidth 32)) (some (b >>> 32#64)))) =
    Outcome.ok (some (a / b), after m isNull store (a % b)) := by
  ustep O
  apply ite_cases <;> intro h2
  · have hb : b >>> 32#64 = 0#64 := by simpa using h2
    obtain ⟨hq, hr⟩ := low_div ha hb
    have hlo : b.setWidth 32 ≠ 0#32 := by bv_decide
    ustep O
    apply ite_cases <;> intro hn
    · have hn' : isNull = true := by simpa using hn
      subst hn'
      repeat ustep O
      rw [hq]
      rfl
    · have hn' : isNull = false := by simpa using hn
      subst hn'
      ustep O
      rw [O.stored rfl, hr]
      usimp O
      repeat ustep O
      rw [hq]
      rfl
  · have hlt : a < b := by
      have : ¬ b >>> 32#64 = 0#64 := by simpa using h2
      bv_decide
    obtain ⟨hq, hr⟩ := less hlt
    ustep O
    apply ite_cases <;> intro hn
    · have hn' : isNull = true := by simpa using hn
      subst hn'
      repeat ustep O
      rw [hq]
      rfl
    · have hn' : isNull = false := by simpa using hn
      subst hn'
      ustep O
      rw [O.stored rfl]
      usimp O
      repeat ustep O
      rw [hq, hr]
      rfl

/-- Everything else: `a` has something in its top half. -/
theorem path_big (O : RemOut m rem isNull store) (ha : a >>> 32#64 ≠ 0#64) (hb0 : b ≠ 0#64) :
    run CrtUdivmoddi4._udivmoddi4.step
      (.g0 (.if_end16 m (some a) (some b) (some rem) (some (a.setWidth 32)) (some (a >>> 32#64)) (some ((a >>> 32#64).setWidth 32))
        (some (b.setWidth 32)) (some (b >>> 32#64)) (some ((b >>> 32#64).setWidth 32)))) =
    Outcome.ok (some (a / b), after m isNull store (a % b)) := by
  have hhi : (a >>> 32#64).setWidth 32 ≠ 0#32 := by bv_decide
  ustep O
  apply ite_cases <;> intro hdlo
  · -- `b`'s bottom half is zero.
    have hd : b.setWidth 32 = 0#32 := by simpa using hdlo
    have hdh : (b >>> 32#64).setWidth 32 ≠ 0#32 := by bv_decide
    have hdh' : (b >>> 32#64 == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      bv_decide
    ustep O
    rw [hdh', ite_eq_right (by simp)]
    ustep O
    apply ite_cases <;> intro hnlo
    · -- So is `a`'s.
      have hn0 : a.setWidth 32 = 0#32 := by simpa using hnlo
      obtain ⟨hq, hr⟩ := high_div (a := a) (b := b) (by bv_decide) (by bv_decide)
      ustep O
      ufinish O, hq, hr
    · have hn0 : a.setWidth 32 ≠ 0#32 := by simpa using hnlo
      ustep O
      apply ite_cases <;> intro hpow
      · -- `b` is a power of 2, with its bit in the top half.
        have hb1 : b = 1#64 <<< (((b >>> 32#64).setWidth 32).ctz.setWidth 64 + 32#64) := by bv_decide
        have hk : ((b >>> 32#64).setWidth 32).ctz.setWidth 64 + 32#64 < 64#64 := by bv_decide
        have hkN : (((b >>> 32#64).setWidth 32).ctz.setWidth 64 + 32#64).toNat < 64 := hk
        obtain ⟨hq0, hr0⟩ := pow2_div (a := a) hkN
        have hb1' : 1#64 <<< (((b >>> 32#64).setWidth 32).ctz.setWidth 64 + 32#64).toNat = b := hb1.symm
        rw [hb1'] at hq0 hr0
        have hq : BitVec.setWidth 64 ((a >>> 32#64).setWidth 32 >>> ((b >>> 32#64).setWidth 32).ctz) = a / b := by
          rw [hq0]
          show _ = a >>> (((b >>> 32#64).setWidth 32).ctz.setWidth 64 + 32#64)
          bv_decide
        have hr : ((b >>> 32#64) + 4294967295#64 &&& a >>> 32#64) <<< 32#64 ||| a &&& 4294967295#64 = a % b := by
          rw [hr0]
          bv_decide
        ustep O
        ufinish O, hq, hr
      · -- It isn't.
        ustep O
        apply ite_cases <;> intro hbig
        · have hlt : a < b := by bv_decide
          obtain ⟨hq, hr⟩ := less hlt
          ustep O
          ufinish O, hq, hr
        · ustep O
          first | apply enter_body O <;> bv_decide | apply enter_loop O <;> bv_decide
  · -- `b`'s bottom half isn't zero.
    have hdl : b.setWidth 32 ≠ 0#32 := by simpa using hdlo
    ustep O
    apply ite_cases <;> intro hdh
    · -- Its top half is.
      ustep O
      apply ite_cases <;> intro hpow
      · -- `b` is a power of 2, with its bit in the bottom half.
        have hb1 : b = 1#64 <<< (b.setWidth 32).ctz.setWidth 64 := by bv_decide
        have hkN : ((b.setWidth 32).ctz.setWidth 64).toNat < 64 := by
          have : (b.setWidth 32).ctz.setWidth 64 < 64#64 := by bv_decide
          exact this
        obtain ⟨hq0, hr0⟩ := pow2_div (a := a) hkN
        have hb1' : 1#64 <<< ((b.setWidth 32).ctz.setWidth 64).toNat = b := hb1.symm
        rw [hb1'] at hq0 hr0
        have hr : (a &&& 4294967295#64) &&& b + 4294967295#64 = a % b := by
          rw [hr0]
          bv_decide
        -- What comes after the remainder is stored, whatever memory that left.
        have hend : ∀ M : Mem, run CrtUdivmoddi4._udivmoddi4.step (.g1 (.if_end114 M (some a) (some (a.setWidth 32))
            (some ((a >>> 32#64).setWidth 32)) (some (b.setWidth 32)))) = Outcome.ok (some (a / b), M) := by
          intro M
          ustep O
          apply ite_cases <;> intro hone
          · have hb' : b = 1#64 := by bv_decide
            have hdiv : a / b = a := by
              rw [hb']
              apply BitVec.eq_of_toNat_eq
              simp
            ustep O
            rw [hdiv]
          · have hs0 : 0#32 < (b.setWidth 32).ctz := by bv_decide
            have hs1 : (b.setWidth 32).ctz < 32#32 := by bv_decide
            have hfs : Val.fshrRaw ((a >>> 32#64).setWidth 32) (a.setWidth 32) (b.setWidth 32).ctz =
                ((a >>> 32#64).setWidth 32 <<< (32#32 - (b.setWidth 32).ctz)) ||| (a.setWidth 32 >>> (b.setWidth 32).ctz) := by
              generalize (b.setWidth 32).ctz = s at hs0 hs1
              have hsN : s.toNat < 32 := hs1
              have hs0N : 0 < s.toNat := hs0
              have hrest : (32#32 - s).toNat = 32 - s.toNat := by
                rw [BitVec.toNat_sub_of_le (by bv_decide)]
                rfl
              simp only [Val.fshrRaw]
              rw [ite_eq_right (by omega), Nat.mod_eq_of_lt hsN]
              have e1 : ∀ x : BitVec 32, x <<< (32#32 - s) = x <<< (32#32 - s).toNat := fun _ => rfl
              have e2 : ∀ x : BitVec 32, x >>> s = x >>> s.toNat := fun _ => rfl
              rw [e1, e2, hrest]
            have hq : (BitVec.setWidth 64 ((a >>> 32#64).setWidth 32 >>> (b.setWidth 32).ctz)) <<< 32#64 |||
                BitVec.setWidth 64 (((a >>> 32#64).setWidth 32 <<< (32#32 - (b.setWidth 32).ctz)) |||
                  (a.setWidth 32 >>> (b.setWidth 32).ctz)) = a / b := by
              rw [hq0]
              show _ = a >>> (b.setWidth 32).ctz.setWidth 64
              bv_decide
            ustep O
            rw [hfs, hq]
            ustep O
        ustep O
        apply ite_cases <;> intro hn
        · have hn' : isNull = true := by simpa using hn
          subst hn'
          exact hend m
        · have hn' : isNull = false := by simpa using hn
          subst hn'
          ustep O
          rw [O.stored rfl, hr]
          usimp O
          exact hend _
      · ustep O
        apply ite_cases <;> intro hmid
        · first | apply enter_body O <;> bv_decide | apply enter_loop O <;> bv_decide
        · ustep O
          apply ite_cases <;> intro hlow
          · ustep O
            first | apply enter_body O <;> bv_decide | apply enter_loop O <;> bv_decide
          · ustep O
            first | apply enter_body O <;> bv_decide | apply enter_loop O <;> bv_decide
    · ustep O
      apply ite_cases <;> intro hbig
      · have hlt : a < b := by bv_decide
        obtain ⟨hq, hr⟩ := less hlt
        ustep O
        ufinish O, hq, hr
      · ustep O
        apply ite_cases <;> intro h32
        · first | apply enter_body O <;> bv_decide | apply enter_loop O <;> bv_decide
        · ustep O
          first | apply enter_body O <;> bv_decide | apply enter_loop O <;> bv_decide

/-- What every path comes to. -/
theorem from_entry (O : RemOut m rem isNull store) (hb0 : b ≠ 0#64) :
    run CrtUdivmoddi4._udivmoddi4.step (.g0 (.entry m (some a) (some b) (some rem))) =
      Outcome.ok (some (a / b), after m isNull store (a % b)) := by
  ustep O
  apply ite_cases <;> intro h
  · exact path_small O (by simpa using h) hb0
  · exact path_big O (by simpa using h) hb0

abbrev effects : Effects := { other := .none, arg := .write, inaccessible := .none, errno := .none }

abbrev remTag (m : Mem) : Tag :=
  { call := m.nextCall, writeonly := true, nofree := true, expires := true, noAddress := true, nullCheck := true }

/-- `__udivmoddi4` with a null `rem`: for a nonzero divisor, the quotient. Division by zero is unspecified in its source, and
gives poison here. -/
theorem udivmoddi4_null (a b : BitVec 64) (hb0 : b ≠ 0#64) :
    CrtUdivmoddi4._udivmoddi4 (some a) (some b) (some Ptr.null) m = Outcome.ok (some (a / b), m.afterCall) := by
  have O : RemOut { m with
      calls := { id := m.nextCall, effects := effects, start := m.next, tracked := true } :: m.calls
      nextCall := m.nextCall + 1 } { Ptr.null with tags := remTag m :: Ptr.null.tags } true (fun _ => { m with
      calls := { id := m.nextCall, effects := effects, start := m.next, tracked := true } :: m.calls
      nextCall := m.nextCall + 1 }) := by
    refine ⟨fun k => ?_, rfl, fun h => by simp at h⟩
    simp [Mem.observeAddress, Ptr.null]
  simp only [CrtUdivmoddi4._udivmoddi4, noundef_some, Mem.call, Mem.tag, Option.map]
  rw [show run CrtUdivmoddi4._udivmoddi4.step _ = _ from from_entry (a := a) O hb0]
  rfl

/-- `__udivmoddi4`, called from outside anything that promised something about memory, with a pointer to somewhere to put the
remainder: for a nonzero divisor, the quotient, and the remainder at that pointer. -/
theorem udivmoddi4_correct {block o : Nat} {w : Nat → BitVec 64} (a b : BitVec 64) (hb0 : b ≠ 0#64) (hcalls : m.calls = [])
    (W : Words m [] block o 1 w) (hw : ∀ s, m.allocs block = some s → s.readonly = false ∧ s.stack = false)
    (hnn : m.addr (bufPtr [] block o 0) ≠ 0#64) :
    CrtUdivmoddi4._udivmoddi4 (some a) (some b) (some (bufPtr [] block o 0)) m =
      Outcome.ok (some (a / b), (m.setWords block o 1 (fun _ => a % b)).afterCall) := by
  obtain ⟨s, hs, hsz, hmax, _⟩ := W.bytes.alloc
  obtain ⟨hro, hst⟩ := hw s hs
  have hoff : (BitVec.ofNat 64 (o + 8 * 0)).toNat = o + 8 * 0 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  let m0 : Mem := { m with
    calls := { id := m.nextCall, effects := effects, start := m.next, tracked := true } :: m.calls
    nextCall := m.nextCall + 1 }
  have hs0 : m0.allocs block = some s := hs
  have hal0 : (m0.addr (bufPtr [remTag m] block o (8 * 0))).toNat % 8 = 0 := W.align
  have hcheck : m0.check (bufPtr [remTag m] block o (8 * 0)) s true = none := by
    simp [Mem.check, Mem.tagRule, Mem.isRunning, m0, hcalls, Mem.callRule, Mem.callAccess, hst, remTag, effects]
  have O : RemOut m0 (bufPtr [remTag m] block o (8 * 0)) false
      (fun r => m0.write (bufPtr [remTag m] block o (8 * 0)) s 8 (fun i => Mem.intByte r i)) := by
    refine ⟨fun k => ?_, ?_, fun _ r => ?_⟩
    · simp [Mem.observeAddress, remTag]
    · simp only [beq_eq_false_iff_ne, ne_eq]
      intro e
      exact hnn (e.trans rfl)
    · exact Words.storeInt_eq hs0 (by simp only [hoff]; omega) hal0 hro hcheck r
  simp only [CrtUdivmoddi4._udivmoddi4, noundef_some, Mem.call, Mem.tag, Option.map]
  rw [show run CrtUdivmoddi4._udivmoddi4.step _ = _ from from_entry (a := a) O hb0]
  simp only [andThen, Outcome.ok, promised_some, after, Bool.false_eq_true, ite_false, Mem.afterCall]
  have hallocs := Words.write_allocs (m := m0) hs0 hoff [remTag m] (a % b)
  have hsame : (m0.setWords block o 1 (fun _ => a % b)).allocs = (m.setWords block o 1 (fun _ => a % b)).allocs := by
    simp only [Mem.setWords, hs0, hs]
    rfl
  have hset : m.setWords block o 1 (fun _ => a % b) = m.setAlloc block (some { s with
      bytes := fun x => if o ≤ x ∧ x < o + 8 * 1 then .val (wordBytes (fun _ => a % b) (x - o)) else s.bytes x }) := by
    simp only [Mem.setWords, hs]
  generalize hM : m0.write (bufPtr [remTag m] block o (8 * 0)) s 8 (fun i => Mem.intByte (a % b) i) = M at *
  have hcall : ∃ c : Call, M.calls = [c] ∧ c.ranges = [] := by
    subst hM
    simp only [Mem.write, m0, hcalls, List.map_cons, List.map_nil]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨c, hc, hr⟩ := hcall
  have hnext : M.next = m.next := by subst hM; rfl
  have hbase : M.base = m.base := by subst hM; rfl
  have hframe : M.frame = m.frame := by subst hM; rfl
  have hfail : M.failAlloc = m.failAlloc := by subst hM; rfl
  have hnc : M.nextCall = m.nextCall + 1 := by subst hM; rfl
  rw [hc]
  simp only [hr, List.any_nil]
  congr 3
  apply Mem.ext'
  · funext b'
    rw [hallocs, hsame]
  · rw [hnext, hset]; rfl
  · rw [hbase, hset]; rfl
  · rw [hframe, hset]; rfl
  · rw [hfail, hset]; rfl
  · rw [hset]; simp [hcalls, Mem.setAlloc]
  · rw [hnc, hset]; rfl

/-- The hypotheses for the remainder can hold on real memory: 100 divided by 7 comes to 14, with 2 left over. -/
theorem udivmoddi4_check_value :
    let m := (CrtUdivmoddi4.initial).addGlobal 100 8 false #[0, 0, 0, 0, 0, 0, 0, 0]
    ∃ w, Words m [] 100 0 1 w ∧ CrtUdivmoddi4._udivmoddi4 (some 100#64) (some 7#64) (some (bufPtr [] 100 0 0)) m =
      Outcome.ok (some 14#64, (m.setWords 100 0 1 (fun _ => 2#64)).afterCall) := by
  intro m
  have hzero : ∀ i : Nat, (#[0, 0, 0, 0, 0, 0, 0, 0] : Array Nat)[i]?.getD 0 = 0 := by
    intro i
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
    | n + 8 => simp
  have B := Readable.ofGlobal CrtUdivmoddi4.initial 100 #[0, 0, 0, 0, 0, 0, 0, 0] rfl (by decide) (by decide) (by decide)
  have hdata : (fun i : Nat => BitVec.ofNat 8 ((#[0, 0, 0, 0, 0, 0, 0, 0] : Array Nat)[i]?.getD 0)) = wordBytes (fun _ => 0#64) := by
    funext i
    rw [hzero]
    simp [wordBytes]
  rw [hdata] at B
  have W : Words m [] 100 0 1 (fun _ => 0#64) := ⟨B.toReachable, by decide⟩
  refine ⟨_, W, ?_⟩
  have hw : ∀ s, m.allocs 100 = some s → s.readonly = false ∧ s.stack = false := by
    intro s hs
    have : some { size := 8, readonly := false, bytes := Mem.globalBytes #[0, 0, 0, 0, 0, 0, 0, 0] } = some s := hs
    cases this
    exact ⟨rfl, rfl⟩
  have e1 : 100#64 / 7#64 = 14#64 := by decide
  have e2 : 100#64 % 7#64 = 2#64 := by decide
  rw [udivmoddi4_correct 100#64 7#64 (by decide) rfl W hw (by decide), e1, e2]

end Llvm.Udivmoddi4
