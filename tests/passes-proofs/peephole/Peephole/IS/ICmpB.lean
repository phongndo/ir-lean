import Peephole.Match
import Peephole.Oracle
import Peephole.Fold
import Peephole.IS.Add
import Peephole.Lemmas.ICmpB

/-! # What the `icmp-b` family's folds share

The folds in `Peephole.IS.ICmpBOnLHS`, `ICmpBBinOp`, `ICmpBMinMax`, `ICmpBAndOr`, `ICmpBSelect` and `ICmpBSelectCond`
answer for an `icmp`, a `select` or an `and`/`or` of compares. None is called on an instruction by InstSimplify's dispatcher: `simplifyICmpInst`,
`simplifySelectInst`, `simplifyAndInst` and `simplifyOrInst` forward to them. Each one's `sound` theorem is stated over
its own C++ arguments, with the instruction its answer replaces, so those callers' models can use it.

This file has what they share:

- `CmpInst`'s predicate algebra: `swapP` is `getSwappedPredicate`, `invP` is `getInversePredicate`, `strictP` is
  `getStrictPredicate`, and `test` is what a predicate says about two values that aren't poison.
- `icmpSrc p s a b`, the compare `icmp [samesign] p a b` a fold replaces, and `boolR`, `getTrue` and `getFalse`.
- `refines_bool`, which turns "the compare is `r` on every pair of values" into a refinement, poison and `samesign`
  included.
- `fwd`, a forward to a fold modelled here, and `ICmpSimp`, the recursive `simplifyICmpInst(…, MaxRecurse - 1)` a
  fold calls, with `ICmpSimp.Sound`, the hypothesis that its answers are right.
- `same`, `==` on two `Value *` of possibly different types, which are the same pointer only at one type.
- `WellTyped`, that casts go the way LLVM's verifier requires.

`CmpPredicate` is a predicate and a `samesign` flag. Comparing it with a predicate, as `Pred == ICMP_SLT`, ignores
`samesign`, and `ICmpInst::getSwappedPredicate(Pred)` and `getInversePredicate` drop it. A model here takes the
predicate as `Pred`, and the flag separately where the C++ passes it on. -/

namespace Peephole.IS.ICmpB

open IRLean

variable {w u : Nat}

/-! ### Predicates -/

/-- `CmpInst::getSwappedPredicate`: the predicate with its operands swapped. -/
def swapP : Pred → Pred
  | .eq => .eq | .ne => .ne
  | .ugt => .ult | .uge => .ule | .ult => .ugt | .ule => .uge
  | .sgt => .slt | .sge => .sle | .slt => .sgt | .sle => .sge

/-- `CmpInst::getInversePredicate`: the predicate's negation. -/
def invP : Pred → Pred
  | .eq => .ne | .ne => .eq
  | .ugt => .ule | .uge => .ult | .ult => .uge | .ule => .ugt
  | .sgt => .sle | .sge => .slt | .slt => .sge | .sle => .sgt

/-- `CmpInst::getStrictPredicate`: `uge`, `ule`, `sge` and `sle` lose their `e`; the rest stay. -/
def strictP : Pred → Pred
  | .uge => .ugt | .ule => .ult | .sge => .sgt | .sle => .slt
  | p => p

/-- `ICmpInst::isEquality`. -/
def isEquality (p : Pred) : Bool := p == .eq || p == .ne

/-- `ICmpInst::isRelational`. -/
def isRelational (p : Pred) : Bool := !isEquality p

/-- `CmpInst::isSigned`. -/
def isSigned (p : Pred) : Bool := p == .sgt || p == .sge || p == .slt || p == .sle

/-- `CmpInst::isUnsigned`. -/
def isUnsigned (p : Pred) : Bool := p == .ugt || p == .uge || p == .ult || p == .ule

/-- What `icmp p` says of two values that aren't poison. -/
def test : Pred → BitVec w → BitVec w → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .ugt, x, y => BitVec.ult y x
  | .uge, x, y => BitVec.ule y x
  | .ult, x, y => BitVec.ult x y
  | .ule, x, y => BitVec.ule x y
  | .sgt, x, y => BitVec.slt y x
  | .sge, x, y => BitVec.sle y x
  | .slt, x, y => BitVec.slt x y
  | .sle, x, y => BitVec.sle x y

theorem eval_some (p : Pred) (x y : BitVec w) (s : Bool) :
    p.eval (some x) (some y) s = if s && x.msb != y.msb then none else some (BitVec.ofBool (test p x y)) := by
  cases p <;> rfl

@[simp] theorem eval_none_left (p : Pred) (b : Val w) (s : Bool) : p.eval none b s = none := by
  cases p <;> rfl

@[simp] theorem eval_none_right (p : Pred) (a : Val w) (s : Bool) : p.eval a none s = none := by
  cases p <;> cases a <;> rfl

theorem test_swap (p : Pred) (x y : BitVec w) : test (swapP p) y x = test p x y := by
  have h : (y == x) = (x == y) := Bool.eq_iff_iff.2 (by simp only [beq_iff_eq]; exact eq_comm)
  cases p <;> simp only [swapP, test, bne, h]

theorem test_inv (p : Pred) (x y : BitVec w) : test (invP p) x y = !test p x y := by
  cases p <;> simp only [invP, test, bne, Bool.not_not] <;>
    simp [Lemmas.ule_eq_not_ult, Lemmas.sle_eq_not_slt]

theorem eval_swap (p : Pred) (a b : Val w) (s : Bool) : (swapP p).eval b a s = p.eval a b s := by
  cases a with
  | none => simp
  | some x =>
  cases b with
  | none => simp
  | some y =>
  rw [eval_some, eval_some, test_swap]
  cases x.msb <;> cases y.msb <;> rfl

/-- A compare with `samesign` is poison wherever the one without it differs. -/
theorem eval_le_plain (p : Pred) (a b : Val w) (s : Bool) : Refine.le (p.eval a b s) (p.eval a b false) := by
  cases a with
  | none => rw [eval_none_left]; exact Refine.val_none _
  | some x =>
  cases b with
  | none => rw [eval_none_right]; exact Refine.val_none _
  | some y =>
  rw [eval_some, eval_some]
  split
  · exact Refine.val_none _
  · exact Refine.refl_val _

/-! ### What a fold replaces, and what it answers -/

/-- `getTrue(ITy)` and `getFalse(ITy)`, and `ConstantInt::getBool`. -/
def boolR (b : Bool) : Repl 1 := .const (BitVec.ofBool b)

/-- The compare `icmp [samesign] p a b` a fold replaces. -/
def icmpSrc (p : Pred) (s : Bool) (a b : Term w) : Repl 1 := .icmp p s (.old a) (.old b)

theorem icmpSrc_eval (ρ : Env) (p : Pred) (s : Bool) (a b : Term w) :
    (icmpSrc p s a b).eval ρ = Outcome.ok (p.eval (a.denote ρ) (b.denote ρ) s) := rfl

theorem boolR_eval (ρ : Env) (b : Bool) : (boolR b).eval ρ = Outcome.ok (some (BitVec.ofBool b)) := rfl

/-- A compare that's `r` whenever neither operand is poison refines `r`, with or without `samesign`. -/
theorem refines_bool {ρ : Env} {p : Pred} {s : Bool} {a b : Term w} {r : Bool}
    (h : ∀ x y, a.denote ρ = some x → b.denote ρ = some y → test p x y = r) :
    Refines ((icmpSrc p s a b).eval ρ) ((boolR r).eval ρ) := by
  rw [icmpSrc_eval, boolR_eval]
  refine refines_ok ?_
  cases ha : a.denote ρ with
  | none => rw [eval_none_left]; exact Refine.val_none _
  | some x =>
  cases hb : b.denote ρ with
  | none => rw [eval_none_right]; exact Refine.val_none _
  | some y =>
  rw [eval_some, h x y ha hb]
  split
  · exact Refine.val_none _
  · exact Refine.refl_val _

/-- What refines a compare without `samesign` refines it with. -/
theorem refines_of_plain {ρ : Env} {p : Pred} {s : Bool} {a b : Term w} {r : Outcome (Val 1)}
    (h : Refines ((icmpSrc p false a b).eval ρ) r) : Refines ((icmpSrc p s a b).eval ρ) r :=
  Refines.trans (refines_ok (eval_le_plain p _ _ s)) h

/-- `icmp p a b` is `icmp (swapP p) b a`, `samesign` and all. -/
theorem icmpSrc_swap (ρ : Env) (p : Pred) (s : Bool) (a b : Term w) :
    (icmpSrc (swapP p) s b a).eval ρ = (icmpSrc p s a b).eval ρ := by
  rw [icmpSrc_eval, icmpSrc_eval, eval_swap]

/-! ### Forwards -/

/-- `if (Value *V = g(...)) return V;`, where `g` is a fold modelled here: `g`'s answer, or fall through. Its site is
`g`'s name, and its theorem is `g`'s `sound`. -/
def fwd (callee : String) : Result w → Step w
  | .value r => .fire callee r
  | .null => .next
  | .delegated c => .delegate c

theorem fwd_fire {c s : String} {res : Result w} {r : Repl w} (h : fwd c res = .fire s r) : res = .value r := by
  cases res <;> simp_all [fwd]

/-- `if (Value *V = g(...)) return V;`, where the model doesn't say what `g` answers: fall through if it declines,
and claim nothing if it doesn't. -/
def delegUnlessNull (callee : String) : Result w → Step w
  | .null => .next
  | _ => .delegate callee

theorem delegUnlessNull_ne_fire {c s : String} {res : Result w} {r : Repl w} :
    delegUnlessNull c res ≠ .fire s r := by
  cases res <;> simp [delegUnlessNull]

/-- A recursive call `simplifyICmpInst(Pred, LHS, RHS, Q, MaxRecurse - 1)`: what InstSimplify answers for the compare
`icmp [samesign] Pred LHS RHS`, at a recursion budget. Folds here take it as a parameter, since it's
`simplifyICmpInst`'s model, which they don't have. -/
abbrev ICmpSimp := (p : Pred) → (samesign : Bool) → {w : Nat} → Term w → Term w → Nat → Result 1

/-- The recursive call is right: whatever it answers refines the compare it was asked about, for operands consistent
with the run and with no `undef`. A theorem that takes this hypothesis names it. -/
def ICmpSimp.Sound (simp : ICmpSimp) (ρ : Env) : Prop :=
  ∀ (p : Pred) (s : Bool) {w : Nat} (a b : Term w) (n : Nat) (r : Repl 1), a.Consistent ρ → b.Consistent ρ →
    a.hasUndef = false → b.hasUndef = false → simp p s a b n = .value r →
      Refines ((icmpSrc p s a b).eval ρ) (r.eval ρ)

/-- The recursive `simplifyICmpInst`, handed on: every call delegated, which claims nothing. `simplifyICmpInst`'s model
passes it to the folds here it forwards to. -/
def ICmpSimp.delegating : ICmpSimp := fun _ _ {_} _ _ _ => .delegated "simplifyICmpInst"

theorem ICmpSimp.delegating_sound (ρ : Env) : ICmpSimp.delegating.Sound ρ := by
  intro _ _ _ _ _ _ _ _ _ _ _ h
  simp [ICmpSimp.delegating] at h

/-! ### Pointers of different types -/

/-- `A == B` for two `Value *` of possibly different types: a pointer has one type, so they're the same pointer only at
the same width, as the same `Value`. -/
def same (a : Term u) (b : Term w) : Bool := u == w && a.ident == b.ident

theorem same_width {a : Term u} {b : Term w} (h : same a b = true) : u = w := by
  simp only [same, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem same_self (a : Term w) : same a a = true := by simp [same]

theorem same_iff_specific (a b : Term w) : same a b = specific a b := by
  simp only [same, specific, beq_self_eq_true, Bool.true_and]
  exact Bool.eq_iff_iff.2 (by simp only [beq_iff_eq]; exact eq_comm)

/-! ### Well-typed casts -/

/-- The casts in an operand go the way LLVM's verifier requires: `zext` and `sext` widen, `trunc` narrows. `Term`
doesn't say so itself. -/
def WellTyped : {w : Nat} → Term w → Prop
  | _, .const _ | _, .poison | _, .undef | _, .var _ => True
  | _, .bin _ _ _ a b | _, .icmp _ _ _ a b | _, .bi _ _ a b => WellTyped a ∧ WellTyped b
  | _, .select _ c t e => WellTyped c ∧ WellTyped t ∧ WellTyped e
  | w, @Term.zext v _ _ _ a => v < w ∧ WellTyped a
  | w, @Term.sext v _ _ a => v < w ∧ WellTyped a
  | w, @Term.trunc v _ _ _ _ a => w < v ∧ WellTyped a
  | _, .freeze _ a | _, .un _ _ a => WellTyped a
  | _, .fsh _ _ a b c => WellTyped a ∧ WellTyped b ∧ WellTyped c

/-! ### What a matched binary operator's value is -/

theorem bin_val {ρ : Env} {t a b : Term w} {op : BinOp} {f : Flags} (h : binop? op t = some (f, a, b))
    (hc : t.Consistent ρ) : op.eval f (a.denote ρ) (b.denote ρ) = Outcome.ok (t.denote ρ) :=
  (binop?_consistent h hc).2.2

theorem or_some {a b : Val w} {d : Bool} {x : BitVec w} (h : Val.or a b d = some x) :
    ∃ p q, a = some p ∧ b = some q ∧ x = p ||| q := by
  cases a with
  | none => cases h
  | some p =>
  cases b with
  | none => cases h
  | some q =>
  simp only [Val.or] at h
  split at h
  · cases h
  · exact ⟨p, q, rfl, rfl, (Option.some.inj h).symm⟩

theorem lshr_some {a b : Val w} {e : Bool} {x : BitVec w} (h : Val.lshr a b e = some x) :
    ∃ p q, a = some p ∧ b = some q ∧ q.toNat < w ∧ x = p >>> q := by
  cases a with
  | none => cases h
  | some p =>
  cases b with
  | none => cases h
  | some q =>
  simp only [Val.lshr] at h
  split at h
  · cases h
  · next hq =>
    split at h
    · cases h
    · refine ⟨p, q, rfl, rfl, ?_, (Option.some.inj h).symm⟩
      simpa [Generic.shiftOk_iff] using hq

theorem shl_some {a b : Val w} {nuw nsw : Bool} {x : BitVec w} (h : Val.shl a b nuw nsw = some x) :
    ∃ p q, a = some p ∧ b = some q ∧ q.toNat < w ∧ x = p <<< q ∧
      (nuw = true → (p <<< q) >>> q = p) ∧ (nsw = true → (p <<< q).sshiftRight' q = p) := by
  cases a with
  | none => cases h
  | some p =>
  cases b with
  | none => cases h
  | some q =>
  simp only [Val.shl] at h
  split at h
  · cases h
  · next hq =>
    split at h
    · cases h
    · next hu =>
      split at h
      · cases h
      · next hs =>
        refine ⟨p, q, rfl, rfl, by simpa [Generic.shiftOk_iff] using hq, (Option.some.inj h).symm, ?_, ?_⟩
        · intro hn; subst hn; simpa using hu
        · intro hn; subst hn; simpa using hs

theorem mul_some {a b : Val w} {nuw nsw : Bool} {x : BitVec w} (h : Val.mul a b nuw nsw = some x) :
    ∃ p q, a = some p ∧ b = some q ∧ x = p * q := by
  cases a with
  | none => cases h
  | some p =>
  cases b with
  | none => cases h
  | some q =>
  simp only [Val.mul] at h
  split at h
  · cases h
  · exact ⟨p, q, rfl, rfl, (Option.some.inj h).symm⟩

theorem sub_some {a b : Val w} {nuw nsw : Bool} {x : BitVec w} (h : Val.sub a b nuw nsw = some x) :
    ∃ p q, a = some p ∧ b = some q ∧ x = p - q := by
  cases a with
  | none => cases h
  | some p =>
  cases b with
  | none => cases h
  | some q =>
  simp only [Val.sub] at h
  split at h
  · cases h
  · exact ⟨p, q, rfl, rfl, (Option.some.inj h).symm⟩

theorem add_some {a b : Val w} {nuw nsw : Bool} {x : BitVec w} (h : Val.add a b nuw nsw = some x) :
    ∃ p q, a = some p ∧ b = some q ∧ x = p + q ∧ (nuw = true → p.uaddOverflow q = false) ∧
      (nsw = true → p.saddOverflow q = false) := by
  cases a with
  | none => cases h
  | some p =>
  cases b with
  | none => cases h
  | some q =>
  simp only [Val.add] at h
  split at h
  · cases h
  · next hf =>
    refine ⟨p, q, rfl, rfl, (Option.some.inj h).symm, ?_, ?_⟩
    · intro hn; subst hn; simp_all
    · intro hn; subst hn; simp_all

/-- A `urem` that ran has a non-zero divisor, and is the remainder where the dividend isn't poison. -/
theorem urem_ok {a b r : Val w} (h : Val.urem a b = Outcome.ok r) :
    ∃ q, b = some q ∧ q ≠ 0#w ∧ ∀ x, r = some x → ∃ p, a = some p ∧ x = p % q := by
  cases b with
  | none => cases h
  | some q =>
  simp only [Val.urem] at h
  split at h
  · cases h
  · next hq =>
    refine ⟨q, rfl, by simpa using hq, ?_⟩
    intro x hx
    subst hx
    cases a with
    | none => cases h
    | some p => exact ⟨p, rfl, (Option.some.inj (ok_inj h)).symm⟩

/-- A `udiv` that ran has a non-zero divisor, and is the quotient where it isn't poison. -/
theorem udiv_ok {a b r : Val w} {e : Bool} (h : Val.udiv a b e = Outcome.ok r) :
    ∃ q, b = some q ∧ q ≠ 0#w ∧ ∀ x, r = some x → ∃ p, a = some p ∧ x = p / q := by
  cases b with
  | none => cases h
  | some q =>
  simp only [Val.udiv] at h
  split at h
  · cases h
  · next hq =>
    refine ⟨q, rfl, by simpa using hq, ?_⟩
    intro x hx
    subst hx
    cases a with
    | none => cases h
    | some p =>
      refine ⟨p, rfl, ?_⟩
      have := ok_inj h
      split at this
      · cases this
      · exact (Option.some.inj this).symm

/-- What a sound oracle's known bits say about the sign. -/
theorem nonneg_of_knownZero {ρ : Env} {o : Oracle} (ho : o.Sound ρ) {t : Term w} {x : BitVec w}
    (hx : t.denote ρ = some x) (hk : (o.knownZero t).msb = true) : x.msb = false :=
  Lemmas.msb_false_of_and_eq_zero (ho.knownZero t x hx) hk

theorem neg_of_knownOne {ρ : Env} {o : Oracle} (ho : o.Sound ρ) {t : Term w} {x : BitVec w}
    (hx : t.denote ρ = some x) (hk : (o.knownOne t).msb = true) : x.msb = true :=
  Lemmas.msb_true_of_and_eq (ho.knownOne t x hx) hk

end Peephole.IS.ICmpB
