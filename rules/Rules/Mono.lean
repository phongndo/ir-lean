import IRLean.Int
import IRLean.Lemmas
import IRLean.Refine

/-! # What a rule's proof and a certificate are built from

A rule says a replacement refines a pattern, about values: `Refines (Outcome.ok lhs) (Outcome.ok rhs)`, as
`Rules/Statements.lean` states each. A certificate says one whole function refines another, where the two differ by one
application of a rule. Between the two is congruence: an instruction given operands that refine gives a result that
refines, since every integer instruction gives poison for a poison operand, and poison allows anything. `Mono` has that
lemma for each instruction a certificate can pass through.

A certificate's proof is one term: `le_of_ret`, then a `Mono` lemma for each instruction on the way from the function's
result down to the rewritten one, `Refine.refl_val` for each operand the rewrite left alone, and the rule's theorem, as
`val`, at the rewritten instruction. `tools/rules/rules.py` writes it. Nothing here is trusted: the kernel checks each
certificate, and `docs/rules.md` says what a certificate claims. -/

namespace Rules

open IRLean

variable {w v u : Nat}

/-! ### Between a rule's statement and values -/

/-- A value that refines, as a run that returns it: what a rule's proof gives from a lemma about values. -/
theorem ok {a b : Val w} (h : Refines a b) : Refines (Outcome.ok a) (Outcome.ok b) :=
  (Refine.outcome_ok_ok a b).2 h

/-- A rule's statement, read as a fact about values: what a certificate uses at the rewritten instruction. -/
theorem val {a b : Val w} (h : Refines (Outcome.ok a) (Outcome.ok b)) : Refine.le a b :=
  (Refine.outcome_ok_ok a b).1 h

/-- Closes a hypothesis a lemma leaves: one of the statement's, a constant the lemma names and the rule writes out, or
a cast's `w ≤ m` from the statement's `w < m`. -/
macro "rule_side" : tactic =>
  `(tactic| first | assumption | rfl | exact Nat.le_of_lt (by assumption))

/-- A rule from a lemma about values, or about a division: the lemma's conclusion is the statement's, and its
hypotheses are the statement's side conditions. The first `intro` unfolds the statement's definition. -/
macro "rule_from " l:term : tactic =>
  `(tactic| (intro; intros; first | (refine Rules.ok ?_; apply $l <;> rule_side) | (apply $l <;> rule_side)))

/-- A rule from an equation of two values, or of a division and what it returns: equal values refine each other. -/
macro "rule_from_eq " l:term : tactic =>
  `(tactic| (intro; intros; first
    | (refine Rules.ok (Refines.of_eq ?_ (Refines.refl _)); apply $l <;> rule_side)
    | (rw [$l:term] <;> first | exact Rules.ok (Refines.refl _) | rule_side)))

/-! ### From a function to its result -/

/-- Two functions of one block each, which return `r` and `r'`: the second refines the first if `r'` refines `r`. -/
theorem le_of_ret {β β' ρ : Type} [Refine ρ] {step : β → Outcome (Next β ρ)} {step' : β' → Outcome (Next β' ρ)}
    {b : β} {b' : β'} {r r' : ρ} (hs : step b = ret r) (ht : step' b' = ret r') (h : Refine.le r r') :
    Refine.le (run step b) (run step' b') := by
  rw [run_ret step hs, run_ret step' ht]
  exact (Refine.outcome_ok_ok r r').2 h

/-- `noundef` on the same argument of both: undefined for poison on both sides, and otherwise what follows. -/
theorem noundef_mono {τ α : Type} [Refine α] {x : Option τ} {k k' : Outcome α} (h : Refine.le k k') :
    Refine.le (noundef x k) (noundef x k') := by
  cases x with
  | none => trivial
  | some _ => exact h

/-! ### Congruence, one lemma an instruction -/

namespace Mono

/-- An instruction of two operands that gives poison for a poison operand. -/
theorem strict₂ (f : Val w → Val u → Val v) (hl : ∀ b, f none b = none) (hr : ∀ a, f a none = none)
    {a a' : Val w} {b b' : Val u} (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (f a b) (f a' b') :=
  Refine.val_map₂_mono hl hr ha hb

/-- An instruction of one operand that gives poison for poison. -/
theorem strict₁ (f : Val w → Val v) (hf : f none = none) {a a' : Val w} (ha : Refine.le a a') :
    Refine.le (f a) (f a') :=
  Refine.val_map_mono hf ha

variable {a a' b b' c c' : Val w}

theorem add {nuw nsw : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.add a b nuw nsw) (Val.add a' b' nuw nsw) :=
  strict₂ (fun a b => Val.add a b nuw nsw) (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb

theorem sub {nuw nsw : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.sub a b nuw nsw) (Val.sub a' b' nuw nsw) :=
  strict₂ (fun a b => Val.sub a b nuw nsw) (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb

theorem mul {nuw nsw : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.mul a b nuw nsw) (Val.mul a' b' nuw nsw) :=
  strict₂ (fun a b => Val.mul a b nuw nsw) (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb

theorem shl {nuw nsw : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.shl a b nuw nsw) (Val.shl a' b' nuw nsw) :=
  strict₂ (fun a b => Val.shl a b nuw nsw) (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb

theorem lshr {exact : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.lshr a b exact) (Val.lshr a' b' exact) :=
  strict₂ (fun a b => Val.lshr a b exact) (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb

theorem ashr {exact : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.ashr a b exact) (Val.ashr a' b' exact) :=
  strict₂ (fun a b => Val.ashr a b exact) (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb

theorem and (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.and a b) (Val.and a' b') :=
  strict₂ Val.and (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb

theorem or {disjoint : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.or a b disjoint) (Val.or a' b' disjoint) :=
  strict₂ (fun a b => Val.or a b disjoint) (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb

theorem xor (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.xor a b) (Val.xor a' b') :=
  strict₂ Val.xor (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb

/-- Any `icmp`: each predicate is `Val.icmp` of its comparison. -/
theorem icmp (p : BitVec w → BitVec w → Bool) {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmp p a b s) (Val.icmp p a' b' s) :=
  strict₂ (fun a b => Val.icmp p a b s) (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb

theorem icmpEq {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpEq a b s) (Val.icmpEq a' b' s) := icmp _ ha hb
theorem icmpNe {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpNe a b s) (Val.icmpNe a' b' s) := icmp _ ha hb
theorem icmpUlt {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpUlt a b s) (Val.icmpUlt a' b' s) := icmp _ ha hb
theorem icmpUle {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpUle a b s) (Val.icmpUle a' b' s) := icmp _ ha hb
theorem icmpUgt {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpUgt a b s) (Val.icmpUgt a' b' s) := icmp _ ha hb
theorem icmpUge {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpUge a b s) (Val.icmpUge a' b' s) := icmp _ ha hb
theorem icmpSlt {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpSlt a b s) (Val.icmpSlt a' b' s) := icmp _ ha hb
theorem icmpSle {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpSle a b s) (Val.icmpSle a' b' s) := icmp _ ha hb
theorem icmpSgt {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpSgt a b s) (Val.icmpSgt a' b' s) := icmp _ ha hb
theorem icmpSge {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpSge a b s) (Val.icmpSge a' b' s) := icmp _ ha hb

/-- `select`: poison for a poison condition, and otherwise the arm the condition picks, which is the same arm on both
sides, since a condition that isn't poison only allows itself. -/
theorem select {p p' : Val 1} (hp : Refine.le p p') (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.select p a b) (IRLean.select p' a' b') := by
  cases p with
  | none => trivial
  | some x =>
    cases hp
    simp only [IRLean.select]
    split <;> assumption

theorem zext {x x' : Val v} {nneg : Bool} (hx : Refine.le x x') :
    Refine.le (Val.zext w x nneg) (Val.zext w x' nneg) :=
  strict₁ (fun x => Val.zext w x nneg) rfl hx

theorem sext {x x' : Val v} (hx : Refine.le x x') : Refine.le (Val.sext w x) (Val.sext w x') :=
  strict₁ (Val.sext w) rfl hx

theorem trunc {x x' : Val v} {nuw nsw : Bool} (hx : Refine.le x x') :
    Refine.le (Val.trunc w x nuw nsw) (Val.trunc w x' nuw nsw) :=
  strict₁ (fun x => Val.trunc w x nuw nsw) rfl hx

theorem umin (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.umin a b) (Val.umin a' b') :=
  strict₂ Val.umin (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb
theorem umax (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.umax a b) (Val.umax a' b') :=
  strict₂ Val.umax (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb
theorem smin (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.smin a b) (Val.smin a' b') :=
  strict₂ Val.smin (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb
theorem smax (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.smax a b) (Val.smax a' b') :=
  strict₂ Val.smax (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb
theorem uaddSat (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.uaddSat a b) (Val.uaddSat a' b') :=
  strict₂ Val.uaddSat (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb
theorem usubSat (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.usubSat a b) (Val.usubSat a' b') :=
  strict₂ Val.usubSat (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb
theorem saddSat (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.saddSat a b) (Val.saddSat a' b') :=
  strict₂ Val.saddSat (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb
theorem ssubSat (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.ssubSat a b) (Val.ssubSat a' b') :=
  strict₂ Val.ssubSat (fun _ => rfl) (fun a => by cases a <;> rfl) ha hb

theorem ctpop (ha : Refine.le a a') : Refine.le (Val.ctpop a) (Val.ctpop a') := strict₁ Val.ctpop rfl ha
theorem bitreverse (ha : Refine.le a a') : Refine.le (Val.bitreverse a) (Val.bitreverse a') :=
  strict₁ Val.bitreverse rfl ha
theorem bswap (ha : Refine.le a a') : Refine.le (Val.bswap a) (Val.bswap a') := strict₁ Val.bswap rfl ha
theorem ctlz {z : Bool} (ha : Refine.le a a') : Refine.le (Val.ctlz a z) (Val.ctlz a' z) :=
  strict₁ (fun a => Val.ctlz a z) rfl ha
theorem cttz {z : Bool} (ha : Refine.le a a') : Refine.le (Val.cttz a z) (Val.cttz a' z) :=
  strict₁ (fun a => Val.cttz a z) rfl ha
theorem abs {z : Bool} (ha : Refine.le a a') : Refine.le (Val.abs a z) (Val.abs a' z) :=
  strict₁ (fun a => Val.abs a z) rfl ha

theorem fshl (ha : Refine.le a a') (hb : Refine.le b b') (hc : Refine.le c c') :
    Refine.le (Val.fshl a b c) (Val.fshl a' b' c') := by
  cases a with
  | none => trivial
  | some x =>
    cases ha
    cases b with
    | none => trivial
    | some y =>
      cases hb
      cases c with
      | none => trivial
      | some z => cases hc; exact Refine.refl_val _

theorem fshr (ha : Refine.le a a') (hb : Refine.le b b') (hc : Refine.le c c') :
    Refine.le (Val.fshr a b c) (Val.fshr a' b' c') := by
  cases a with
  | none => trivial
  | some x =>
    cases ha
    cases b with
    | none => trivial
    | some y =>
      cases hb
      cases c with
      | none => trivial
      | some z => cases hc; exact Refine.refl_val _

end Mono

end Rules
