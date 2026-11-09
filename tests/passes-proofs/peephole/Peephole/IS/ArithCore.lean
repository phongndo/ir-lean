import Peephole.Match
import Peephole.Oracle
import Peephole.Fold
import Peephole.IS.Add
import Peephole.IS.ArithBase
import Peephole.Lemmas.Add
import Peephole.Lemmas.Arith
import IRLean.Generic.Arith
import IRLean.Generic.Bitwise

/-! # What the models of InstSimplify's arithmetic folds share

`simplifySubInst`, `simplifyMulInst` and the divisions call InstSimplify again, on operands they build from their own:
`simplifyBinOp` and `simplifyICmpInst`, with a smaller `MaxRecurse`. A model here takes those calls as a parameter,
`Recur`, and a theorem about it holds for every `Recur` that's `Recur.Sound` in the run: whatever value it answers
refines the operation it was asked about. `Recur.unknown`, which answers that the model doesn't say, is sound, and is
what `onInst` runs with, so the comparison with `opt` never takes an answer the model didn't compute.

`simplifyByDomEq` asks `isImpliedByDomCondition`, which `Peephole.Oracle` doesn't have. `DomOracle` is it, with its
own `Sound`; `DomOracle.none` knows nothing, and is what `onInst` runs with.

A fold that forwards to another fold modelled here, as `if (Value *V = g(...)) return V;` does, has the step
`forward (g.steps ...)`: it fires what `g` fires, under `g`'s site, so a rewrite keeps its own ID. A step that returns
what a recursive call answered fires under the callee's name, `"simplifyBinOp"`, since the inventory counts such a
return as a forward, not a site. -/

namespace Peephole.IS.Arith

open IRLean

variable {w : Nat}

/-- `RecursionLimit` in `InstructionSimplify.cpp`: the `MaxRecurse` an instruction starts with. -/
def recursionLimit : Nat := 3

/-! ### Recursive calls -/

/-- What a recursive call answers: a value, `nullptr`, or what the model doesn't say. InstSimplify builds no
instruction, so a value it answers is one that exists, or a constant: a `Term`. -/
inductive Ans (w : Nat) where
  | val (t : Term w)
  | null
  | unknown

/-- The recursive calls into InstSimplify a fold makes, with their `MaxRecurse` first. -/
structure Recur where
  /-- `simplifyBinOp(Opcode, LHS, RHS, Q, MaxRecurse)`, which runs the opcode's fold with no flags. -/
  binOp : Nat → {w : Nat} → BinOp → Term w → Term w → Ans w
  /-- `simplifyICmpInst(Pred, LHS, RHS, Q, MaxRecurse)`. -/
  icmp : Nat → {w : Nat} → Pred → Term w → Term w → Ans 1

/-- Every value a `Recur` answers is right in the run `ρ`: for operands consistent with it and with no `undef`, the
answer is consistent too, has no `undef`, and refines the operation, which has no flags. -/
structure Recur.Sound (r : Recur) (ρ : Env) : Prop where
  binOp : ∀ (n : Nat) {w : Nat} (op : BinOp) (a b t : Term w), r.binOp n op a b = .val t →
    a.Consistent ρ → b.Consistent ρ → a.hasUndef = false → b.hasUndef = false →
    t.Consistent ρ ∧ t.hasUndef = false ∧ Refines (op.eval {} (a.denote ρ) (b.denote ρ)) (Outcome.ok (t.denote ρ))
  icmp : ∀ (n : Nat) {w : Nat} (p : Pred) (a b : Term w) (t : Term 1), r.icmp n p a b = .val t →
    a.Consistent ρ → b.Consistent ρ → a.hasUndef = false → b.hasUndef = false →
    Refines (p.eval (a.denote ρ) (b.denote ρ) false) (t.denote ρ)

/-- The calls the model doesn't say anything about. -/
def Recur.unknown : Recur where
  binOp _ _ _ _ _ := .unknown
  icmp _ _ _ _ _ := .unknown

theorem Recur.unknown_sound (ρ : Env) : Recur.unknown.Sound ρ where
  binOp _ _ _ _ _ _ h := by simp [Recur.unknown] at h
  icmp _ _ _ _ _ _ h := by simp [Recur.unknown] at h

/-- A step on what `callee` answered: `k` on a value, `onNull` on `nullptr`, delegated where the model doesn't say. -/
def Ans.bind {w v : Nat} (callee : String) (a : Ans w) (onNull : Step v) (k : Term w → Step v) : Step v :=
  match a with
  | .val t => k t
  | .null => onNull
  | .unknown => .delegate callee

theorem Ans.bind_fire {w v : Nat} {callee : String} {a : Ans w} {onNull : Step v} {k : Term w → Step v}
    {s : String} {r : Repl v} (h : a.bind callee onNull k = .fire s r) :
    (a = .null ∧ onNull = .fire s r) ∨ ∃ t, a = .val t ∧ k t = .fire s r := by
  cases a with
  | val t => exact .inr ⟨t, rfl, h⟩
  | null => exact .inl ⟨rfl, h⟩
  | unknown => simp [Ans.bind] at h

/-! ### Dominating conditions -/

/-- `isImpliedByDomCondition(Pred, LHS, RHS, CxtI, DL)`: whether a condition that dominates the instruction implies
`LHS pred RHS` is true (`some true`) or false (`some false`). -/
structure DomOracle where
  implied : {w : Nat} → Pred → Term w → Term w → Option Bool

/-- Each answer is true in the run, for operands that aren't poison, as `Oracle.Sound`'s are. -/
structure DomOracle.Sound (d : DomOracle) (ρ : Env) : Prop where
  implied : ∀ {w : Nat} (p : Pred) (a b : Term w) (r : Bool) (x y : BitVec w), d.implied p a b = some r →
    a.denote ρ = some x → b.denote ρ = some y → p.eval (some x) (some y) false = some (BitVec.ofBool r)

/-- No dominating condition known. -/
def DomOracle.none : DomOracle where
  implied _ _ _ := Option.none

theorem DomOracle.none_sound (ρ : Env) : DomOracle.none.Sound ρ where
  implied _ _ _ _ _ _ h := by simp [DomOracle.none] at h

/-- A dominating condition implying `a == b` makes their values equal. -/
theorem DomOracle.Sound.eq {d : DomOracle} {ρ : Env} (hd : d.Sound ρ) {a b : Term w} {x y : BitVec w}
    (h : d.implied .eq a b = some true) (ha : a.denote ρ = some x) (hb : b.denote ρ = some y) : x = y := by
  have := hd.implied .eq a b true x y h ha hb
  simp only [Pred.eval, Val.icmpEq, Val.icmp, Bool.false_and, Bool.false_eq_true, ite_false, Option.some.injEq]
    at this
  have h1 := congrArg BitVec.toNat this
  revert h1
  cases hxy : (x == y) <;> simp_all

/-! ### Forwarding to a fold modelled here -/

/-- `if (Value *V = g(...)) return V;`, as one step: what `g`'s first step that doesn't fall through does, with a
decline falling through instead. -/
def forward : List (Step w) → Step w
  | [] => .next
  | .next :: rest => forward rest
  | .fire s r :: _ => .fire s r
  | .decline :: _ => .next
  | .delegate c :: _ => .delegate c

theorem forward_fire {steps : List (Step w)} {s : String} {r : Repl w} (h : forward steps = .fire s r) :
    Step.fire s r ∈ steps := by
  induction steps with
  | nil => simp [forward] at h
  | cons st rest ih =>
    cases st with
    | next => exact List.mem_cons_of_mem _ (ih h)
    | fire s' r' =>
      simp only [forward, Step.fire.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact List.mem_cons_self
    | decline => simp [forward] at h
    | delegate c => simp [forward] at h

/-! ### Operators -/

/-- The source a binary fold replaces: `op` with its flags, on operands that exist. -/
def binSrc (op : BinOp) (f : Flags) (a b : Term w) : Repl w := .bin op f (.old a) (.old b)

@[simp] theorem binSrc_eval (ρ : Env) (op : BinOp) (f : Flags) (a b : Term w) :
    (binSrc op f a b).eval ρ = op.eval f (a.denote ρ) (b.denote ρ) := rfl

/-- `Instruction::isAssociative` on an integer opcode. -/
def isAssociative : BinOp → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

/-- `Instruction::isCommutative` on an integer opcode. -/
def isCommutative : BinOp → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

/-- `Operator::hasPoisonGeneratingFlags` on a binary operator. -/
def poisonFlags : BinOp → Flags → Bool
  | .add, f | .sub, f | .mul, f | .shl, f => f.nuw || f.nsw
  | .udiv, f | .sdiv, f | .lshr, f | .ashr, f => f.exact
  | .or, f => f.disjoint
  | _, _ => false

/-- An operator with no flag that makes poison is the operator with no flags. -/
theorem eval_of_poisonFlags {op : BinOp} {f : Flags} (h : poisonFlags op f = false) (a b : Val w) :
    op.eval f a b = op.eval {} a b := by
  cases op <;> simp_all [poisonFlags, BinOp.eval]

/-- A poison left operand: the result is poison, or the run is undefined. -/
theorem eval_none_left (op : BinOp) (f : Flags) (b : Val w) (r : Val w) :
    Refines (op.eval f none b) (Outcome.ok r) := by
  cases op with
  | udiv => exact udiv_none_left b f.exact r
  | sdiv => exact sdiv_none_left b f.exact r
  | urem => exact urem_none_left b r
  | srem => exact srem_none_left b r
  | _ => exact ok_none_refines _

/-- A poison right operand: the result is poison, or the run is undefined. -/
theorem eval_none_right (op : BinOp) (f : Flags) (a : Val w) (r : Val w) :
    Refines (op.eval f a none) (Outcome.ok r) := by
  cases op with
  | udiv => exact udiv_none_right a f.exact r
  | sdiv => exact sdiv_none_right a f.exact r
  | urem => exact urem_none_right a r
  | srem => exact srem_none_right a r
  | _ => cases a <;> exact ok_none_refines _

private theorem ok_drop {a b : Val w} (h : a = none ∨ b = a) : Refines (Outcome.ok a) (Outcome.ok b) :=
  (Refine.outcome_ok_ok _ _).2 ((Refine.val_iff a b).2 h)

private theorem udiv_drop (a b : Val w) (exact : Bool) : Refines (Val.udiv a b exact) (Val.udiv a b false) := by
  cases b with
  | none => exact Refine.outcome_ub _ _
  | some y =>
    by_cases hy : y = 0#w
    · subst hy; simp only [Val.udiv, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _
    · cases a with
      | none => simp only [Val.udiv, beq_iff_eq, hy, ite_false]; exact ok_none_refines _
      | some x =>
        simp only [Val.udiv, beq_iff_eq, hy, ite_false, Bool.false_and, Bool.false_eq_true]
        exact ok_drop (by split <;> simp)

private theorem sdiv_drop (a b : Val w) (exact : Bool) : Refines (Val.sdiv a b exact) (Val.sdiv a b false) := by
  cases b with
  | none => exact Refine.outcome_ub _ _
  | some y =>
    by_cases hy : y = 0#w
    · subst hy; simp only [Val.sdiv, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _
    · have h0 : (y == 0#w) = false := by simpa using hy
      by_cases ho : Val.divOverflows a y = true
      · simp only [Val.sdiv, h0, ho, Bool.false_eq_true, ite_false, ite_true]; exact Refine.outcome_ub _ _
      · simp only [Bool.not_eq_true] at ho
        cases a with
        | none => simp only [Val.sdiv, h0, ho, Bool.false_eq_true, ite_false]; exact ok_none_refines _
        | some x =>
          simp only [Val.sdiv, h0, ho, Bool.false_eq_true, ite_false, Bool.false_and]
          exact ok_drop (by split <;> simp)

private theorem urem_drop (a b : Val w) : Refines (Val.urem a b) (Val.urem a b) := by
  cases b with
  | none => exact Refine.outcome_ub _ _
  | some y =>
    by_cases hy : y = 0#w
    · subst hy; simp only [Val.urem, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _
    · cases a with
      | none => simp only [Val.urem, beq_iff_eq, hy, ite_false]; exact ok_none_refines _
      | some x => simp only [Val.urem, beq_iff_eq, hy, ite_false]; exact ok_refl _

private theorem srem_drop (a b : Val w) : Refines (Val.srem a b) (Val.srem a b) := by
  cases b with
  | none => exact Refine.outcome_ub _ _
  | some y =>
    by_cases hy : y = 0#w
    · subst hy; simp only [Val.srem, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _
    · have h0 : (y == 0#w) = false := by simpa using hy
      by_cases ho : Val.divOverflows a y = true
      · simp only [Val.srem, h0, ho, Bool.false_eq_true, ite_false, ite_true]; exact Refine.outcome_ub _ _
      · simp only [Bool.not_eq_true] at ho
        cases a with
        | none => simp only [Val.srem, h0, ho, Bool.false_eq_true, ite_false]; exact ok_none_refines _
        | some x => simp only [Val.srem, h0, ho, Bool.false_eq_true, ite_false]; exact ok_refl _

/-- Dropping an operator's flags only removes poison. -/
theorem eval_drop_flags (op : BinOp) (f : Flags) (a b : Val w) : Refines (op.eval f a b) (op.eval {} a b) := by
  cases op with
  | udiv => exact udiv_drop a b f.exact
  | sdiv => exact sdiv_drop a b f.exact
  | urem => exact urem_drop a b
  | srem => exact srem_drop a b
  | add =>
    refine ok_drop ?_
    cases a <;> cases b <;> simp only [Val.add, Bool.false_and, Bool.or_false, Bool.false_eq_true, ite_false] <;>
      first | (simp; done) | (split <;> simp)
  | sub =>
    refine ok_drop ?_
    cases a <;> cases b <;> simp only [Val.sub, Bool.false_and, Bool.or_false, Bool.false_eq_true, ite_false] <;>
      first | (simp; done) | (split <;> simp)
  | mul =>
    refine ok_drop ?_
    cases a <;> cases b <;> simp only [Val.mul, Bool.false_and, Bool.or_false, Bool.false_eq_true, ite_false] <;>
      first | (simp; done) | (split <;> simp)
  | shl =>
    refine ok_drop ?_
    cases a <;> cases b <;> simp only [Val.shl, Bool.false_and, Bool.false_eq_true, ite_false] <;>
      first | (simp; done) | (split <;> first | (simp; done) | (split <;> first | (simp; done) | (split <;> simp)))
  | lshr =>
    refine ok_drop ?_
    cases a <;> cases b <;> simp only [Val.lshr, Bool.false_and, Bool.false_eq_true, ite_false] <;>
      first | (simp; done) | (split <;> first | (simp; done) | (split <;> simp))
  | ashr =>
    refine ok_drop ?_
    cases a <;> cases b <;> simp only [Val.ashr, Bool.false_and, Bool.false_eq_true, ite_false] <;>
      first | (simp; done) | (split <;> first | (simp; done) | (split <;> simp))
  | or =>
    refine ok_drop ?_
    cases a <;> cases b <;> simp only [Val.or, Bool.false_and, Bool.false_eq_true, ite_false] <;>
      first | (simp; done) | (split <;> simp)
  | and => exact ok_refl _
  | xor => exact ok_refl _

/-- A run that refines another, before one that refines a value, refines the value. -/
theorem refines_trans_ok {o o' : Outcome (Val w)} {v : Val w} (h : Refines o o') (h' : Refines o' (Outcome.ok v)) :
    Refines o (Outcome.ok v) :=
  Refines.trans h h'

/-- What a refinement of a value that isn't poison says. -/
theorem eq_of_refines_some {x : BitVec w} {b : Val w} (h : Refines (Outcome.ok (some x)) (Outcome.ok b)) :
    b = some x :=
  (Refine.val_some x b).1 ((Refine.outcome_ok_ok _ _).1 h)

/-! ### Associative and commutative operators -/

/-- What an associative and commutative operator computes on two values. -/
def raw : BinOp → BitVec w → BitVec w → BitVec w
  | .add, x, y => x + y
  | .mul, x, y => x * y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | _, x, _ => x

theorem raw_assoc {op : BinOp} (h : isAssociative op = true) (x y z : BitVec w) :
    raw op (raw op x y) z = raw op x (raw op y z) := by
  cases op <;> simp_all [isAssociative, raw, BitVec.add_assoc, BitVec.mul_assoc, BitVec.and_assoc, BitVec.or_assoc,
    BitVec.xor_assoc]

theorem raw_comm {op : BinOp} (h : isCommutative op = true) (x y : BitVec w) : raw op x y = raw op y x := by
  cases op <;> simp_all [isCommutative, raw, BitVec.add_comm, BitVec.mul_comm, BitVec.and_comm, BitVec.or_comm,
    BitVec.xor_comm]

theorem isAssociative_of_isCommutative {op : BinOp} (h : isCommutative op = true) : isAssociative op = true := by
  cases op <;> simp_all [isCommutative, isAssociative]

/-- Every associative integer opcode is commutative too. -/
theorem isCommutative_of_isAssociative {op : BinOp} (h : isAssociative op = true) : isCommutative op = true := by
  cases op <;> simp_all [isCommutative, isAssociative]

/-- With no flags, an associative operator on two values is a value. -/
theorem eval_assoc_plain {op : BinOp} (h : isAssociative op = true) (x y : BitVec w) :
    op.eval {} (some x) (some y) = Outcome.ok (some (raw op x y)) := by
  cases op <;> simp_all [isAssociative, raw, BinOp.eval, Val.add, Val.mul, Val.and, Val.or, Val.xor, Val.map₂]

/-- An associative operator that gave a value had values for operands, and gave what `raw` does. -/
theorem eval_assoc_some {op : BinOp} (h : isAssociative op = true) {f : Flags} {a b : Val w} {l : BitVec w}
    (hv : op.eval f a b = Outcome.ok (some l)) : ∃ x y, a = some x ∧ b = some y ∧ l = raw op x y := by
  cases a with
  | none => cases op <;> simp_all [isAssociative, BinOp.eval, Val.add, Val.mul, Val.and, Val.or, Val.xor, Val.map₂,
      Outcome.ok]
  | some x =>
  cases b with
  | none => cases op <;> simp_all [isAssociative, BinOp.eval, Val.add, Val.mul, Val.and, Val.or, Val.xor, Val.map₂,
      Outcome.ok]
  | some y =>
    refine ⟨x, y, rfl, rfl, ?_⟩
    cases op <;> simp_all [isAssociative, BinOp.eval, Val.add, Val.mul, Val.and, Val.or, Val.xor, Val.map₂,
      Outcome.ok, raw] <;> (split at hv <;> simp_all)

/-- An associative operator, with any flags, refines a value that's what `raw` gives wherever its operands are
values. -/
theorem eval_assoc_refines {op : BinOp} (h : isAssociative op = true) (f : Flags) {a b t : Val w}
    (ht : ∀ x y, a = some x → b = some y → t = some (raw op x y)) : Refines (op.eval f a b) (Outcome.ok t) := by
  cases a with
  | none => exact eval_none_left op f b t
  | some x =>
  cases b with
  | none => exact eval_none_right op f (some x) t
  | some y =>
    rw [ht x y rfl rfl]
    refine Refines.trans (eval_drop_flags op f _ _) ?_
    rw [eval_assoc_plain h]
    exact ok_refl _

/-- A commutative operator, with any flags, doesn't mind the order of its operands. -/
theorem eval_comm {op : BinOp} (h : isCommutative op = true) (f : Flags) (a b : Val w) :
    op.eval f a b = op.eval f b a := by
  cases op <;> simp only [isCommutative, Bool.false_eq_true] at h <;> simp only [BinOp.eval]
  · rw [Lemmas.add_comm]
  · rw [Lemmas.mul_comm]
  · cases a <;> cases b <;> simp [Val.and, Val.map₂, BitVec.and_comm]
  · cases a <;> cases b <;> simp only [Val.or, BitVec.and_comm, BitVec.or_comm]
  · cases a <;> cases b <;> simp [Val.xor, Val.map₂, BitVec.xor_comm]

/-- `op` distributes over `opex` from the right, for the pairs `expandCommutativeBinOp` is called with: `mul` over
`add`, `and` over `or` and `xor`, and `or` over `and`. -/
def distributes : BinOp → BinOp → Bool
  | .mul, .add | .and, .or | .and, .xor | .or, .and => true
  | _, _ => false

theorem raw_distrib {op opex : BinOp} (h : distributes op opex = true) (x y z : BitVec w) :
    raw op (raw opex x y) z = raw opex (raw op x z) (raw op y z) := by
  cases op <;> cases opex <;> simp only [distributes, Bool.false_eq_true] at h <;> simp only [raw]
  · exact BitVec.add_mul
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]; cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_xor]; cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]; cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem isAssociative_of_distributes_left {op opex : BinOp} (h : distributes op opex = true) :
    isAssociative op = true := by
  cases op <;> cases opex <;> simp_all [distributes, isAssociative]

theorem isCommutative_of_distributes_right {op opex : BinOp} (h : distributes op opex = true) :
    isCommutative opex = true := by
  cases op <;> cases opex <;> simp_all [distributes, isCommutative]

theorem isCommutative_of_distributes_left {op opex : BinOp} (h : distributes op opex = true) :
    isCommutative op = true := by
  cases op <;> cases opex <;> simp_all [distributes, isCommutative]

/-- A `select`'s value is poison, or one of its arms'. -/
theorem select_cases (c : Val 1) (t e : Val w) :
    IRLean.select c t e = none ∨ IRLean.select c t e = t ∨ IRLean.select c t e = e := by
  cases c with
  | none => exact .inl rfl
  | some b =>
    simp only [IRLean.select]
    split
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)

/-! ### Operands -/

/-- `isa<SelectInst>(V)`. -/
def isSelect : Term w → Bool
  | .select .. => true
  | _ => false

/-- Whether `isa<PHINode>(V)` may hold: a phi is an operand the model doesn't look into, as an argument is. -/
def mayBePhi : Term w → Bool
  | .var _ => true
  | _ => false

/-- An instruction's value, where it's a binary operator matched with `binop?`, as its operation on its operands'. -/
theorem binop?_eval {ρ : Env} {t a b : Term w} {op : BinOp} {f : Flags} (h : binop? op t = some (f, a, b))
    (hc : t.Consistent ρ) : op.eval f (a.denote ρ) (b.denote ρ) = Outcome.ok (t.denote ρ) :=
  (binop?_consistent h hc).2.2

end Peephole.IS.Arith
