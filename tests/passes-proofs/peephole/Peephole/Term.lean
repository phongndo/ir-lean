import IRLean.Int
import IRLean.Refine

/-! # What a fold sees, and what it builds

A fold in InstSimplify or InstCombine looks at an instruction's operands through LLVM's matchers, and either declines
or answers with a replacement. This file gives both sides a shape a Lean model can follow, for scalar integers:

- `Term w` is an operand of type `iw`, as far as a matcher can see into it. Each instruction in it carries an `id`, which
  stands for its address, so `m_Specific` compares identities, not trees, as the C++ does.
- `Repl w` is what a fold answers with: an operand that already exists, a constant, or new instructions built on them.

A run gives every argument and instruction a value: `Env`. `Term.denote` reads an operand's value from it, and
`Term.Consistent` says each instruction's value is what its operation computes from its operands', so one `Value *` has
one value, as in SSA. `Repl.eval` runs a replacement, new instructions and all, on those values. A fold's rewrite is
right when the replacement refines the instruction it replaces, `IRLean.Refines`, for every `Env` its operands are
consistent with.

`undef` is here only so a model can follow a matcher that tests for it. IRLean has no `undef`, so theorems about folds
assume no operand reaches one (`Term.noUndef`), and say nothing about `undef`, as #47's theorem doesn't. -/

namespace Peephole

open IRLean

/-- LLVM's integer binary operators. -/
inductive BinOp where
  | add | sub | mul | udiv | sdiv | urem | srem | shl | lshr | ashr | and | or | xor
  deriving DecidableEq, Repr, Inhabited

/-- The predicates of `icmp`. -/
inductive Pred where
  | eq | ne | ugt | uge | ult | ule | sgt | sge | slt | sle
  deriving DecidableEq, Repr, Inhabited

/-- The flags a binary operator can carry. Each opcode reads only its own: `nuw` and `nsw` for `add`, `sub`, `mul` and
`shl`, `exact` for the divisions and right shifts, and `disjoint` for `or`. -/
structure Flags where
  nuw : Bool := false
  nsw : Bool := false
  exact : Bool := false
  disjoint : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Integer intrinsics of one operand, with their flag where they have one. -/
inductive UnIntr where
  | ctpop | bitreverse | bswap
  | ctlz (zeroPoison : Bool)
  | cttz (zeroPoison : Bool)
  | abs (intMinPoison : Bool)
  deriving DecidableEq, Repr

/-- Integer intrinsics of two operands of one type. -/
inductive BinIntr where
  | umin | umax | smin | smax | uaddSat | usubSat | saddSat | ssubSat
  deriving DecidableEq, Repr

/-- An operand of type `iw`, as far as a matcher sees into it. `id` stands for an instruction's address. -/
inductive Term : Nat → Type where
  /-- A `ConstantInt`. -/
  | const {w : Nat} (c : BitVec w) : Term w
  /-- The `PoisonValue` of the type. -/
  | poison {w : Nat} : Term w
  /-- The `UndefValue` of the type that isn't poison. -/
  | undef {w : Nat} : Term w
  /-- An argument, or an instruction no matcher here looks into. -/
  | var {w : Nat} (id : Nat) : Term w
  | bin {w : Nat} (id : Nat) (op : BinOp) (f : Flags) (a b : Term w) : Term w
  | icmp {w : Nat} (id : Nat) (p : Pred) (samesign : Bool) (a b : Term w) : Term 1
  | select {w : Nat} (id : Nat) (c : Term 1) (t e : Term w) : Term w
  | zext {v w : Nat} (id : Nat) (nneg : Bool) (a : Term v) : Term w
  | sext {v w : Nat} (id : Nat) (a : Term v) : Term w
  | trunc {v w : Nat} (id : Nat) (nuw nsw : Bool) (a : Term v) : Term w
  | freeze {w : Nat} (id : Nat) (a : Term w) : Term w
  | un {w : Nat} (id : Nat) (f : UnIntr) (a : Term w) : Term w
  | bi {w : Nat} (id : Nat) (f : BinIntr) (a b : Term w) : Term w
  /-- `fshl` if `left`, else `fshr`. -/
  | fsh {w : Nat} (id : Nat) (left : Bool) (a b c : Term w) : Term w

/-- Which `Value *` an operand is. LLVM keeps one `ConstantInt` per value and type, and one `PoisonValue` and one
`UndefValue` per type, so those are the same pointer exactly when they're the same constant. -/
inductive Ident where
  | const (w : Nat) (c : Nat)
  | poison (w : Nat)
  | undef (w : Nat)
  | node (id : Nat)
  deriving DecidableEq, Repr

variable {w v : Nat}

def Term.ident : {w : Nat} → Term w → Ident
  | w, .const c => .const w c.toNat
  | w, .poison => .poison w
  | w, .undef => .undef w
  | _, .var id | _, .bin id .. | _, .icmp id .. | _, .select id .. | _, .zext id .. | _, .sext id .. | _, .trunc id ..
  | _, .freeze id .. | _, .un id .. | _, .bi id .. | _, .fsh id .. => .node id

/-- `isa<Constant>`. -/
def Term.isConstant : {w : Nat} → Term w → Bool
  | _, .const _ | _, .poison | _, .undef => true
  | _, _ => false

/-- Whether an `undef` is anywhere in the operand. -/
def Term.hasUndef : {w : Nat} → Term w → Bool
  | _, .const _ | _, .poison | _, .var _ => false
  | _, .undef => true
  | _, .bin _ _ _ a b | _, .icmp _ _ _ a b | _, .bi _ _ a b => a.hasUndef || b.hasUndef
  | _, .select _ c t e => c.hasUndef || t.hasUndef || e.hasUndef
  | _, .zext _ _ a | _, .sext _ a | _, .trunc _ _ _ a | _, .freeze _ a | _, .un _ _ a => a.hasUndef
  | _, .fsh _ _ a b c => a.hasUndef || b.hasUndef || c.hasUndef

/-! ### Semantics -/

/-- What a run gives each argument and instruction: its value at each width. -/
abbrev Env := (w : Nat) → Nat → Val w

def BinOp.eval : BinOp → Flags → Val w → Val w → Outcome (Val w)
  | .add, f, a, b => Outcome.ok (Val.add a b f.nuw f.nsw)
  | .sub, f, a, b => Outcome.ok (Val.sub a b f.nuw f.nsw)
  | .mul, f, a, b => Outcome.ok (Val.mul a b f.nuw f.nsw)
  | .udiv, f, a, b => Val.udiv a b f.exact
  | .sdiv, f, a, b => Val.sdiv a b f.exact
  | .urem, _, a, b => Val.urem a b
  | .srem, _, a, b => Val.srem a b
  | .shl, f, a, b => Outcome.ok (Val.shl a b f.nuw f.nsw)
  | .lshr, f, a, b => Outcome.ok (Val.lshr a b f.exact)
  | .ashr, f, a, b => Outcome.ok (Val.ashr a b f.exact)
  | .and, _, a, b => Outcome.ok (Val.and a b)
  | .or, f, a, b => Outcome.ok (Val.or a b f.disjoint)
  | .xor, _, a, b => Outcome.ok (Val.xor a b)

def Pred.eval : Pred → Val w → Val w → Bool → Val 1
  | .eq, a, b, s => Val.icmpEq a b s
  | .ne, a, b, s => Val.icmpNe a b s
  | .ugt, a, b, s => Val.icmpUgt a b s
  | .uge, a, b, s => Val.icmpUge a b s
  | .ult, a, b, s => Val.icmpUlt a b s
  | .ule, a, b, s => Val.icmpUle a b s
  | .sgt, a, b, s => Val.icmpSgt a b s
  | .sge, a, b, s => Val.icmpSge a b s
  | .slt, a, b, s => Val.icmpSlt a b s
  | .sle, a, b, s => Val.icmpSle a b s

def UnIntr.eval : UnIntr → Val w → Val w
  | .ctpop, a => Val.ctpop a
  | .bitreverse, a => Val.bitreverse a
  | .bswap, a => Val.bswap a
  | .ctlz z, a => Val.ctlz a z
  | .cttz z, a => Val.cttz a z
  | .abs p, a => Val.abs a p

def BinIntr.eval : BinIntr → Val w → Val w → Val w
  | .umin, a, b => Val.umin a b
  | .umax, a, b => Val.umax a b
  | .smin, a, b => Val.smin a b
  | .smax, a, b => Val.smax a b
  | .uaddSat, a, b => Val.uaddSat a b
  | .usubSat, a, b => Val.usubSat a b
  | .saddSat, a, b => Val.saddSat a b
  | .ssubSat, a, b => Val.ssubSat a b

/-- An operand's value in a run. An instruction's is the run's, which `Consistent` ties to its operands. `undef` has no
single value: it reads as poison here, and theorems assume it isn't there. -/
def Term.denote (ρ : Env) : {w : Nat} → Term w → Val w
  | _, .const c => some c
  | _, .poison => none
  | _, .undef => none
  | w, .var id | w, .bin id .. | w, .select id .. | w, .zext id .. | w, .sext id .. | w, .trunc id ..
  | w, .freeze id .. | w, .un id .. | w, .bi id .. | w, .fsh id .. => ρ w id
  | _, .icmp id .. => ρ 1 id

/-- Each instruction's value is what its operation computes from its operands' values. An operand has already run, so
it wasn't undefined. A `freeze` of poison is some value, fixed for all its uses. -/
def Term.Consistent (ρ : Env) : {w : Nat} → Term w → Prop
  | _, .const _ | _, .poison | _, .undef | _, .var _ => True
  | w, .bin id op f a b =>
    a.Consistent ρ ∧ b.Consistent ρ ∧ op.eval f (a.denote ρ) (b.denote ρ) = Outcome.ok (ρ w id)
  | _, .icmp id p s a b => a.Consistent ρ ∧ b.Consistent ρ ∧ p.eval (a.denote ρ) (b.denote ρ) s = ρ 1 id
  | w, .select id c t e =>
    c.Consistent ρ ∧ t.Consistent ρ ∧ e.Consistent ρ ∧ IRLean.select (c.denote ρ) (t.denote ρ) (e.denote ρ) = ρ w id
  | w, .zext id nneg a => a.Consistent ρ ∧ Val.zext w (a.denote ρ) nneg = ρ w id
  | w, .sext id a => a.Consistent ρ ∧ Val.sext w (a.denote ρ) = ρ w id
  | w, .trunc id nuw nsw a => a.Consistent ρ ∧ Val.trunc w (a.denote ρ) nuw nsw = ρ w id
  | w, .freeze id a => a.Consistent ρ ∧ ∃ pick, Val.freeze pick (a.denote ρ) = ρ w id
  | w, .un id f a => a.Consistent ρ ∧ f.eval (a.denote ρ) = ρ w id
  | w, .bi id f a b => a.Consistent ρ ∧ b.Consistent ρ ∧ f.eval (a.denote ρ) (b.denote ρ) = ρ w id
  | w, .fsh id l a b c =>
    a.Consistent ρ ∧ b.Consistent ρ ∧ c.Consistent ρ ∧
      (if l then Val.fshl else Val.fshr) (a.denote ρ) (b.denote ρ) (c.denote ρ) = ρ w id

/-- Two operands that are the same `Value *` have the same value. -/
theorem Term.denote_of_ident {ρ : Env} {s t : Term w} (h : t.ident = s.ident) : t.denote ρ = s.denote ρ := by
  cases s <;> cases t <;> simp_all [Term.ident, Term.denote, BitVec.toNat_inj]

/-! ### Replacements -/

/-- What a fold answers with: an operand that exists, or new instructions, built on operands that exist. -/
inductive Repl : Nat → Type where
  | old {w : Nat} (t : Term w) : Repl w
  | const {w : Nat} (c : BitVec w) : Repl w
  | poison {w : Nat} : Repl w
  | bin {w : Nat} (op : BinOp) (f : Flags) (a b : Repl w) : Repl w
  | icmp {w : Nat} (p : Pred) (samesign : Bool) (a b : Repl w) : Repl 1
  | select {w : Nat} (c : Repl 1) (t e : Repl w) : Repl w
  | zext {v w : Nat} (nneg : Bool) (a : Repl v) : Repl w
  | sext {v w : Nat} (a : Repl v) : Repl w
  | trunc {v w : Nat} (nuw nsw : Bool) (a : Repl v) : Repl w
  | un {w : Nat} (f : UnIntr) (a : Repl w) : Repl w
  | bi {w : Nat} (f : BinIntr) (a b : Repl w) : Repl w
  | fsh {w : Nat} (left : Bool) (a b c : Repl w) : Repl w

/-- Runs a replacement: its operands that exist have their values, and its new instructions run in order. -/
def Repl.eval (ρ : Env) : {w : Nat} → Repl w → Outcome (Val w)
  | _, .old t => Outcome.ok (t.denote ρ)
  | _, .const c => Outcome.ok (some c)
  | _, .poison => Outcome.ok none
  | _, .bin op f a b => andThen (a.eval ρ) fun x => andThen (b.eval ρ) fun y => op.eval f x y
  | _, .icmp p s a b => andThen (a.eval ρ) fun x => andThen (b.eval ρ) fun y => Outcome.ok (p.eval x y s)
  | _, .select c t e =>
    andThen (c.eval ρ) fun x => andThen (t.eval ρ) fun y => andThen (e.eval ρ) fun z =>
      Outcome.ok (IRLean.select x y z)
  | w, .zext nneg a => andThen (a.eval ρ) fun x => Outcome.ok (Val.zext w x nneg)
  | w, .sext a => andThen (a.eval ρ) fun x => Outcome.ok (Val.sext w x)
  | w, .trunc nuw nsw a => andThen (a.eval ρ) fun x => Outcome.ok (Val.trunc w x nuw nsw)
  | _, .un f a => andThen (a.eval ρ) fun x => Outcome.ok (f.eval x)
  | _, .bi f a b => andThen (a.eval ρ) fun x => andThen (b.eval ρ) fun y => Outcome.ok (f.eval x y)
  | _, .fsh l a b c =>
    andThen (a.eval ρ) fun x => andThen (b.eval ρ) fun y => andThen (c.eval ρ) fun z =>
      Outcome.ok ((if l then Val.fshl else Val.fshr) x y z)

@[simp] theorem Repl.eval_old (ρ : Env) (t : Term w) : (Repl.old t).eval ρ = Outcome.ok (t.denote ρ) := rfl
@[simp] theorem Repl.eval_const (ρ : Env) (c : BitVec w) : (Repl.const c).eval ρ = Outcome.ok (some c) := rfl
@[simp] theorem Repl.eval_poison (ρ : Env) : (Repl.poison : Repl w).eval ρ = Outcome.ok none := rfl

/-- An instruction, as what it computes from its operands: what a fold replaces. An operand isn't an instruction, so
it computes itself. -/
def Term.top : {w : Nat} → Term w → Repl w
  | _, .bin _ op f a b => .bin op f (.old a) (.old b)
  | _, .icmp _ p s a b => .icmp p s (.old a) (.old b)
  | _, .select _ c t e => .select (.old c) (.old t) (.old e)
  | _, .zext _ nneg a => .zext nneg (.old a)
  | _, .sext _ a => .sext (.old a)
  | _, .trunc _ nuw nsw a => .trunc nuw nsw (.old a)
  | _, .un _ f a => .un f (.old a)
  | _, .bi _ f a b => .bi f (.old a) (.old b)
  | _, .fsh _ l a b c => .fsh l (.old a) (.old b) (.old c)
  | _, t => .old t

end Peephole
