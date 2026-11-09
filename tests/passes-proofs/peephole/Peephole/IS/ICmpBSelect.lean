import Peephole.IS.ICmpBMinMax

/-! # InstSimplify's compare-and-select folds, and their rewrites for every input

At `llvmorg-23.1.3`, in `llvm/lib/Analysis/InstructionSimplify.cpp`: `isSameCompare` at 98-108, `simplifyCmpSelCase` at
115-129 with its wrappers `simplifyCmpSelTrueCase` and `simplifyCmpSelFalseCase` at 131-145, and
`simplifyCmpSelOfMaxMin` at 4716-4788. `threadCmpOverSelect` forwards to the wrappers, and
`simplifySelectWithICmpCond` to `simplifyCmpSelOfMaxMin`. Each step that rewrites carries its ID from
`tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyCmpSelCase.L121` | `icmp Pred LHS, RHS`, where it simplifies to the `select`'s condition, to true or false |
| `IS.simplifyCmpSelCase.L125` | the same, where the compare is the condition itself, or it with operands swapped |
| `IS.simplifyCmpSelOfMaxMin.L4763` | `(X pred Y) ? X : max/min(X, Y)` to the max/min, where `pred` is its strict predicate |
| `IS.simplifyCmpSelOfMaxMin.L4771` | `(X == Y) ? X : max/min(X, Y)` to the max/min |
| `IS.simplifyCmpSelOfMaxMin.L4775` | `(X != Y) ? X : max/min(X, Y)` to `X` |
| `IS.simplifyCmpSelOfMaxMin.L4783` | `(X pred Y) ? X : max/min(X, Y)` to `X`, where `pred`'s inverse is its strict predicate |

`simplifyCmpSelCase` answers for the compare in one arm of a `select`: `TrueOrFalse` is right where the `select`'s
condition is that constant, which is how `threadCmpOverSelect` uses it, so its theorem assumes so. It calls the
recursive `simplifyCmpInst`, which for an integer predicate is `simplifyICmpInst`, and its theorem takes that call's
soundness as a hypothesis, `ICmpSimp.Sound`.

`threadCmpOverSelect` is called from `simplifyFCmpInst` too, and from `simplifyICmpInst` on compares of pointers, and
`Term` has neither floating point nor pointers, so the theorems of `simplifyCmpSelCase` prove the integer instance,
not every input, and `folds/is-icmp-b.json` lists `L121` and `L125` unproved. `simplifyCmpSelOfMaxMin` needs a min or
max intrinsic, an integer. -/

namespace Peephole.IS.ICmpB

open IRLean

variable {w u : Nat}

/-! ### `simplifyCmpSelCase` -/

/-- `SimplifiedCmp == Cond`: the recursive call answered with the pointer `Cond`. A constant is one pointer per value;
an instruction InstSimplify would build isn't any existing pointer. -/
def sameRepl : Repl w → Term w → Bool
  | .old t, c => t.ident == c.ident
  | .const k, c => c.ident == .const w k.toNat
  | .poison, c => c.ident == .poison w
  | _, _ => false

theorem sameRepl_eval {ρ : Env} {r : Repl w} {c : Term w} (h : sameRepl r c = true) :
    r.eval ρ = Outcome.ok (c.denote ρ) := by
  cases r with
  | old t =>
    simp only [sameRepl, beq_iff_eq] at h
    rw [Repl.eval_old, Term.denote_of_ident h]
  | const k =>
    simp only [sameRepl, beq_iff_eq] at h
    cases c <;> simp_all [Term.ident]
    rename_i k'
    have : k' = k := BitVec.eq_of_toNat_eq h
    subst this
    rfl
  | poison =>
    simp only [sameRepl, beq_iff_eq] at h
    cases c <;> simp_all [Term.ident]
    rfl
  | _ => simp [sameRepl] at h

/-- `isSameCompare(V, Pred, LHS, RHS)`: `V` is `icmp Pred LHS, RHS`, or `icmp (swapped Pred) RHS, LHS`. `CPred == Pred`
compares predicates, not `samesign`. -/
def isSameCompare (v : Term 1) (p : Pred) (lhs rhs : Term w) : Bool :=
  match v with
  | .icmp _ cp _ cl cr => (cp == p && same cl lhs && same cr rhs) || (cp == swapP p && same cl rhs && same cr lhs)
  | _ => false

/-- `simplifyCmpSelCase(Pred, LHS, RHS, Cond, Q, MaxRecurse, TrueOrFalse)`, step by step. `simp` is the recursive
`simplifyCmpInst`, `simplifyICmpInst` for an integer predicate. -/
def _root_.Peephole.IS.simplifyCmpSelCase.steps (simp : ICmpSimp) (p : Pred) (s : Bool) (lhs rhs : Term w)
    (cond : Term 1) (n : Nat) (tof : BitVec 1) : List (Step 1) :=
  match simp p s lhs rhs n with
  | .value r =>
    [ -- %cmp simplified to the select condition (%cond).
      if sameRepl r cond then .fire "IS.simplifyCmpSelCase.L121" (.const tof) else .next,
      -- return SimplifiedCmp;
      .fire "simplifyICmpInst" r ]
  | .null =>
    [ -- It didn't simplify. However, if composed comparison is equivalent
      -- to the select condition (%cond) then we can replace it.
      if isSameCompare cond p lhs rhs then .fire "IS.simplifyCmpSelCase.L125" (.const tof) else .next ]
  | .delegated c => [.delegate c]

def _root_.Peephole.IS.simplifyCmpSelCase (simp : ICmpSimp) (p : Pred) (s : Bool) (lhs rhs : Term w)
    (cond : Term 1) (n : Nat) (tof : BitVec 1) : Result 1 :=
  run (simplifyCmpSelCase.steps simp p s lhs rhs cond n tof)

/-- `simplifyCmpSelTrueCase`: `TrueOrFalse` is `getTrue(Cond->getType())`, `i1` true. -/
def _root_.Peephole.IS.simplifyCmpSelTrueCase (simp : ICmpSimp) (p : Pred) (s : Bool) (lhs rhs : Term w)
    (cond : Term 1) (n : Nat) : Result 1 :=
  simplifyCmpSelCase simp p s lhs rhs cond n (BitVec.ofBool true)

/-- `simplifyCmpSelFalseCase`: `TrueOrFalse` is `getFalse(Cond->getType())`, `i1` false. -/
def _root_.Peephole.IS.simplifyCmpSelFalseCase (simp : ICmpSimp) (p : Pred) (s : Bool) (lhs rhs : Term w)
    (cond : Term 1) (n : Nat) : Result 1 :=
  simplifyCmpSelCase simp p s lhs rhs cond n (BitVec.ofBool false)

/-- `IS.simplifyCmpSelCase.L121`: the compare, where the recursive `simplifyICmpInst` answered with `Cond`, to
`TrueOrFalse`, where `Cond` is `TrueOrFalse`. -/
theorem _root_.Peephole.IS.simplifyCmpSelCase.L121 (ρ : Env) (simp : ICmpSimp) (hsimp : simp.Sound ρ) (p : Pred)
    (s : Bool) (lhs rhs : Term w) (cond : Term 1) (n : Nat) (tof : BitVec 1) (cl : lhs.Consistent ρ)
    (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hcond : cond.denote ρ = some tof) (r : Repl 1) (hr : simp p s lhs rhs n = .value r)
    (h : sameRepl r cond = true) : Refines ((icmpSrc p s lhs rhs).eval ρ) ((Repl.const tof).eval ρ) := by
  have := hsimp p s lhs rhs n r cl cr ul ur hr
  rwa [sameRepl_eval h, hcond] at this

theorem eval_le_of_some {p : Pred} {a b : Val w} {cs s : Bool} {t : BitVec 1} (h : p.eval a b cs = some t) :
    Refine.le (p.eval a b s) (some t) := by
  cases a with
  | none => rw [eval_none_left] at h; cases h
  | some x =>
  cases b with
  | none => rw [eval_none_right] at h; cases h
  | some y =>
  rw [eval_some] at h ⊢
  split at h
  · cases h
  · split
    · exact Refine.val_none _
    · rw [Option.some.inj h]; exact Refine.refl_val _

/-- `IS.simplifyCmpSelCase.L125`: the compare, where `Cond` is it or it swapped, to `TrueOrFalse`, where `Cond` is
`TrueOrFalse`. -/
theorem _root_.Peephole.IS.simplifyCmpSelCase.L125 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w)
    (cond : Term 1) (tof : BitVec 1) (cc : cond.Consistent ρ) (hcond : cond.denote ρ = some tof)
    (h : isSameCompare cond p lhs rhs = true) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((Repl.const tof).eval ρ) := by
  unfold isSameCompare at h
  split at h
  · next cid cp cs cl cr =>
    simp only [Term.Consistent] at cc
    obtain ⟨-, -, he⟩ := cc
    have hc : cp.eval (cl.denote ρ) (cr.denote ρ) cs = some tof := by rw [he]; exact hcond
    rw [icmpSrc_eval, Repl.eval_const]
    refine refines_ok ?_
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, h1⟩, h2⟩ | ⟨⟨rfl, h1⟩, h2⟩
    · obtain rfl := same_width h1
      rw [same_iff_specific] at h1 h2
      rw [← specific_denote h1, ← specific_denote h2] at hc
      exact eval_le_of_some hc
    · obtain rfl := same_width h1
      rw [same_iff_specific] at h1 h2
      rw [← specific_denote h1, ← specific_denote h2, eval_swap] at hc
      exact eval_le_of_some hc
  · cases h

/-- Theorem 1 for `simplifyCmpSelCase`: every value the model returns refines `icmp [samesign] Pred LHS, RHS`, at
every width, predicate, `samesign` flag and recursion budget, poison included, where `Cond` is `TrueOrFalse` and the
recursive `simplifyICmpInst` is sound. -/
theorem _root_.Peephole.IS.simplifyCmpSelCase.sound (ρ : Env) (simp : ICmpSimp) (hsimp : simp.Sound ρ) (p : Pred)
    (s : Bool) (lhs rhs : Term w) (cond : Term 1) (n : Nat) (tof : BitVec 1) (cl : lhs.Consistent ρ)
    (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false) (cc : cond.Consistent ρ)
    (hcond : cond.denote ρ = some tof) {r : Repl 1} (h : simplifyCmpSelCase simp p s lhs rhs cond n tof = .value r) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) := by
  suffices hs : ∀ site r, Step.fire site r ∈ simplifyCmpSelCase.steps simp p s lhs rhs cond n tof →
      Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) from run_sound hs h
  intro site r hmem
  unfold simplifyCmpSelCase.steps at hmem
  cases hr0 : simp p s lhs rhs n with
  | value r0 =>
    rw [hr0] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyCmpSelCase.L121 ρ simp hsimp p s lhs rhs cond n tof cl cr ul ur hcond r0 hr0 (by assumption)
    · simp only [Step.fire.injEq] at h
      obtain ⟨-, hrr⟩ := h
      rw [hrr]
      exact hsimp p s lhs rhs n r0 cl cr ul ur hr0
  | null =>
    rw [hr0] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    split at hmem <;> simp only [Step.fire.injEq, reduceCtorEq] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact simplifyCmpSelCase.L125 ρ p s lhs rhs cond tof cc hcond (by assumption)
  | delegated c =>
    rw [hr0] at hmem
    simp at hmem

/-- Theorem 1 for `simplifyCmpSelTrueCase`: as `simplifyCmpSelCase`'s, where `Cond` is true. -/
theorem _root_.Peephole.IS.simplifyCmpSelTrueCase.sound (ρ : Env) (simp : ICmpSimp) (hsimp : simp.Sound ρ)
    (p : Pred) (s : Bool) (lhs rhs : Term w) (cond : Term 1) (n : Nat) (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ)
    (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false) (cc : cond.Consistent ρ)
    (hcond : cond.denote ρ = some (BitVec.ofBool true)) {r : Repl 1}
    (h : simplifyCmpSelTrueCase simp p s lhs rhs cond n = .value r) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) :=
  simplifyCmpSelCase.sound ρ simp hsimp p s lhs rhs cond n _ cl cr ul ur cc hcond h

/-- Theorem 1 for `simplifyCmpSelFalseCase`: as `simplifyCmpSelCase`'s, where `Cond` is false. -/
theorem _root_.Peephole.IS.simplifyCmpSelFalseCase.sound (ρ : Env) (simp : ICmpSimp) (hsimp : simp.Sound ρ)
    (p : Pred) (s : Bool) (lhs rhs : Term w) (cond : Term 1) (n : Nat) (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ)
    (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false) (cc : cond.Consistent ρ)
    (hcond : cond.denote ρ = some (BitVec.ofBool false)) {r : Repl 1}
    (h : simplifyCmpSelFalseCase simp p s lhs rhs cond n = .value r) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) :=
  simplifyCmpSelCase.sound ρ simp hsimp p s lhs rhs cond n _ cl cr ul ur cc hcond h

/-! ### `simplifyCmpSelOfMaxMin` -/

/-- The `select` a fold replaces: `select (icmp [samesign] Pred CmpLHS, CmpRHS), TVal, FVal`. -/
def selSrc (p : Pred) (s : Bool) (cl cr : Term u) (tv fv : Term w) : Repl w :=
  .select (icmpSrc p s cl cr) (.old tv) (.old fv)

theorem selSrc_eval (ρ : Env) (p : Pred) (s : Bool) (cl cr : Term u) (tv fv : Term w) :
    (selSrc p s cl cr tv fv).eval ρ =
      Outcome.ok (IRLean.select (p.eval (cl.denote ρ) (cr.denote ρ) s) (tv.denote ρ) (fv.denote ρ)) := rfl

theorem select_inv (p : Pred) (a b : Val u) (s : Bool) (t e : Val w) :
    IRLean.select ((invP p).eval a b s) t e = IRLean.select (p.eval a b s) e t := by
  cases a with
  | none => rw [eval_none_left, eval_none_left]; rfl
  | some x =>
  cases b with
  | none => rw [eval_none_right, eval_none_right]; rfl
  | some y =>
  rw [eval_some, eval_some, test_inv]
  split
  · rfl
  · cases test p x y <;> rfl

/-- The two canonicalizations: the operand the compare and the `select` share to `CmpLHS`, by swapping the compare,
then to `TVal`, by swapping the arms and inverting the predicate. -/
def selCanon (cl cr : Term w) (p : Pred) (tv fv : Term w) : Term w × Term w × Pred × Term w × Term w :=
  -- Canonicalize common cmp+sel operand as CmpLHS.
  if specific cr tv || specific cr fv then
    -- Canonicalize common cmp+sel operand as TVal.
    if specific cr fv then (cr, cl, invP (swapP p), fv, tv) else (cr, cl, swapP p, tv, fv)
  else
    if specific cl fv then (cl, cr, invP p, fv, tv) else (cl, cr, p, tv, fv)

theorem selCanon_eval (ρ : Env) {cl cr tv fv x y t f : Term w} {p q : Pred} (s : Bool)
    (hc : selCanon cl cr p tv fv = (x, y, q, t, f)) :
    IRLean.select (p.eval (cl.denote ρ) (cr.denote ρ) s) (tv.denote ρ) (fv.denote ρ) =
      IRLean.select (q.eval (x.denote ρ) (y.denote ρ) s) (t.denote ρ) (f.denote ρ) := by
  unfold selCanon at hc
  split at hc <;> split at hc <;> simp only [Prod.mk.injEq] at hc <;> obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hc
  · rw [select_inv, eval_swap]
  · rw [eval_swap]
  · rw [select_inv]
  · rfl

/-- `dyn_cast<MinMaxIntrinsic>(V)`, and `MMI->getPredicate()`. -/
def mmPred? : Term w → Option Pred
  | .bi _ .smax _ _ => some .sgt
  | .bi _ .smin _ _ => some .slt
  | .bi _ .umax _ _ => some .ugt
  | .bi _ .umin _ _ => some .ult
  | _ => none

/-- `match(V, m_c_MaxOrMin(m_Specific(X), m_Specific(Y)))`. -/
def mmXY (v x y : Term w) : Bool :=
  match v with
  | .bi _ f a b =>
    (f == .smax || f == .smin || f == .umax || f == .umin) &&
      ((specific x a && specific y b) || (specific x b && specific y a))
  | _ => false

/-- A min or max of `x` and `y` by its predicate. -/
def mmRaw : Pred → BitVec w → BitVec w → BitVec w
  | .sgt, x, y => if x.sle y then y else x
  | .slt, x, y => if x.sle y then x else y
  | .ugt, x, y => if x.ule y then y else x
  | _, x, y => if x.ule y then x else y

theorem mmRaw_of_test {mp q : Pred} (hm : mp = .sgt ∨ mp = .slt ∨ mp = .ugt ∨ mp = .ult) (hq : strictP q = mp)
    {x y : BitVec w} (h : test q x y = true) : mmRaw mp x y = x := by
  rcases hm with rfl | rfl | rfl | rfl <;> cases q <;> simp only [strictP, reduceCtorEq] at hq <;>
    simp only [mmRaw, test] at h ⊢
  · exact Lemmas.smax_of_sle (by simp only [BitVec.slt, BitVec.sle, decide_eq_true_eq] at h ⊢; omega)
  · exact Lemmas.smax_of_sle h
  · exact Lemmas.smin_of_sle (by simp only [BitVec.slt, BitVec.sle, decide_eq_true_eq] at h ⊢; omega)
  · exact Lemmas.smin_of_sle h
  · exact Lemmas.umax_of_ule (by simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq] at h ⊢; omega)
  · exact Lemmas.umax_of_ule h
  · exact Lemmas.umin_of_ule (by simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq] at h ⊢; omega)
  · exact Lemmas.umin_of_ule h

theorem mmRaw_self {mp : Pred} (x : BitVec w) : mmRaw mp x x = x := by
  cases mp <;> simp [mmRaw]

theorem mmPred?_cases {v : Term w} {mp : Pred} (h : mmPred? v = some mp) :
    mp = .sgt ∨ mp = .slt ∨ mp = .ugt ∨ mp = .ult := by
  unfold mmPred? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp

/-- A min or max matched against `X` and `Y`, where neither is poison, is their min or max. -/
theorem mmXY_val {ρ : Env} {v x y : Term w} {mp : Pred} (hp : mmPred? v = some mp) (hxy : mmXY v x y = true)
    (cv : v.Consistent ρ) {xv yv : BitVec w} (hx : x.denote ρ = some xv) (hy : y.denote ρ = some yv) :
    v.denote ρ = some (mmRaw mp xv yv) := by
  cases v with
  | bi id f a b =>
    simp only [Term.Consistent] at cv
    obtain ⟨-, -, he⟩ := cv
    show ρ w id = _
    rw [← he]
    simp only [mmXY, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hxy
    obtain ⟨-, hab⟩ := hxy
    have hcomm : f.eval (a.denote ρ) (b.denote ρ) = f.eval (b.denote ρ) (a.denote ρ) := by
      cases f <;> simp only [mmPred?, reduceCtorEq] at hp
      · exact unsignedKind.comm_min _ _
      · exact unsignedKind.comm_max _ _
      · exact signedKind.comm_min _ _
      · exact signedKind.comm_max _ _
    have hval : f.eval (some xv) (some yv) = some (mmRaw mp xv yv) := by
      cases f <;> simp only [mmPred?, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;> rfl
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [specific_denote ha, specific_denote hb, hx, hy, hval]
    · rw [hcomm, specific_denote ha, specific_denote hb, hx, hy, hval]
  | _ => simp [mmPred?] at hp

theorem selCanon_arms {cl cr tv fv x y t f : Term w} {p q : Pred} (hc : selCanon cl cr p tv fv = (x, y, q, t, f)) :
    (t = tv ∧ f = fv) ∨ (t = fv ∧ f = tv) := by
  unfold selCanon at hc
  split at hc <;> split at hc <;> simp only [Prod.mk.injEq] at hc
  · exact Or.inr ⟨hc.2.2.2.1.symm, hc.2.2.2.2.symm⟩
  · exact Or.inl ⟨hc.2.2.2.1.symm, hc.2.2.2.2.symm⟩
  · exact Or.inr ⟨hc.2.2.2.1.symm, hc.2.2.2.2.symm⟩
  · exact Or.inl ⟨hc.2.2.2.1.symm, hc.2.2.2.2.symm⟩

/-- The `select` against a min or max, after the canonicalizations, refines an operand that's `X` where `X pred Y`
and the min or max where not. -/
theorem selmm_refines {ρ : Env} {p : Pred} {s : Bool} {cl cr tv fv x y t f r : Term w} {q mp : Pred}
    (hc : selCanon cl cr p tv fv = (x, y, q, t, f)) (hm : mmPred? f = some mp)
    (hxt : (specific x t && mmXY f x y) = true) (cf : f.Consistent ρ)
    (hr : ∀ xv yv, x.denote ρ = some xv → y.denote ρ = some yv →
      r.denote ρ = some (if test q xv yv then xv else mmRaw mp xv yv)) :
    Refines ((selSrc p s cl cr tv fv).eval ρ) ((Repl.old r).eval ρ) := by
  rw [Bool.and_eq_true] at hxt
  obtain ⟨ht, hmm⟩ := hxt
  rw [selSrc_eval, selCanon_eval ρ s hc, Repl.eval_old, specific_denote ht]
  refine refines_ok ?_
  cases hx : x.denote ρ with
  | none => rw [eval_none_left]; exact Refine.val_none _
  | some xv =>
  cases hy : y.denote ρ with
  | none => rw [eval_none_right]; exact Refine.val_none _
  | some yv =>
  rw [mmXY_val hm hmm cf hx hy, hr xv yv hx hy, eval_some]
  split
  · exact Refine.val_none _
  · cases test q xv yv <;> exact Refine.refl_val _

/-- `IS.simplifyCmpSelOfMaxMin.L4763`: `(X pred Y) ? X : max/min(X, Y)` to the max/min, where the max/min's predicate
is `pred` made strict, after the canonicalizations. -/
theorem _root_.Peephole.IS.simplifyCmpSelOfMaxMin.L4763 (ρ : Env) (p : Pred) (s : Bool) (cl cr tv fv x y t f : Term w)
    (q mp : Pred) (hc : selCanon cl cr p tv fv = (x, y, q, t, f)) (hm : mmPred? f = some mp)
    (hxt : (specific x t && mmXY f x y) = true) (cf : f.Consistent ρ) (h : (mp == strictP q) = true) :
    Refines ((selSrc p s cl cr tv fv).eval ρ) ((Repl.old f).eval ρ) := by
  rw [beq_iff_eq] at h
  refine selmm_refines hc hm hxt cf fun xv yv hx hy => ?_
  rw [Bool.and_eq_true] at hxt
  rw [mmXY_val hm hxt.2 cf hx hy]
  cases ht : test q xv yv
  · rfl
  · simp only [ite_true]
    rw [mmRaw_of_test (mmPred?_cases hm) h.symm ht]

/-- `IS.simplifyCmpSelOfMaxMin.L4771`: `(X == Y) ? X : max/min(X, Y)` to the max/min. -/
theorem _root_.Peephole.IS.simplifyCmpSelOfMaxMin.L4771 (ρ : Env) (p : Pred) (s : Bool) (cl cr tv fv x y t f : Term w)
    (q mp : Pred) (hc : selCanon cl cr p tv fv = (x, y, q, t, f)) (hm : mmPred? f = some mp)
    (hxt : (specific x t && mmXY f x y) = true) (cf : f.Consistent ρ) (h : (q == .eq) = true) :
    Refines ((selSrc p s cl cr tv fv).eval ρ) ((Repl.old f).eval ρ) := by
  rw [beq_iff_eq] at h
  subst h
  refine selmm_refines hc hm hxt cf fun xv yv hx hy => ?_
  rw [Bool.and_eq_true] at hxt
  rw [mmXY_val hm hxt.2 cf hx hy]
  cases ht : test .eq xv yv
  · rfl
  · simp only [test, beq_iff_eq] at ht
    subst ht
    simp only [ite_true, mmRaw_self]

/-- `IS.simplifyCmpSelOfMaxMin.L4775`: `(X != Y) ? X : max/min(X, Y)` to `X`. -/
theorem _root_.Peephole.IS.simplifyCmpSelOfMaxMin.L4775 (ρ : Env) (p : Pred) (s : Bool) (cl cr tv fv x y t f : Term w)
    (q mp : Pred) (hc : selCanon cl cr p tv fv = (x, y, q, t, f)) (hm : mmPred? f = some mp)
    (hxt : (specific x t && mmXY f x y) = true) (cf : f.Consistent ρ) (h : (q == .ne) = true) :
    Refines ((selSrc p s cl cr tv fv).eval ρ) ((Repl.old x).eval ρ) := by
  rw [beq_iff_eq] at h
  subst h
  refine selmm_refines hc hm hxt cf fun xv yv hx hy => ?_
  rw [hx]
  cases ht : test .ne xv yv
  · simp only [test, bne_eq_false_iff_eq] at ht
    subst ht
    simp only [Bool.false_eq_true, ite_false, mmRaw_self]
  · rfl

/-- `IS.simplifyCmpSelOfMaxMin.L4783`: `(X pred Y) ? X : max/min(X, Y)` to `X`, where the max/min's predicate is
`pred`'s inverse made strict. -/
theorem _root_.Peephole.IS.simplifyCmpSelOfMaxMin.L4783 (ρ : Env) (p : Pred) (s : Bool) (cl cr tv fv x y t f : Term w)
    (q mp : Pred) (hc : selCanon cl cr p tv fv = (x, y, q, t, f)) (hm : mmPred? f = some mp)
    (hxt : (specific x t && mmXY f x y) = true) (cf : f.Consistent ρ) (h : (mp == strictP (invP q)) = true) :
    Refines ((selSrc p s cl cr tv fv).eval ρ) ((Repl.old x).eval ρ) := by
  rw [beq_iff_eq] at h
  refine selmm_refines hc hm hxt cf fun xv yv hx hy => ?_
  rw [hx]
  cases ht : test q xv yv
  · simp only [Bool.false_eq_true, ite_false]
    have hi : test (invP q) xv yv = true := by rw [test_inv, ht]; rfl
    rw [mmRaw_of_test (mmPred?_cases hm) h.symm hi]
  · rfl

/-- `simplifyCmpSelOfMaxMin(CmpLHS, CmpRHS, Pred, TVal, FVal)` once the compare's operands and the `select`'s have one
width, step by step. A scalar `FVal` is never a `ShuffleVectorInst`, so nothing is peeked through. -/
def _root_.Peephole.IS.simplifyCmpSelOfMaxMin.steps (cl cr : Term w) (p : Pred) (tv fv : Term w) : List (Step w) :=
  match selCanon cl cr p tv fv with
  | (x, y, q, t, f) =>
    match mmPred? f with
    | some mp =>
      -- (X pred Y) ? X : max/min(X, Y)
      if specific x t && mmXY f x y then
        [ -- (X >  Y) ? X : max(X, Y) --> max(X, Y), and the like
          if mp == strictP q then .fire "IS.simplifyCmpSelOfMaxMin.L4763" (.old f) else .next,
          -- (X == Y) ? X : max/min(X, Y) --> max/min(X, Y)
          if q == .eq then .fire "IS.simplifyCmpSelOfMaxMin.L4771" (.old f) else .next,
          -- (X != Y) ? X : max/min(X, Y) --> X
          if q == .ne then .fire "IS.simplifyCmpSelOfMaxMin.L4775" (.old x) else .next,
          -- (X <  Y) ? X : max(X, Y) --> X, and the like
          if mp == strictP (invP q) then .fire "IS.simplifyCmpSelOfMaxMin.L4783" (.old x) else .next ]
      else []
    | none => []

/-- `simplifyCmpSelOfMaxMin(CmpLHS, CmpRHS, Pred, TVal, FVal)`. A compare's operands of another width than the
`select`'s are other pointers: neither swap happens, `TVal != X`, and it declines. -/
def _root_.Peephole.IS.simplifyCmpSelOfMaxMin (cl cr : Term u) (p : Pred) (tv fv : Term w) : Result w :=
  if h : u = w then run (simplifyCmpSelOfMaxMin.steps (h ▸ cl) (h ▸ cr) p tv fv) else .null

/-- Theorem 1 for `simplifyCmpSelOfMaxMin`: every value the model returns refines
`select (icmp [samesign] Pred CmpLHS, CmpRHS), TVal, FVal`, at every width, predicate and `samesign` flag, in every
run the arms are consistent with, poison included. -/
theorem _root_.Peephole.IS.simplifyCmpSelOfMaxMin.sound (ρ : Env) (p : Pred) (s : Bool) (cl cr : Term u)
    (tv fv : Term w) (ct : tv.Consistent ρ) (cf : fv.Consistent ρ) {r : Repl w}
    (h : simplifyCmpSelOfMaxMin cl cr p tv fv = .value r) :
    Refines ((selSrc p s cl cr tv fv).eval ρ) (r.eval ρ) := by
  unfold simplifyCmpSelOfMaxMin at h
  split at h
  · next hu =>
    subst hu
    suffices hs : ∀ site r, Step.fire site r ∈ simplifyCmpSelOfMaxMin.steps cl cr p tv fv →
        Refines ((selSrc p s cl cr tv fv).eval ρ) (r.eval ρ) from run_sound hs h
    intro site r hmem
    unfold simplifyCmpSelOfMaxMin.steps at hmem
    split at hmem
    next x y q t f hc =>
    have cff : f.Consistent ρ := by
      rcases selCanon_arms hc with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact cf
      · exact ct
    split at hmem
    · next mp hm =>
      split at hmem
      · next hxt =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h | h | h <;> split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;>
          obtain ⟨-, rfl⟩ := h
        · exact simplifyCmpSelOfMaxMin.L4763 ρ p s cl cr tv fv x y t f q mp hc hm hxt cff (by assumption)
        · exact simplifyCmpSelOfMaxMin.L4771 ρ p s cl cr tv fv x y t f q mp hc hm hxt cff (by assumption)
        · exact simplifyCmpSelOfMaxMin.L4775 ρ p s cl cr tv fv x y t f q mp hc hm hxt cff (by assumption)
        · exact simplifyCmpSelOfMaxMin.L4783 ρ p s cl cr tv fv x y t f q mp hc hm hxt cff (by assumption)
      · simp at hmem
    · simp at hmem
  · cases h

end Peephole.IS.ICmpB
