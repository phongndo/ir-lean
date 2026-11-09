import Peephole.IS.ArithRecur

/-! # InstSimplify's `simplifySubInst`, and its rewrites for every input

`simplifySubInst` is at `llvm/lib/Analysis/InstructionSimplify.cpp:741-894` at `llvmorg-23.1.3`. This is its model on
`Peephole.Term`, step by step in the C++'s order. Each step that rewrites carries its ID from
`tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifySubInst.L754` | `X - poison` and `poison - X` to poison |
| `IS.simplifySubInst.L759` | `X - undef` and `undef - X` to `undef`. IRLean has no `undef`, so this is about poison only |
| `IS.simplifySubInst.L763` | `X - 0` to `X` |
| `IS.simplifySubInst.L767` | `X - X` to 0 |
| `IS.simplifySubInst.L773` | `sub nuw 0, X` to 0 |
| `IS.simplifySubInst.L780` | `sub nsw 0, X` to 0, where `X`'s known zeros are every bit but the sign bit |
| `IS.simplifySubInst.L783` | `0 - X` to `X` there |
| `IS.simplifySubInst.L886` | `sub nuw C, (xor X, C)` to `X`, for a low-bit mask `C` |

`IS.simplifySubInst.L860`, `ptrtoint X - ptrtoint Y` to the constant difference of two pointers, needs memory: no
`Term` is a `ptrtoint`, so the model's step for it never matches.

The reassociations, such as `(X + Y) - Z` to what `X + (Y - Z)` simplifies to, return a recursive call's answer: they
fire as `"simplifyBinOp"`, and each has a theorem too, so `simplifySubInst.sound` covers every value the model
returns, for every `Recur` that's sound. -/

namespace Peephole.IS

open IRLean Peephole.IS.Arith

variable {w : Nat}

/-! ### Matchers -/

/-- `m_LowBitMask()`: a `ConstantInt` that `APInt::isMask` accepts, `c != 0 && ((c + 1) & c) == 0`. -/
def lowBitMask : Term w → Bool := cst fun c => c != 0#w && ((c + 1#w) &&& c) == 0#w

/-- `m_Xor(m_Value(X), m_Specific(S))` on `V`, binding `X`. Not commutative. -/
def xorOf (s v : Term w) : Option (Term w) :=
  match binop? .xor v with
  | some (_, x, b) => if specific s b then some x else none
  | none => none

/-! ### The model -/

/-- `simplifySubInst(Op0, Op1, IsNSW, IsNUW, Q, MaxRecurse)`, step by step. -/
def simplifySubInst.steps (o : Oracle) (d : DomOracle) (r : Recur) (op0 op1 : Term w) (isNSW isNUW : Bool)
    (maxRecurse : Nat) : List (Step w) :=
  [ -- foldOrCommuteConstant: the constant folder folds two constants, and `sub` isn't commutative, so a lone constant
    -- stays where it is.
    if op0.isConstant && op1.isConstant then .delegate "ConstantFoldBinaryOpOperands" else .next,
    -- X - poison -> poison
    -- poison - X -> poison
    if isPoison op0 || isPoison op1 then .fire "IS.simplifySubInst.L754" .poison else .next,
    -- X - undef -> undef
    -- undef - X -> undef
    if isUndefValue op0 || isUndefValue op1 then .fire "IS.simplifySubInst.L759" (.old .undef) else .next,
    -- X - 0 -> X
    if zero op1 then .fire "IS.simplifySubInst.L763" (.old op0) else .next,
    -- X - X -> 0
    if specific op0 op1 then .fire "IS.simplifySubInst.L767" (.const 0#w) else .next,
    -- Is this a negation?
    -- 0 - X -> 0 if the sub is NUW.
    if zero op0 && isNUW then .fire "IS.simplifySubInst.L773" (.const 0#w) else .next,
    -- Op1 is either 0 or the minimum signed value. If the sub is NSW, then Op1 must be 0 because negating the
    -- minimum signed value is undefined.
    if zero op0 && o.knownZero op1 == BitVec.intMax w && isNSW then .fire "IS.simplifySubInst.L780" (.const 0#w)
    else .next,
    -- 0 - X -> X if X is 0 or the minimum signed value.
    if zero op0 && o.knownZero op1 == BitVec.intMax w then .fire "IS.simplifySubInst.L783" (.old op1) else .next,
    -- (X + Y) - Z -> X + (Y - Z) or Y + (X - Z) if everything simplifies.
    -- See if "V === Y - Z" simplifies. It does!  Now see if "X + V" simplifies.
    match (if maxRecurse != 0 then binop? .add op0 else none) with
    | some (_, x, y) =>
      (r.binOp (maxRecurse - 1) .sub y op1).bind "simplifyBinOp" .next fun v =>
        (r.binOp (maxRecurse - 1) .add x v).bind "simplifyBinOp" .next fun w' => .fire "simplifyBinOp" (.old w')
    | none => .next,
    -- See if "V === X - Z" simplifies. It does!  Now see if "Y + V" simplifies.
    match (if maxRecurse != 0 then binop? .add op0 else none) with
    | some (_, x, y) =>
      (r.binOp (maxRecurse - 1) .sub x op1).bind "simplifyBinOp" .next fun v =>
        (r.binOp (maxRecurse - 1) .add y v).bind "simplifyBinOp" .next fun w' => .fire "simplifyBinOp" (.old w')
    | none => .next,
    -- X - (Y + Z) -> (X - Y) - Z or (X - Z) - Y if everything simplifies.
    -- See if "V === X - Y" simplifies. It does!  Now see if "V - Z" simplifies.
    match (if maxRecurse != 0 then binop? .add op1 else none) with
    | some (_, y, z) =>
      (r.binOp (maxRecurse - 1) .sub op0 y).bind "simplifyBinOp" .next fun v =>
        (r.binOp (maxRecurse - 1) .sub v z).bind "simplifyBinOp" .next fun w' => .fire "simplifyBinOp" (.old w')
    | none => .next,
    -- See if "V === X - Z" simplifies. It does!  Now see if "V - Y" simplifies.
    match (if maxRecurse != 0 then binop? .add op1 else none) with
    | some (_, y, z) =>
      (r.binOp (maxRecurse - 1) .sub op0 z).bind "simplifyBinOp" .next fun v =>
        (r.binOp (maxRecurse - 1) .sub v y).bind "simplifyBinOp" .next fun w' => .fire "simplifyBinOp" (.old w')
    | none => .next,
    -- Z - (X - Y) -> (Z - X) + Y if everything simplifies.
    -- See if "V === Z - X" simplifies. It does!  Now see if "V + Y" simplifies.
    match (if maxRecurse != 0 then binop? .sub op1 else none) with
    | some (_, x, y) =>
      (r.binOp (maxRecurse - 1) .sub op0 x).bind "simplifyBinOp" .next fun v =>
        (r.binOp (maxRecurse - 1) .add v y).bind "simplifyBinOp" .next fun w' => .fire "simplifyBinOp" (.old w')
    | none => .next,
    -- trunc(X) - trunc(Y) -> trunc(X - Y) if everything simplifies.
    -- See if "V === X - Y" simplifies. It does!  Now see if "trunc V" simplifies: simplifyCastInst isn't modelled.
    match op0, op1 with
    | .trunc (v := v0) _ _ _ x, .trunc (v := v1) _ _ _ y =>
      if maxRecurse != 0 then
        if h : v1 = v0 then
          (r.binOp (maxRecurse - 1) .sub x (h ▸ y)).bind "simplifyBinOp" .next fun _ => .delegate "simplifyCastInst"
        else .next
      else .next
    | _, _ => .next,
    -- Variations on GEP(base, I, ...) - GEP(base, i, ...) -> GEP(null, I-i, ...): `m_PtrToIntOrAddr` matches no
    -- `Term`, since a `ptrtoint` is an operand the model doesn't see into.
    .next,
    -- i1 sub -> xor: what simplifyXorInst answers isn't modelled.
    if maxRecurse != 0 && w == 1 then .delegate "simplifyXorInst" else .next,
    forward (simplifyByDomEq.steps d .sub op0 op1 maxRecurse),
    -- (sub nuw C_Mask, (xor X, C_Mask)) -> X
    if isNUW then
      match xorOf op0 op1 with
      | some x => if lowBitMask op0 then .fire "IS.simplifySubInst.L886" (.old x) else .next
      | none => .next
    else .next ]

/-- `simplifySubInst(Op0, Op1, IsNSW, IsNUW, Q, MaxRecurse)`. -/
def simplifySubInst (o : Oracle) (d : DomOracle) (r : Recur) (op0 op1 : Term w) (isNSW isNUW : Bool)
    (maxRecurse : Nat) : Result w :=
  run (simplifySubInst.steps o d r op0 op1 isNSW isNUW maxRecurse)

/-- What InstSimplify does with a `sub`: `simplifyInstruction` calls `simplifySubInst` with the instruction's own flags
and `MaxRecurse` at `RecursionLimit`. The recursive calls and the dominating conditions are what the model doesn't
say: `Recur.unknown` and `DomOracle.none`. -/
def simplifySubInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .sub f a b => simplifySubInst o DomOracle.none Recur.unknown a b f.nsw f.nuw recursionLimit
  | _, _ => .null

/-! ### The rewrites, one theorem each -/

/-- The `sub` `simplifySubInst` replaces, with its operands and flags. -/
def subSrc (op0 op1 : Term w) (isNSW isNUW : Bool) : Repl w :=
  binSrc .sub { nuw := isNUW, nsw := isNSW } op0 op1

theorem subSrc_eval (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) :
    (subSrc op0 op1 isNSW isNUW).eval ρ = Outcome.ok (Val.sub (op0.denote ρ) (op1.denote ρ) isNUW isNSW) := rfl

/-- `IS.simplifySubInst.L754`: `X - poison` and `poison - X` to poison. -/
theorem simplifySubInst.L754 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool)
    (h : (isPoison op0 || isPoison op1) = true) :
    Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.poison : Repl w).eval ρ) := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [subSrc, binSrc_eval, isPoison_denote h]; exact eval_none_left _ _ _ _
  · rw [subSrc, binSrc_eval, isPoison_denote h]; exact eval_none_right _ _ _ _

/-- `IS.simplifySubInst.L759`: `X - undef` and `undef - X` to `undef`, which without `undef` is poison to poison. -/
theorem simplifySubInst.L759 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) (h : (isUndefValue op0 || isUndefValue op1) = true) :
    Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old (.undef : Term w)).eval ρ) := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [subSrc, binSrc_eval, isUndefValue_denote h u0]; exact eval_none_left _ _ _ _
  · rw [subSrc, binSrc_eval, isUndefValue_denote h u1]; exact eval_none_right _ _ _ _

/-- `IS.simplifySubInst.L763`: `X - 0` to `X`. -/
theorem simplifySubInst.L763 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (h : zero op1 = true) :
    Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [subSrc_eval, cst_eq h, Generic.sub_zero]
  exact ok_refl _

/-- `IS.simplifySubInst.L767`: `X - X` to 0. -/
theorem simplifySubInst.L767 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (h : specific op0 op1 = true) :
    Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [subSrc_eval, specific_denote h]
  exact ok_refines (Generic.sub_self_refines _ _ _)

/-- `IS.simplifySubInst.L773`: `sub nuw 0, X` to 0. -/
theorem simplifySubInst.L773 (ρ : Env) (op0 op1 : Term w) (isNSW : Bool) (h : zero op0 = true) :
    Refines ((subSrc op0 op1 isNSW true).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [subSrc_eval, cst_eq h]
  exact ok_refines (Lemmas.sub_zero_left_nuw_refines _ _)

/-- `IS.simplifySubInst.L780`: `sub nsw 0, X` to 0, where `computeKnownBits(X).Zero` is every bit but the sign bit. -/
theorem simplifySubInst.L780 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 : Term w) (isNUW : Bool)
    (h0 : zero op0 = true) (hk : o.knownZero op1 = BitVec.intMax w) :
    Refines ((subSrc op0 op1 true isNUW).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [subSrc_eval, cst_eq h0]
  cases h1 : op1.denote ρ with
  | none => exact ok_refines (by cases isNUW <;> exact Refine.val_none _)
  | some y =>
    have := ho.knownZero op1 y h1
    rw [hk] at this
    exact ok_refines (Lemmas.sub_zero_left_nsw_refines this _)

/-- `IS.simplifySubInst.L783`: `0 - X` to `X`, where `computeKnownBits(X).Zero` is every bit but the sign bit. -/
theorem simplifySubInst.L783 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 op1 : Term w) (isNSW isNUW : Bool)
    (h0 : zero op0 = true) (hk : o.knownZero op1 = BitVec.intMax w) :
    Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [subSrc_eval, cst_eq h0, Repl.eval_old]
  cases h1 : op1.denote ρ with
  | none => exact ok_refines (Refine.val_none _)
  | some y =>
    have := ho.knownZero op1 y h1
    rw [hk] at this
    exact ok_refines (Lemmas.sub_zero_left_refines_self this _ _)

/-- `IS.simplifySubInst.L886`: `sub nuw C, (xor X, C)` to `X`, for a low-bit mask `C`. -/
theorem simplifySubInst.L886 (ρ : Env) (op0 op1 x : Term w) (isNSW : Bool) (c1 : op1.Consistent ρ)
    (hx : xorOf op0 op1 = some x) (hm : lowBitMask op0 = true) :
    Refines ((subSrc op0 op1 isNSW true).eval ρ) ((Repl.old x).eval ρ) := by
  unfold xorOf at hx
  split at hx
  · next g x' b hb =>
    split at hx
    · next hs =>
      cases hx
      obtain ⟨c, hc, hd⟩ := cst_denote (ρ := ρ) hm
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
      rw [subSrc_eval, xor_denote hb c1, specific_denote hs, hd, Repl.eval_old]
      exact ok_refines (Lemmas.sub_mask_xor_nuw_refines _ hc.2 _)
    · cases hx
  · cases hx

/-! ### The reassociations -/

private theorem sub_plain (x y : BitVec w) : BinOp.eval .sub {} (some x) (some y) = Outcome.ok (some (x - y)) := by
  simp [BinOp.eval, Val.sub]

private theorem add_plain (x y : BitVec w) : BinOp.eval .add {} (some x) (some y) = Outcome.ok (some (x + y)) := by
  simp [BinOp.eval, Val.add]

/-- A `sub`, with any flags, refines a value that's the difference wherever its operands are values. -/
private theorem sub_refines {a b t : Val w} (nuw nsw : Bool)
    (ht : ∀ x y, a = some x → b = some y → t = some (x - y)) :
    Refines (Outcome.ok (Val.sub a b nuw nsw)) (Outcome.ok t) := by
  cases a with
  | none => exact ok_none_refines _
  | some x =>
  cases b with
  | none => exact ok_none_refines _
  | some y =>
    rw [ht x y rfl rfl]
    simp only [Val.sub]
    split
    · exact ok_none_refines _
    · exact ok_refl _

/-- A matched `sub` that gave a value had values for operands, and gave their difference. -/
private theorem sub_some {ρ : Env} {t a b : Term w} {g : Flags} (h : binop? .sub t = some (g, a, b))
    (hc : t.Consistent ρ) {l : BitVec w} (hl : t.denote ρ = some l) :
    ∃ x y, a.denote ρ = some x ∧ b.denote ρ = some y ∧ l = x - y := by
  have := binop?_eval h hc
  rw [hl] at this
  simp only [BinOp.eval, Outcome.ok, Option.some.injEq, Except.ok.injEq] at this
  revert this
  cases a.denote ρ <;> cases b.denote ρ <;> simp only [Val.sub, reduceCtorEq, false_imp_iff]
  rename_i x y
  split
  · simp
  · intro h; exact ⟨x, y, rfl, rfl, (Option.some.inj h).symm⟩

/-- A matched `add` that gave a value had values for operands, and gave their sum. -/
private theorem add_some {ρ : Env} {t a b : Term w} {g : Flags} (h : binop? .add t = some (g, a, b))
    (hc : t.Consistent ρ) {l : BitVec w} (hl : t.denote ρ = some l) :
    ∃ x y, a.denote ρ = some x ∧ b.denote ρ = some y ∧ l = x + y :=
  binop_raw_add h hc hl
where
  binop_raw_add {ρ : Env} {t a b : Term w} {g : Flags} (h : binop? .add t = some (g, a, b))
      (hc : t.Consistent ρ) {l : BitVec w} (hl : t.denote ρ = some l) :
      ∃ x y, a.denote ρ = some x ∧ b.denote ρ = some y ∧ l = x + y := by
    have := binop?_eval h hc
    rw [hl] at this
    exact eval_assoc_some (op := .add) rfl this

/-- A recursive answer about two values, where the operation with no flags gives `z`, is `z`. -/
private theorem recur_eq {ρ : Env} {r : Recur} (hr : r.Sound ρ) {n : Nat} {op : BinOp} {a b t : Term w}
    (h : r.binOp n op a b = .val t) (ca : a.Consistent ρ) (cb : b.Consistent ρ) (ua : a.hasUndef = false)
    (ub : b.hasUndef = false) {x y z : BitVec w} (hx : a.denote ρ = some x) (hy : b.denote ρ = some y)
    (hp : op.eval {} (some x) (some y) = Outcome.ok (some z)) :
    t.Consistent ρ ∧ t.hasUndef = false ∧ t.denote ρ = some z := by
  obtain ⟨ct, ut, hrf⟩ := hr.binOp n op a b t h ca cb ua ub
  rw [hx, hy, hp] at hrf
  exact ⟨ct, ut, eq_of_refines_some hrf⟩

/-- The facts a reassociation's proof starts from. -/
private theorem recur_ctx {ρ : Env} {r : Recur} (hr : r.Sound ρ) {n : Nat} {op : BinOp} {a b t : Term w}
    (h : r.binOp n op a b = .val t) (ca : a.Consistent ρ) (cb : b.Consistent ρ) (ua : a.hasUndef = false)
    (ub : b.hasUndef = false) : t.Consistent ρ ∧ t.hasUndef = false :=
  let ⟨ct, ut, _⟩ := hr.binOp n op a b t h ca cb ua ub
  ⟨ct, ut⟩

/-- `(X + Y) - Z` to what `X + V` simplifies to, where `Y - Z` simplifies to `V`. -/
theorem simplifySubInst.fwdAddLeft1 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op0 op1 : Term w) (isNSW isNUW : Bool)
    (n : Nat) {g : Flags} {x y v w' : Term w} (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) (hb : binop? .add op0 = some (g, x, y))
    (hv : r.binOp n .sub y op1 = .val v) (hw : r.binOp n .add x v = .val w') :
    Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old w').eval ρ) := by
  obtain ⟨cx, cy, -⟩ := binop?_consistent hb c0
  obtain ⟨ux, uy⟩ := binop?_noUndef hb u0
  obtain ⟨cv, uv⟩ := recur_ctx hr hv cy c1 uy u1
  rw [subSrc_eval, Repl.eval_old]
  refine sub_refines _ _ fun l c hl hc => ?_
  obtain ⟨a, b, ha, hb', rfl⟩ := add_some hb c0 hl
  obtain ⟨-, -, hV⟩ := recur_eq hr hv cy c1 uy u1 hb' hc (sub_plain _ _)
  obtain ⟨-, -, hW⟩ := recur_eq hr hw cx cv ux uv ha hV (add_plain _ _)
  rw [hW, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- `(X + Y) - Z` to what `Y + V` simplifies to, where `X - Z` simplifies to `V`. -/
theorem simplifySubInst.fwdAddLeft2 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op0 op1 : Term w) (isNSW isNUW : Bool)
    (n : Nat) {g : Flags} {x y v w' : Term w} (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) (hb : binop? .add op0 = some (g, x, y))
    (hv : r.binOp n .sub x op1 = .val v) (hw : r.binOp n .add y v = .val w') :
    Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old w').eval ρ) := by
  obtain ⟨cx, cy, -⟩ := binop?_consistent hb c0
  obtain ⟨ux, uy⟩ := binop?_noUndef hb u0
  obtain ⟨cv, uv⟩ := recur_ctx hr hv cx c1 ux u1
  rw [subSrc_eval, Repl.eval_old]
  refine sub_refines _ _ fun l c hl hc => ?_
  obtain ⟨a, b, ha, hb', rfl⟩ := add_some hb c0 hl
  obtain ⟨-, -, hV⟩ := recur_eq hr hv cx c1 ux u1 ha hc (sub_plain _ _)
  obtain ⟨-, -, hW⟩ := recur_eq hr hw cy cv uy uv hb' hV (add_plain _ _)
  rw [hW, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_comm a b, BitVec.add_assoc]

/-- `X - (Y + Z)` to what `V - Z` simplifies to, where `X - Y` simplifies to `V`. -/
theorem simplifySubInst.fwdAddRight1 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op0 op1 : Term w) (isNSW isNUW : Bool)
    (n : Nat) {g : Flags} {y z v w' : Term w} (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) (hb : binop? .add op1 = some (g, y, z))
    (hv : r.binOp n .sub op0 y = .val v) (hw : r.binOp n .sub v z = .val w') :
    Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old w').eval ρ) := by
  obtain ⟨cy, cz, -⟩ := binop?_consistent hb c1
  obtain ⟨uy, uz⟩ := binop?_noUndef hb u1
  obtain ⟨cv, uv⟩ := recur_ctx hr hv c0 cy u0 uy
  rw [subSrc_eval, Repl.eval_old]
  refine sub_refines _ _ fun a m ha hm => ?_
  obtain ⟨b, c, hb', hc, rfl⟩ := add_some hb c1 hm
  obtain ⟨-, -, hV⟩ := recur_eq hr hv c0 cy u0 uy ha hb' (sub_plain _ _)
  obtain ⟨-, -, hW⟩ := recur_eq hr hw cv cz uv uz hV hc (sub_plain _ _)
  rw [hW, BitVec.sub_sub]

/-- `X - (Y + Z)` to what `V - Y` simplifies to, where `X - Z` simplifies to `V`. -/
theorem simplifySubInst.fwdAddRight2 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op0 op1 : Term w) (isNSW isNUW : Bool)
    (n : Nat) {g : Flags} {y z v w' : Term w} (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) (hb : binop? .add op1 = some (g, y, z))
    (hv : r.binOp n .sub op0 z = .val v) (hw : r.binOp n .sub v y = .val w') :
    Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old w').eval ρ) := by
  obtain ⟨cy, cz, -⟩ := binop?_consistent hb c1
  obtain ⟨uy, uz⟩ := binop?_noUndef hb u1
  obtain ⟨cv, uv⟩ := recur_ctx hr hv c0 cz u0 uz
  rw [subSrc_eval, Repl.eval_old]
  refine sub_refines _ _ fun a m ha hm => ?_
  obtain ⟨b, c, hb', hc, rfl⟩ := add_some hb c1 hm
  obtain ⟨-, -, hV⟩ := recur_eq hr hv c0 cz u0 uz ha hc (sub_plain _ _)
  obtain ⟨-, -, hW⟩ := recur_eq hr hw cv cy uv uy hV hb' (sub_plain _ _)
  rw [hW, BitVec.sub_sub, BitVec.add_comm c b]

/-- `Z - (X - Y)` to what `V + Y` simplifies to, where `Z - X` simplifies to `V`. -/
theorem simplifySubInst.fwdSubRight (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op0 op1 : Term w) (isNSW isNUW : Bool)
    (n : Nat) {g : Flags} {x y v w' : Term w} (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) (hb : binop? .sub op1 = some (g, x, y))
    (hv : r.binOp n .sub op0 x = .val v) (hw : r.binOp n .add v y = .val w') :
    Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old w').eval ρ) := by
  obtain ⟨cx, cy, -⟩ := binop?_consistent hb c1
  obtain ⟨ux, uy⟩ := binop?_noUndef hb u1
  obtain ⟨cv, uv⟩ := recur_ctx hr hv c0 cx u0 ux
  rw [subSrc_eval, Repl.eval_old]
  refine sub_refines _ _ fun c m hc hm => ?_
  obtain ⟨a, b, ha, hb', rfl⟩ := sub_some hb c1 hm
  obtain ⟨-, -, hV⟩ := recur_eq hr hv c0 cx u0 ux hc ha (sub_plain _ _)
  obtain ⟨-, -, hW⟩ := recur_eq hr hw cv cy uv uy hV hb' (add_plain _ _)
  have e : c - (a - b) = c - a + b := by
    rw [BitVec.sub_eq_add_neg c (a - b), BitVec.neg_sub, ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg]
  rw [hW, e]

/-! ### The fold -/

/-- The two operands of a reassociation's match, under `MaxRecurse != 0`. -/
private theorem recurse_match {op : BinOp} {t : Term w} {n : Nat} {g : Flags} {a b : Term w}
    (h : (if n != 0 then binop? op t else none) = some (g, a, b)) : binop? op t = some (g, a, b) := by
  split at h
  · exact h
  · cases h

/-- What a reassociation's step fires: what the second recursive call answered. -/
private theorem bind2_fire {a1 : Ans w} {k : Term w → Ans w} {s : String} {res : Repl w}
    (h : a1.bind "simplifyBinOp" .next (fun v => (k v).bind "simplifyBinOp" .next
      fun w' => .fire "simplifyBinOp" (.old w')) = .fire s res) :
    ∃ v w', a1 = .val v ∧ k v = .val w' ∧ res = .old w' := by
  rcases Ans.bind_fire h with ⟨-, h⟩ | ⟨v, hv, h⟩
  · cases h
  rcases Ans.bind_fire h with ⟨-, h⟩ | ⟨w', hw, h⟩
  · cases h
  simp only [Step.fire.injEq] at h
  exact ⟨v, w', hv, hw, h.2.symm⟩

/-- Every step of `simplifySubInst` that fires is right. -/
theorem simplifySubInst.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : DomOracle) (hd : d.Sound ρ)
    (r : Recur) (hr : r.Sound ρ) (op0 op1 : Term w) (isNSW isNUW : Bool) (n : Nat)
    (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) :
    ∀ s res, Step.fire s res ∈ simplifySubInst.steps o d r op0 op1 isNSW isNUW n →
      Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) (res.eval ρ) := by
  intro s res hmem
  simp only [simplifySubInst.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifySubInst.L754 ρ op0 op1 isNSW isNUW (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifySubInst.L759 ρ op0 op1 isNSW isNUW u0 u1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifySubInst.L763 ρ op0 op1 isNSW isNUW (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifySubInst.L767 ρ op0 op1 isNSW isNUW (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨h0, rfl⟩ := hc
    exact simplifySubInst.L773 ρ op0 op1 isNSW h0
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨h0, hk⟩, rfl⟩ := hc
    exact simplifySubInst.L780 ρ o ho op0 op1 isNUW h0 hk
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact simplifySubInst.L783 ρ o ho op0 op1 isNSW isNUW hc.1 hc.2
  · split at h
    · next hm =>
      obtain ⟨v, w', hv, hw, rfl⟩ := bind2_fire h.symm
      exact simplifySubInst.fwdAddLeft1 ρ r hr op0 op1 isNSW isNUW _ c0 c1 u0 u1 (recurse_match hm) hv hw
    · simp only [reduceCtorEq] at h
  · split at h
    · next hm =>
      obtain ⟨v, w', hv, hw, rfl⟩ := bind2_fire h.symm
      exact simplifySubInst.fwdAddLeft2 ρ r hr op0 op1 isNSW isNUW _ c0 c1 u0 u1 (recurse_match hm) hv hw
    · simp only [reduceCtorEq] at h
  · split at h
    · next hm =>
      obtain ⟨v, w', hv, hw, rfl⟩ := bind2_fire h.symm
      exact simplifySubInst.fwdAddRight1 ρ r hr op0 op1 isNSW isNUW _ c0 c1 u0 u1 (recurse_match hm) hv hw
    · simp only [reduceCtorEq] at h
  · split at h
    · next hm =>
      obtain ⟨v, w', hv, hw, rfl⟩ := bind2_fire h.symm
      exact simplifySubInst.fwdAddRight2 ρ r hr op0 op1 isNSW isNUW _ c0 c1 u0 u1 (recurse_match hm) hv hw
    · simp only [reduceCtorEq] at h
  · split at h
    · next hm =>
      obtain ⟨v, w', hv, hw, rfl⟩ := bind2_fire h.symm
      exact simplifySubInst.fwdSubRight ρ r hr op0 op1 isNSW isNUW _ c0 c1 u0 u1 (recurse_match hm) hv hw
    · simp only [reduceCtorEq] at h
  · split at h
    · split at h
      · split at h
        · rcases Ans.bind_fire h.symm with ⟨-, h⟩ | ⟨_, _, h⟩ <;> cases h
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · exact simplifyByDomEq.steps_sound ρ d hd .sub { nuw := isNUW, nsw := isNSW } op0 op1 n s res
      (forward_fire h.symm)
  · split at h
    · next hn =>
      split at h
      · next x hx =>
        split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
        next hm =>
        obtain ⟨-, rfl⟩ := h
        subst hn
        exact simplifySubInst.L886 ρ op0 op1 x isNSW c1 hx hm
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h

/-- Theorem 1 for `simplifySubInst`: every value the model returns refines the `sub` it replaces, at every width, for
both flags and every recursion budget, in every run its operands are consistent with, poison included, for every
oracle, dominating-condition oracle and recursive simplifier that's sound in the run. It says nothing about operands
that reach an `undef`. -/
theorem simplifySubInst.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : DomOracle) (hd : d.Sound ρ) (r : Recur)
    (hr : r.Sound ρ) (op0 op1 : Term w) (isNSW isNUW : Bool) (n : Nat)
    (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false)
    {res : Repl w} (h : simplifySubInst o d r op0 op1 isNSW isNUW n = .value res) :
    Refines ((subSrc op0 op1 isNSW isNUW).eval ρ) (res.eval ρ) :=
  run_sound (simplifySubInst.steps_sound ρ o ho d hd r hr op0 op1 isNSW isNUW n c0 c1 u0 u1) h

end Peephole.IS
