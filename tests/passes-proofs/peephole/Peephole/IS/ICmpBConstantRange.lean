import Peephole.IS.ICmpConstantRange

/-! # `ConstantRange`'s `intersectWith` and `unionWith`, as `simplifyAndOrOfICmpsWithConstants` uses them

`llvm/lib/IR/ConstantRange.cpp:458-465` and `581-778` at `llvmorg-23.1.3`: `isSizeStrictlySmallerThan`,
`getPreferredRange`, `intersectWith` and `unionWith`, with the default `PreferredRangeType`, `Smallest`, on the
`icmp` family's model of `ConstantRange`, `Peephole.IS.ICmp.CR`. Each is as the C++ computes it on `Lower` and
`Upper`, statement by statement, with the C++'s pictures of the cases. What each says about values:

- `intersectWith a b` contains every value both `a` and `b` contain: `intersectWith_contains`. Where the two ranges'
  intersection isn't one range, it contains more.
- Where `unionWith a b` is the full set, every value is in `a` or in `b`: `unionWith_isFullSet`. Where the two ranges'
  union isn't one range, `unionWith` contains more, but then it isn't full.

Neither needs a positive width. -/

namespace Peephole.IS.ICmpB.Range

open Peephole.IS.ICmp

variable {w : Nat}

/-! ### The functions, as `ConstantRange.cpp` has them -/

/-- `ConstantRange::isSizeStrictlySmallerThan`. -/
def isSizeStrictlySmallerThan (a b : CR w) : Bool :=
  if a.isFullSet then false
  else if b.isFullSet then true
  else BitVec.ult (a.upper - a.lower) (b.upper - b.lower)

/-- `getPreferredRange(CR1, CR2, Smallest)`: `CR1` if it's strictly smaller, else `CR2`. -/
def getPreferredRange (a b : CR w) : CR w := if isSizeStrictlySmallerThan a b then a else b

/-- `intersectWith` from its fourth statement on, where neither range is empty or full and `a` is upper-wrapped if
`b` is. -/
def intersectCore (a b : CR w) : CR w :=
  if !a.isUpperWrapped && !b.isUpperWrapped then
    if BitVec.ult a.lower b.lower then
      -- L---U       : this
      --       L---U : CR
      if BitVec.ule a.upper b.lower then CR.empty
      -- L---U       : this
      --   L---U     : CR
      else if BitVec.ult a.upper b.upper then ⟨b.lower, a.upper⟩
      -- L-------U   : this
      --   L---U     : CR
      else b
    --   L---U     : this
    -- L-------U   : CR
    else if BitVec.ult a.upper b.upper then a
    --   L-----U   : this
    -- L-----U     : CR
    else if BitVec.ult a.lower b.upper then ⟨a.lower, b.upper⟩
    --       L---U : this
    -- L---U       : CR
    else CR.empty
  else if a.isUpperWrapped && !b.isUpperWrapped then
    if BitVec.ult b.lower a.upper then
      -- ------U   L--- : this
      --  L--U          : CR
      if BitVec.ult b.upper a.upper then b
      -- ------U   L--- : this
      --  L------U      : CR
      else if BitVec.ule b.upper a.lower then ⟨b.lower, a.upper⟩
      -- ------U   L--- : this
      --  L----------U  : CR
      else getPreferredRange a b
    else if BitVec.ult b.lower a.lower then
      -- --U      L---- : this
      --     L--U       : CR
      if BitVec.ule b.upper a.lower then CR.empty
      -- --U      L---- : this
      --     L------U   : CR
      else ⟨a.lower, b.upper⟩
    -- --U  L------ : this
    --        L--U  : CR
    else b
  else if BitVec.ult b.upper a.upper then
    -- ------U L-- : this
    -- --U L------ : CR
    if BitVec.ult b.lower a.upper then getPreferredRange a b
    -- ----U   L-- : this
    -- --U   L---- : CR
    else if BitVec.ult b.lower a.lower then ⟨a.lower, b.upper⟩
    -- ----U L---- : this
    -- --U     L-- : CR
    else b
  else if BitVec.ule b.upper a.lower then
    -- --U     L-- : this
    -- ----U L---- : CR
    if BitVec.ult b.lower a.lower then a
    -- --U   L---- : this
    -- ----U   L-- : CR
    else ⟨b.lower, a.upper⟩
  -- --U L------ : this
  -- ------U L-- : CR
  else getPreferredRange a b

/-- `ConstantRange::intersectWith(CR, Smallest)`. Where `a` isn't upper-wrapped and `b` is, the C++ returns
`CR.intersectWith(*this, Type)`, whose first three statements then fall through: that's `intersectCore b a`. -/
def intersectWith (a b : CR w) : CR w :=
  -- Handle common cases.
  if a.isEmptySet || b.isFullSet then a
  else if b.isEmptySet || a.isFullSet then b
  else if !a.isUpperWrapped && b.isUpperWrapped then intersectCore b a
  else intersectCore a b

/-- `unionWith` from its fourth statement on, where neither range is empty or full and `a` is upper-wrapped if `b`
is. -/
def unionCore (a b : CR w) : CR w :=
  if !a.isUpperWrapped && !b.isUpperWrapped then
    --        L---U  and  L---U        : this
    --  L---U                   L---U  : CR
    -- result in one of
    --  L---------U
    -- -----U L-----
    if BitVec.ult b.upper a.lower || BitVec.ult a.upper b.lower then
      getPreferredRange ⟨a.lower, b.upper⟩ ⟨b.lower, a.upper⟩
    else
      let l := if BitVec.ult b.lower a.lower then b.lower else a.lower
      let u := if BitVec.ult (a.upper - 1#w) (b.upper - 1#w) then b.upper else a.upper
      if l == 0#w && u == 0#w then CR.full else ⟨l, u⟩
  else if !b.isUpperWrapped then
    -- ------U   L-----  and  ------U   L----- : this
    --   L--U                            L--U  : CR
    if BitVec.ule b.upper a.upper || BitVec.ule a.lower b.lower then a
    -- ------U   L----- : this
    --    L---------U   : CR
    else if BitVec.ule b.lower a.upper && BitVec.ule a.lower b.upper then CR.full
    -- ----U       L---- : this
    --       L---U       : CR
    -- results in one of
    -- ----------U L----
    -- ----U L----------
    else if BitVec.ult a.upper b.lower && BitVec.ult b.upper a.lower then
      getPreferredRange ⟨a.lower, b.upper⟩ ⟨b.lower, a.upper⟩
    -- ----U     L----- : this
    --        L----U    : CR
    else if BitVec.ult a.upper b.lower && BitVec.ule a.lower b.upper then ⟨b.lower, a.upper⟩
    -- ------U    L---- : this
    --    L-----U       : CR
    else ⟨a.lower, b.upper⟩
  -- ------U    L----  and  ------U    L---- : this
  -- -U  L-----------  and  ------------U  L : CR
  else if BitVec.ule b.lower a.upper || BitVec.ule a.lower b.upper then CR.full
  else ⟨if BitVec.ult b.lower a.lower then b.lower else a.lower,
    if BitVec.ult a.upper b.upper then b.upper else a.upper⟩

/-- `ConstantRange::unionWith(CR, Smallest)`. Where `a` isn't upper-wrapped and `b` is, the C++ returns
`CR.unionWith(*this, Type)`, whose first three statements then fall through: that's `unionCore b a`. -/
def unionWith (a b : CR w) : CR w :=
  if a.isFullSet || b.isEmptySet then a
  else if b.isFullSet || a.isEmptySet then b
  else if !a.isUpperWrapped && b.isUpperWrapped then unionCore b a
  else unionCore a b

/-! ### What they say about values -/

theorem getPreferredRange_cases (a b : CR w) : getPreferredRange a b = a ∨ getPreferredRange a b = b := by
  unfold getPreferredRange
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem empty_lower : (CR.empty : CR w).lower = 0#w := rfl
theorem empty_upper : (CR.empty : CR w).upper = 0#w := rfl
theorem full_lower : (CR.full : CR w).lower = BitVec.allOnes w := rfl
theorem full_upper : (CR.full : CR w).upper = BitVec.allOnes w := rfl

/-- Neither empty nor full, on `toNat`s. -/
theorem proper_iff (r : CR w) :
    (r.isEmptySet = false ∧ r.isFullSet = false) ↔
      ¬ (r.lower.toNat = r.upper.toNat ∧ r.lower.toNat = 0) ∧
        ¬ (r.lower.toNat = r.upper.toNat ∧ r.lower.toNat = 2 ^ w - 1) := by
  rw [Bool.eq_false_iff, Bool.eq_false_iff, Ne, Ne, CR.isEmptySet_iff, CR.isFullSet_iff]

/-- `a` upper-wrapped if `b` is, on `toNat`s. -/
theorem wrapped_order_iff (a b : CR w) :
    (a.isUpperWrapped = true ∨ b.isUpperWrapped = false) ↔
      (a.upper.toNat < a.lower.toNat ∨ b.lower.toNat ≤ b.upper.toNat) := by
  simp only [CR.isUpperWrapped, BitVec.ult_eq_decide, decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt]

theorem intersectCore_contains {a b : CR w} (ha : a.isEmptySet = false ∧ a.isFullSet = false)
    (hb : b.isEmptySet = false ∧ b.isFullSet = false) (hab : a.isUpperWrapped = true ∨ b.isUpperWrapped = false)
    {x : BitVec w} (hxa : a.contains x = true) (hxb : b.contains x = true) :
    (intersectCore a b).contains x = true := by
  have := a.lower.isLt
  have := a.upper.isLt
  have := b.lower.isLt
  have := b.upper.isLt
  have := x.isLt
  rw [proper_iff] at ha hb
  rw [wrapped_order_iff] at hab
  rw [CR.contains_iff] at hxa hxb
  unfold intersectCore
  simp only [CR.isUpperWrapped, BitVec.ult_eq_decide, BitVec.ule_eq_decide, Bool.not_eq_true',
    decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq, Nat.not_lt]
  repeat' split
  all_goals
    first
    | (rcases getPreferredRange_cases a b with h | h <;> rw [h] <;> simp only [CR.contains_iff] <;> omega)
    | (simp only [CR.contains_iff, empty_lower, empty_upper, BitVec.toNat_ofNat, Nat.zero_mod]; omega)
    | (simp only [CR.contains_iff]; omega)

/-- `intersectWith a b` contains every value both `a` and `b` contain. -/
theorem intersectWith_contains {a b : CR w} {x : BitVec w} (hxa : a.contains x = true)
    (hxb : b.contains x = true) : (intersectWith a b).contains x = true := by
  unfold intersectWith
  split
  · exact hxa
  · next h1 =>
    split
    · exact hxb
    · next h2 =>
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h1 h2
      split
      · next h3 =>
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h3
        exact intersectCore_contains ⟨h2.1, h1.2⟩ ⟨h1.1, h2.2⟩ (Or.inl h3.2) hxb hxa
      · next h3 =>
        have hab : a.isUpperWrapped = true ∨ b.isUpperWrapped = false := by
          revert h3; cases a.isUpperWrapped <;> cases b.isUpperWrapped <;> simp
        exact intersectCore_contains ⟨h1.1, h2.2⟩ ⟨h2.1, h1.2⟩ hab hxa hxb

theorem unionCore_isFullSet {a b : CR w} (ha : a.isEmptySet = false ∧ a.isFullSet = false)
    (hb : b.isEmptySet = false ∧ b.isFullSet = false) (hab : a.isUpperWrapped = true ∨ b.isUpperWrapped = false)
    (h : (unionCore a b).isFullSet = true) (x : BitVec w) : a.contains x = true ∨ b.contains x = true := by
  have := a.lower.isLt
  have := a.upper.isLt
  have := b.lower.isLt
  have := b.upper.isLt
  have := x.isLt
  rw [proper_iff] at ha hb
  rw [wrapped_order_iff] at hab
  rw [CR.contains_iff, CR.contains_iff]
  revert h
  unfold unionCore
  simp only [CR.isUpperWrapped, BitVec.ult_eq_decide, BitVec.ule_eq_decide, Bool.not_eq_true',
    decide_eq_false_iff_not, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Nat.not_lt, beq_iff_eq,
    BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]
  repeat' split
  all_goals
    intro h
    first
    | omega
    | (rcases getPreferredRange_cases (CR.mk a.lower b.upper) (CR.mk b.lower a.upper) with e | e <;> rw [e] at h <;>
        simp only [CR.isFullSet_iff] at h <;> omega)
    | (simp only [CR.isFullSet_iff] at h; omega)

/-- If `unionWith a b` is the full set, every value is in `a` or in `b`. -/
theorem unionWith_isFullSet {a b : CR w} (h : (unionWith a b).isFullSet = true) (x : BitVec w) :
    a.contains x = true ∨ b.contains x = true := by
  unfold unionWith at h
  split at h
  · exact Or.inl (CR.isFullSet_contains h x)
  · next h1 =>
    split at h
    · exact Or.inr (CR.isFullSet_contains h x)
    · next h2 =>
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h1 h2
      split at h
      · next h3 =>
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h3
        exact (unionCore_isFullSet ⟨h1.2, h2.1⟩ ⟨h2.2, h1.1⟩ (Or.inl h3.2) h x).symm
      · next h3 =>
        have hab : a.isUpperWrapped = true ∨ b.isUpperWrapped = false := by
          revert h3; cases a.isUpperWrapped <;> cases b.isUpperWrapped <;> simp
        exact unionCore_isFullSet ⟨h2.2, h1.1⟩ ⟨h1.2, h2.1⟩ hab h x

end Peephole.IS.ICmpB.Range
