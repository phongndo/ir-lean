import IRLean.ExecMem

/-! # Memory for proof tests

What a tier-1 proof test ([`tools/prooftest`](../tools/prooftest)) generates for a function that takes memory, and
what an equivalence property compares. `docs/proof-tests.md#memory` has how they're used.

A property names memory through these, so its statement is about `Mem`, as every theorem is:

- `Buffer n`: the bytes of an allocation, at most `n` of them.
- `Pointer b`: a pointer into the allocation holding buffer `b`, `offset` bytes from its start. Each allocation
  `place` makes starts at an address `Mem.spacedOut` aligns to `2 ^ 32`, so `offset` is how far the pointer is from
  any alignment a load or a vector asks for.
- `Length p`: a length that fits in `b` past pointer `p`.
- `place m bufs`: `m` with each buffer in a writable allocation of its own, made by `Mem.addGlobal`, buffer `i` as
  allocation `m.next + i`. `Pointer.into p m i` is `p` into buffer `i` there.

Tier 1 runs a property on `ExecMem` instead, which `placeExec` builds: `toMem_placeExec` says it's `place`, read
back. The rest of what makes that run a run on `Mem` is in `IRLean/ExecMem.lean`.

`Same` is what an equivalence property claims of two runs: the same result, and the same memory, as a caller that
held the memory both started from sees it. The property claims it where the reference `Answers` and `Returns`, and
the other function `Answers`, three hypotheses. An input where the reference is undefined says nothing, and tier 1
counts it as not meeting the hypotheses. One where either stops the model says nothing either, since the model
doesn't know what LLVM does there, so tier 1 counts it apart, and never passes a property with one. -/

namespace IRLean.Ptf

/-- The bytes of an allocation, at most `n` of them. -/
structure Buffer (n : Nat) where
  bytes : List (BitVec 8)
  fits : bytes.length ≤ n

/-- The first `n` bytes of `l`. -/
def Buffer.ofList (n : Nat) (l : List (BitVec 8)) : Buffer n :=
  ⟨l.take n, by simp only [List.length_take]; omega⟩

/-- A pointer into the allocation holding `b`, `offset` bytes from its start. -/
structure Pointer {n : Nat} (b : Buffer n) where
  offset : Nat
  fits : offset ≤ b.bytes.length

/-- `k` bytes into `b`, or its end if that's sooner. -/
def Pointer.ofNat {n : Nat} (b : Buffer n) (k : Nat) : Pointer b :=
  ⟨min k b.bytes.length, Nat.min_le_right _ _⟩

/-- A length that fits in `b` past `p`. -/
structure Length {n : Nat} {b : Buffer n} (p : Pointer b) where
  val : Nat
  fits : p.offset + val ≤ b.bytes.length

/-- `k`, or the bytes left past `p` if that's fewer. -/
def Length.ofNat {n : Nat} {b : Buffer n} (p : Pointer b) (k : Nat) : Length p :=
  ⟨min k (b.bytes.length - p.offset), by have := p.fits; omega⟩

/-- The length as the `i64` a function takes. -/
def Length.toVal {n : Nat} {b : Buffer n} {p : Pointer b} (l : Length p) : Val 64 :=
  some (BitVec.ofNat 64 l.val)

/-- A buffer's bytes as `Mem.addGlobal` takes them. -/
def init (bytes : List (BitVec 8)) : Array Nat := (bytes.map (·.toNat)).toArray

/-- `m` with each of `bufs` in a writable allocation of its own, from allocation `block` on. -/
def placeFrom (m : Mem) (block : Nat) : List (List (BitVec 8)) → Mem
  | [] => m
  | b :: rest => placeFrom (m.addGlobal block b.length false (init b)) (block + 1) rest

/-- `m` with each of `bufs` in a writable allocation of its own: buffer `i` is allocation `m.next + i`. -/
def place (m : Mem) (bufs : List (List (BitVec 8))) : Mem := placeFrom m m.next bufs

/-- `p`, into buffer `i` of `place m bufs`. -/
def Pointer.into {n : Nat} {b : Buffer n} (p : Pointer b) (m : Mem) (i : Nat) : PtrVal :=
  some ⟨m.next + i, BitVec.ofNat 64 p.offset, []⟩

/-- `placeFrom`, on `ExecMem`. -/
def placeExecFrom (x : ExecMem) (block : Nat) : List (List (BitVec 8)) → ExecMem
  | [] => x
  | b :: rest => placeExecFrom (x.addGlobal block b.length false (init b)) (block + 1) rest

/-- `place`, on `ExecMem`. -/
def placeExec (x : ExecMem) (bufs : List (List (BitVec 8))) : ExecMem := placeExecFrom x x.next bufs

theorem toMem_placeExecFrom (x : ExecMem) (block : Nat) (bufs : List (List (BitVec 8))) :
    (placeExecFrom x block bufs).toMem = placeFrom x.toMem block bufs := by
  induction bufs generalizing x block with
  | nil => rfl
  | cons b rest ih => simp only [placeExecFrom, placeFrom, ih, ExecMem.toMem_addGlobal]

/-- The memory tier 1 runs on is the memory the property names. -/
theorem toMem_placeExec (x : ExecMem) (bufs : List (List (BitVec 8))) :
    (placeExec x bufs).toMem = place x.toMem bufs :=
  toMem_placeExecFrom x x.next bufs

/-! ### Comparing runs -/

/-- Whether two bytes are the same: the same value, both uninitialized, both poison, or the same byte of the same
pointer. -/
def sameByte : Byte → Byte → Bool
  | .uninit, .uninit => true
  | .poison, .poison => true
  | .val a, .val b => a == b
  | .ptr p i, .ptr q j => decide (p = q) && i == j
  | _, _ => false

/-- Whether `m` and `m'` hold the same as each other in every allocation `m₀` has: whether it's there, its size,
its flags and its bytes. Allocations made since `m₀` aren't compared, and nor are the bytes of one that's constant
in `m₀`, which the model makes writing undefined. -/
def sameMem (m₀ m m' : Mem) : Bool :=
  (List.range m₀.next).all fun block =>
    match m.allocs block, m'.allocs block with
    | none, none => true
    | some a, some a' =>
      a.size == a'.size && a.readonly == a'.readonly && a.heap == a'.heap && a.stack == a'.stack &&
        ((m₀.allocs block).any (·.readonly) || (List.range a.size).all fun i => sameByte (a.bytes i) (a'.bytes i))
    | _, _ => false

/-- Whether two runs from `m₀` end the same way: the same result and the same memory, as `sameMem` compares it,
both undefined, for any reasons, both stopping the model for the same reason, or both never finishing. -/
def same {α : Type} [DecidableEq α] (m₀ : Mem) : Outcome (α × Mem) → Outcome (α × Mem) → Bool
  | some (.ok (a, m)), some (.ok (a', m')) => decide (a = a') && sameMem m₀ m m'
  | some (.error (.undefined _)), some (.error (.undefined _)) => true
  | some (.error (.model r)), some (.error (.model r')) => decide (r = r')
  | none, none => true
  | _, _ => false

/-- Two runs from `m₀` end the same way, as `same` says. -/
abbrev Same {α : Type} [DecidableEq α] (m₀ : Mem) (r r' : Outcome (α × Mem)) : Prop := same m₀ r r' = true

/-- Whether a run ends without stopping the model. -/
def answers {α : Type} : Outcome α → Bool
  | some (.error (.model _)) => false
  | _ => true

/-- The run ends without stopping the model: it returns, it's undefined, or it never finishes. -/
abbrev Answers {α : Type} (r : Outcome α) : Prop := answers r = true

/-- Whether a run returns. -/
def returns {α : Type} : Outcome α → Bool
  | some (.ok _) => true
  | _ => false

/-- The run returns: it isn't undefined, doesn't stop the model, and finishes. -/
abbrev Returns {α : Type} (r : Outcome α) : Prop := returns r = true

end IRLean.Ptf
