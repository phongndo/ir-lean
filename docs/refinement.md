# Refinement

What it means, in `IRLean`, for one function to be a correct replacement for another, what that does and doesn't say
about LLVM, and the API proofs and certificates use. This is SEM-01 of the [task list](llvm-verification-tasks.md). For
what any theorem means, read [trust](trust.md) first.

**This is a relation, not a result.** Nothing here proves any pass correct. It's the statement a certificate about one
instance proves, and the laws that let certified steps compose.

## The relation

[`IRLean/Refine.lean`](../IRLean/Refine.lean), namespace `IRLean`, imported by `IRLean.lean`. It imports only
`IRLean.Basic`.

```lean
class Refine (α : Type) where
  le : α → α → Prop
  trans : ∀ {a b c : α}, le a b → le b c → le a c

def Refines {α : Type} [Refine α] (src tgt : α) : Prop := Refine.le src tgt
```

`Refines src tgt` says `tgt` only does what `src` allows. The instances say what that is for each type ir-lean emits.
The last two rows are memory's, since 2026-11-10, in [`IRLean/MemRefine.lean`](../IRLean/MemRefine.lean):

| Type | `src` allows `tgt` when |
| --- | --- |
| `Val w` | `src` is poison, or `tgt` is the same value |
| `Vec n w`, any `Vector α n` | Lane by lane. A poison lane allows anything in that lane only |
| `α × β`, for a struct | Field by field |
| `Unit`, for `void` | Always |
| `Outcome α`, a run | `src` is undefined: always. `src` stops the model: never. `src` never finishes: `tgt` never finishes. `src` returns `x`: `tgt` returns some `y` that `x` allows |
| `Outcomes α`, a run that makes choices | For every way `tgt` chooses, some way `src` chooses gives a run that allows `tgt`'s. See [choices](#runs-that-make-choices) |
| `Exit α`, how a run that calls outside the module ends | `src` returned `x` with trace `t`: `tgt` returned some `y` that `x` allows, with trace `t`. `src` ended in a call that never came back, or unwound, or was cut off: `tgt` ended the same way, with the same trace. See [calls](calls.md) |
| `Talks α`, a run of a function that calls outside the module | For every way `tgt` chooses, some way `src` chooses gives a run that allows `tgt`'s, watched for any number of calls with effects. The number comes after the source's choice, so one run of `src` has to agree with every prefix of `tgt`'s trace. See [calls](calls.md#refinement) |
| `α → β`, a function | For every input, the same input to both, the results are related. A `Val` input is a value or poison. For a function that calls outside the module, the `World` and the trace before it are inputs too, so both sides face the same world |
| `(vs : VScale) → β vs`, a function in a module with scalable vectors | For every `vscale`, the same on both sides, by `IRLean.Scalable`'s instance. It's a parameter, not a choice: see [scalable vectors](scalable-vectors.md) |
| `PtrVal`, a pointer | `src` is poison, or `tgt` is the same pointer: allocation, offset and tags |
| `Mem`, the memory a run leaves | `Mem.le`: the same allocations, by number, each the same size and kind, the same layout, frame and running calls, and bytes `src`'s allow. See [functions with memory](#functions-with-memory) |

The emitter gives every function that mentions a pointer or touches memory a `Mem` argument, last, and a `Mem` in its
result. Until 2026-11-10 there was no instance for `Mem` or `PtrVal`, so such a function had no `Refines` claim at
all. It has one now, under the simplest relation that's sound, which leaves out a target that allocates differently:
[functions with memory](#functions-with-memory) says what it covers.

Every instance is transitive. Values, vectors, structs and functions into them are also reflexive, as the class
`Refine.Reflexive` says. Runs aren't: a model stop refines nothing, itself included. So for a function into `Outcome`,
`Refines f f` holds exactly when `f` never stops the model on any input, and that's how equality of two functions
becomes refinement.

## Runs that make choices

Since F3, on 2026-11-09, `freeze` of poison is a value, and no longer stops the model. `undef` stays out, by the
[maintainer's decision](roadmap.md#three-decisions-of-2026-11-09) of the same day.

### What LangRef asks

`freeze x` is `x` when `x` isn't poison. Of poison it "returns an arbitrary, but fixed, value of type `ty`", and "all
uses of a value returned by the same `freeze` instruction are guaranteed to always observe the same value, while
different `freeze` instructions may yield different values". A `freeze` that runs twice, in a loop or in a function
called twice, returns two values, and they may differ: loop unrolling and inlining turn such a `freeze` into two
`freeze` instructions, which is only a refinement if each run of it may choose again. #49's
[prototype](undef-freeze.md) settles the rest on straight-line code, choosing once per `freeze` and per run, and shows
which orders of quantifiers certify wrong rewrites.

### The model

- **`IRLean.Choice`** is `List Nat → Nat`: every choice a run makes, fixed in advance, as a number for each place a
  `freeze` can run. A `freeze` of width `w` reads its number modulo `2 ^ w`, so every value of the type is some choice
  (`IRLean.Contract.freeze_none_any`).
- **Places are paths.** A function whose run can make a choice takes one `Choice`, and each of its blocks carries its
  own: the entry block the function's, and each next block `c.sub 0` of the block `c` before it. In a block with `c`,
  the `k`th `freeze` or call to a function that makes choices, counting from 1, reads `c.pick k`, the number at `[k]`,
  if it's a `freeze`, and gives its callee `c.sub k`, the numbers under `[k]`, if it's a call. A floating-point
  operation that can give a NaN is a chooser too, since LangRef leaves a NaN's sign and payload to a choice: it reads
  `c.pick k`, and on a vector lane `i` reads `(c.sub k).pick i`, so each lane chooses on its own
  ([floating point](float.md#nan-payloads-as-a-choice)). So the place a `freeze`
  reads is, for each frame from the outermost, a `0` for each block before the current one and then the call's
  number, and last the `freeze`'s own number. No two `freeze`s a run executes read the same place, and every way of
  choosing a value for each of them is some `Choice`. The outcomes over every `Choice` are exactly the outcomes over
  every way each `freeze` that runs can choose, in loops, calls, recursion and code with memory too.
  `tests/emitter.sh` runs emitted code under chosen `Choice`s to show each of those places is its own.
- **`Val.freeze pick a`** is `a` when `a` is a value, and `some (BitVec.ofNat w pick)` when it's poison. Emitted code
  binds it with `let`, since it can't fail.
- **`IRLean.Outcomes α`** is `Choice → Outcome α`. A function that has a `freeze` or a floating-point operation that
  can give a NaN, or calls one that does, through a pointer too, returns it after its arguments: `def f (x : Val 8) : Outcomes (Val 8) := fun c' => ...`. A cycle of
  calls shares the answer. Every other function is emitted as before, and returns `Outcome α`, so no proof about one
  changes. `c'` is primed so no value's name can be the same.

### Refinement

```lean
instance [Refine α] : Refine (Outcomes α) where
  le a b := ∀ ct, ∃ cs, Refine.le (a cs) (b ct)
```

With the instance for functions around it, `Refines src tgt` says: for every input, for every way the target chooses,
there's a way the source chooses whose run allows the target's. That's the prototype's order: inputs first, the
target's choices for the whole run, then the source's for the whole run, and only then the outcome. The source's
choice comes after the target's because the target's nondeterminism is what any execution may do, and the source's is
the optimizer's to pick. Moving any quantifier certifies a wrong rewrite, as the prototype's
[shortcuts](undef-freeze.md#refinement-and-the-order-of-its-quantifiers) show. A source that's undefined for some way
of choosing allows anything there, since the optimizer may assume it chose that way.

It's transitive. A run that makes choices refines itself where no way of choosing stops the model
(`Refine.outcomes_le_self`). Choosing the same on both sides proves a refinement where it holds
(`Refine.outcomes_of_same`), which is how most proofs go, but it isn't the relation: replacing a frozen poison with a
constant needs the source to choose that constant.

When only one side makes choices, the other is lifted with `Outcomes.det`, the same outcome for every choice, and the
claim is about the lifted function: `Refines src fun x => Outcomes.det (tgt x)`. `tools/binding_check.lean` builds it
that way, and `Refine.outcomes_det_left` and `outcomes_det_right` unfold it.

### Why this, and not something else

- **The prototype's sets.** The prototype's `Run (UVal w)` is a set of results, each a set of values per use. Without
  `undef`, a use sees one value, so that's a set of outcomes, and `Choice → Outcome α` lists the same set with an index.
  Refinement is the same, `∀` of the target's against `∃` of the source's, and every emitted function stays a function:
  given its `Choice`, it runs through `IRLean.run`, the drivers for promises, and every lemma about them, unchanged,
  and code can still be run, as tier-1 proof tests and the differential tests do. On single values the two agree:
  `IRLean.Experimental.UndefFreeze.model_freeze`.
- **One value for each `freeze` instruction, for the whole run.** It gives a `freeze` that runs twice one value, which
  loop unrolling and inlining contradict, so a target could be certified on fewer behaviors than LLVM gives it.
- **Choices keyed by what a block starts from.** Choosing by the block's arguments and memory, instead of by place, gives
  the same outcomes, but needs a `Choice` type for each function, and `Refine` relates two things of one type.

### What it doesn't cover

- `undef`, which stays out: `undef` constants are refused, and reading uninitialized memory gives poison. See
  [trust](trust.md#known-gaps-in-the-model).
- `freeze` of a vector, a pointer or a struct, which ir-lean refuses. LangRef freezes a vector's lanes one by one, and
  gives a pointer with no provenance.
- Running a claim that quantifies over choices. Tier-1 proof tests generate no `Choice`, and `tools/verify.py` can't
  decide `∃` over the source's choices at a witness, so both answer unknown or unsupported there, never a pass. The
  refutations are kernel-checked theorems instead, in `tests/freeze/FreezeModel.lean` and `tests/refine`.

## Functions with memory

SEM-06, F4, in stages. This is what's done, on 2026-11-10: the simplest sound relation, and what it covers. What's
left is [below](#what-it-leaves-out).

### The claim

A function with memory is `f args (m : Mem) : Outcome (ρ × Mem)`. `Refines src tgt` says: for every argument and
every memory, **the same for both**, the source's run allows the target's, and two runs that return are related in
what they return and in the memory they leave. `RefineCases.memory_claim` and `memory_result` pin that.

`Mem.le m m'`, the source's memory allowing the target's:

| Part of a memory | Rule | Why |
| --- | --- | --- |
| Allocations | The same ones, by number, each with the same size, and the same flags for constant, heap and stack | A pointer is an allocation's number and an offset, and pointers are compared as they are, so both sides have to number allocations the same |
| A poison byte | Allows any byte | Poison is refined by anything |
| An uninitialized byte | Allows any byte but poison | LLVM 23 reads it as `undef`, which a value refines and poison doesn't. The model reads it as poison. This is what both readings allow |
| A byte of a value, or of a stored pointer | Allows only itself | |
| `next`, the number the next allocation gets | The same | See [what it leaves out](#what-it-leaves-out) |
| `base`, the layout, and `failAlloc`, which `malloc`s fail | The same | They're oracles a theorem quantifies over, and both sides face the same ones |
| The frame, and the calls that are running | The same frame. The same calls, each having written at least what the source's has, and with what `initializes` covers written the same | What a call has written decides whether a read through a `writeonly` pointer is poison, and what `initializes` didn't write goes back to uninitialized when the call ends |

`Byte.le`'s laws, `Mem.le.next_eq`, and `Refine.ptr_some` pin each rule, and `tests/memory_refine.sh` changes four of
them in a copy and checks the law stops.

### A claim says where the source has an answer

`Refine.le` has a source that stops the model allow nothing, so that two functions that both stop aren't called
equal. With memory that bites at once. Every load and store checks the promises of the calls that are running, and
stops the model where LangRef leaves one open, such as an access in a call of a `memory(none)` function, and a load
stops on bytes it can't read as its type. `Mem` ranges over every memory, with any calls running and any bytes. So a
function that touches memory stops the model on some memory, and doesn't refine itself:
`RefineCases.memory_claim_needs_its_guard` proves it of one store, and `MemoryRefine.unguarded_claim_is_false` of a
right rewrite.

So a claim about memory is guarded:

```lean
theorem store_overwritten_right :
    Refines (fun p a b m => (store_overwritten_right_ir.src p a b m).answered) store_overwritten_right_ir.tgt
```

`Outcome.answered` reads a model stop as undefined behavior, and nothing else: a claim about `(src x m).answered`
makes none where the model has no answer for the source, and is `Outcome.Sim`, [the cut lemma](#the-cut-lemma)'s
relation, everywhere (`Refine.answered_iff`). The guard is on the source only. A target that stops the model where
the source returns still isn't allowed.

The guard is in the statement, so a reader sees it, and it doesn't make a claim empty by itself: a claim holds
vacuously only where its source has no answer, and how much that is can be proved.
`store_overwritten_right_answers` and `store_forwarded_right_answers` prove their sources have an answer on every
memory no running call restricts, `Mem.Unrestricted`. `Mem.check_ne_model` and `Mem.storeInt_ne_stop` are the
lemmas. A load can still stop there, on bytes that hold a pointer.

### What it covers

A rewrite that leaves the allocations what they were: stores removed, forwarded, or made to store a value where the
source stored poison, loads removed or merged, and code between them rewritten. These are proved of what ir-lean
emits, for every pointer, value and memory, in [`tests/memory_refine`](../tests/memory_refine/MemoryRefine.lean):

| Case | Verdict | By | Alive2 |
| --- | --- | --- | --- |
| `store_overwritten_right`: a store that's overwritten before anything reads it, removed | Refines | `Mem.storeInt_overwritten` | Correct |
| `store_forwarded_right`: a load after a store, replaced by what was stored | Refines | `Mem.loadInt_of_storeInt` | Correct |
| `load_repeated_right`: two loads of the same bytes, to one | Refines | The memory is the same at both | Correct |
| `stored_value_refined_right`: `store (add nuw %a, 1)` to `store (add %a, 1)` | Refines | `Mem.le.storeInt`: the bytes differ, and the source's allow the target's | Correct |
| `store_removed_wrong`: a store that a load reads, removed | Doesn't, from a cell of zeros: 5 against 0 | | Incorrect |
| `stores_swapped_wrong`: two stores through pointers that may be the same, swapped | Doesn't, with both the same: a 2 left against a 1 | | Incorrect |
| `load_added_wrong`: a load from memory the source never touched, added | Doesn't, with nothing allocated: the target is undefined | | Incorrect |
| `store_added_wrong`: a store, added | Doesn't: a 5 left where the source left 0 | | Incorrect |
| `alloca_removed_no_claim`: an `alloca` nothing reads, removed with its store | **No claim**: the relation doesn't hold | | Correct |

The two rules behind the first two are theorems about any memory, tracked calls and promises included:

- **`Mem.storeInt_overwritten`**: two stores through one pointer, with nothing between them, are allowed to be the
  second alone.
- **`Mem.loadInt_of_storeInt`**: a load after a store through the same pointer, at the same width and alignment, a
  whole number of bytes, gives what was stored, or is undefined, or has no answer. It's never another value.

### What it leaves out

- **A target that allocates differently.** `Mem.le` asks both memories for the same `next`, so a target with one
  `alloca` fewer, or more, isn't related, whatever its memory holds. `alloca_removed_no_claim` proves `Refines` fails
  for removing an `alloca` nothing reads, which LLVM does and Alive2 calls correct. That theorem is about the
  relation, and no tool may read it as a counterexample. It isn't a matter of ignoring `next`: after the two sides
  allocate differently, every later allocation has a different number on each, so their pointers differ, and the
  oracles `base` and `failAlloc`, which are indexed by that number, give each side different addresses and
  failures. Relating them takes a renaming of allocations carried through values and memory, with the target's
  oracles quantified before the source's, as `freeze`'s choices are. And arguments range over pointers to
  allocations that don't exist yet, which a source's own `alloca` could then be mistaken for, so it also takes a
  precondition that arguments point into the memory they come with. None of that is here. It's stage 3 of F4.
- **A call outside the module that passes a pointer or touches the function's memory.** Still refused by the
  emitter, as [calls](calls.md#calls-that-touch-memory) says. The relation it waited for is here, and what the
  world's answer says about memory isn't.
- **What a promise tracks, beyond the rule above.** A target that writes less than the source, to bytes that end up
  the same, isn't related inside a call that tracks writes: removing `store (load %p), %p` is right, and has no
  claim on a memory with such a call running.
- **A load after bytes were refined in kind.** A store keeps the relation of the memories it's given
  (`Mem.le.storeInt`). A load doesn't always (`Mem.le.loadInt`): where the source's bytes were poison and the target's
  can't be read as the load's type, as a pointer stored where the source stored a poison one and then loaded as an
  integer, the target stops the model, so there's no claim.
- **Each [known gap](trust.md#known-gaps-in-the-model) in the model's memory still has its side.** The relation
  doesn't close them. [What it says about LLVM](#what-it-says-about-llvm) lists which side each is wrong for, and
  what a claim has to assume.

## The API

What other code may rely on. These names are stable. A change to any of them is a request to this lane.

| Name | Says |
| --- | --- |
| `IRLean.Refine`, `IRLean.Refines` | The class and the relation |
| `Refine.val_none`, `val_some`, `val_iff` | Poison allows anything, a value only itself |
| `Refine.vector_iff`, `prod_iff`, `unit`, `fn` | The other instances, unfolded |
| `Refine.outcome_ok`, `outcome_ok_ok`, `outcome_ub`, `outcome_stop`, `outcome_none` | Each kind of run in the source |
| `Refine.refl_val`, `Refine.Reflexive`, `Refines.refl` | Reflexivity, where it holds |
| `Refine.outcome_le_self_iff`, `Refines.self_iff` | A run, or a function of one argument, refines itself exactly when it never stops the model |
| `Refine.outcomes_iff`, `outcomes_det`, `outcomes_det_left`, `outcomes_det_right` | Runs that make choices, unfolded, and with one side lifted from a run that makes none |
| `Refine.outcomes_of_same`, `outcomes_le_self` | Choosing the same on both sides is enough, and a run that never stops the model refines itself |
| `Refine.exit_done`, `exit_done_done`, `exit_halted`, `exit_unwound`, `exit_cut`, `exit_lift`, `talks_iff`, `talks_of_same` | How a run that calls outside the module ends, unfolded, with both sides lifted from runs that don't by `Exit.lift`, and runs of functions that do, unfolded, and with the same choice on both sides. In [`IRLean/World.lean`](../IRLean/World.lean) |
| `Refines.trans` | Refinements compose |
| `Refines.of_eq` | Equal functions refine each other where the source refines itself. With `self_iff`, `tools/binding.py`'s `ir_instance_equivalence` claim implies `ir_instance_refinement`'s |
| `Refine.andThen_mono` | Replacing a run by one it allows, before a continuation that keeps refinement, keeps refinement |
| `Refine.val_map_mono`, `val_map₂_mono` | An operation that gives poison for poison keeps refinement, as `Contract.Strict₁` and `Strict₂` say |
| `Outcome.Sim`, `Next.Rel`, and `Outcome.Sim.ok`, `ok_iff`, `ub`, `stop`, `refl`, `mono`, `trans`, `andThen`, `jump`, `ret`, `br`, `run` | [The cut lemma](#the-cut-lemma): a run allowed wherever the model has an answer for the source, what two blocks do last, and how both compose. In [`IRLean/Cut.lean`](../IRLean/Cut.lean) |
| `Outcome.Sim.promised`, `runPromised`, `promised_dropped`, `stay_sim`, `runPromised_ne_stop`, `stayFuel`, `stay_of_stayFuel`, `stayFuel_of_stay` | The same between blocks, for runs under a promise to progress. In [`IRLean/CutPromised.lean`](../IRLean/CutPromised.lean) |
| `Refine.le_iff_sim`, `sim_of_le`, `le_of_sim`, `Refines.of_sim`, `Refines.sim_cut`, `Refines.ok_of_fn` | `Refine.le` on runs is `Outcome.Sim` and the source not stopping the model, and what a cut's proof gives the block that holds it |
| `Outcome.answered`, `Refine.answered_iff`, `answered_of_ne_stop`, `answered_of_le` | A run with a model stop read as undefined, for a claim that covers only the inputs the model has an answer for |
| `run_ne_stop`, `jump_ne_stop`, `ret_ne_stop`, `br_ne_stop`, `andThen_ne_stop`, `runFuel`, `run_of_runFuel`, `runFuel_of_run`, `Next.run`, `run_eq`, `andThen_ret_run`, `andThen_assoc` | A run stops the model only where a block does, `run` for a bounded number of blocks, and a run as its first block and then the rest |
| `Refine.PoisonLeast`, `Mono.*`, `refine_mono` | The model's operations keep refinement, one lemma each, and the tactic that chains them. In [`IRLean/Mono.lean`](../IRLean/Mono.lean) |
| `Byte.le`, `Alloc.le`, `Call.le`, `Mem.le`, their `refl` and `trans`, `Byte.le.poison_le`, `uninit_le_iff`, `not_uninit_le_poison`, `val_le_iff`, `ptr_le_iff`, `Mem.le.next_eq`, `alloc`, `gone`, `addr` | [Memory's relation](#functions-with-memory), and the laws that pin it. In [`IRLean/MemRefine.lean`](../IRLean/MemRefine.lean) |
| `Refine.ptr_none`, `ptr_some`, `ptr_iff`, `mem_iff`, `Mem.lift` | The instances for a pointer and a memory, unfolded, and a function with no memory as one with |
| `Mem.storeInt_overwritten`, `Mem.loadInt_of_storeInt` | A store that's overwritten can go, and a load after a store gives what was stored |
| `Mem.le.storeInt`, `storeVec`, `loadInt`, `loadInt_some`, `gep`, `gep_eq`, `alloca`, `withFrame`, `toVal`, `nonnull`, `aligned`, `dereferenceable`, `observeAddress`, and `Mem.le.write`, `access`, `check`, `visible`, `collect`, `isRunning` | [Memory's operations keep the relation](#with-memory), and what that takes |
| `Mem.le.call`, `endCall`, `enterCall`, `tag`, and `Mem.enterCall`, `Mem.endCall`, `Mem.call_eq` | A function's promises about memory keep the relation, and `Mem.call` as its body inside the call and then the call's end |
| `Mono.loadInt`, `Mono.gep`, `Mono.noundefPtr`, `Mono.call` | The same, for the same memory on both sides |
| `Mem.intBytes`, `storeInt_eq`, `storeInt_ok`, `storeInt_ok_of_ok`, `storeInt_error_or_ok`, `storeInt_write_self`, `loadInt_write_self`, `access_ok_iff`, `access_write_self`, `check_write`, `check_congr`, `write_write_le`, `Mem.Alloc.overlay` | What a store needs and leaves, for proofs about any memory |
| `Mem.check_ne_model`, `Mem.storeInt_ne_stop`, `Mem.unrestricted_write`, `unrestricted_storeInt`, `andThen_ne_stop_of` | Where no running call restricts memory, a store has an answer |

The unfolding lemmas are `Iff.rfl` or `trivial`, so a proof through them proves the same statement as one unfolding the
instances, and doesn't depend on what the instances are named.

## The cut lemma

A cut of a function is a slice of its instructions, with the values that go in and come out. A search proves a
rewrite on a cut, since that's what it can afford to look at, and the claim that matters is about the function. The
lemma that joins them, since 2026-11-10: **if a cut is refined by its replacement, the function with the cut replaced
refines the original.** It's in [`IRLean/Cut.lean`](../IRLean/Cut.lean), stated over what the emitter emits, which has
two levels, so it has two halves.

| Half | Says | Where emitted code has it |
| --- | --- | --- |
| `Outcome.Sim.andThen` | A run replaced by one it allows, before a continuation that keeps the relation for every pair of related results, gives related runs | Inside a block, where instructions are chained with `andThen` and `let` |
| `Outcome.Sim.run` | Two functions whose blocks, where related by `R`, step to blocks related by `R` or return related results, have related runs from any two related blocks | Between blocks, which `run` drives. The source and the target each have a `Block` type of their own, and `R` says which blocks correspond and how their live values are related |
| `Refines.sim_cut` | A cut's proof, a `Refines` between the cut and its replacement as functions of the values that go in, gives `Outcome.Sim` between the cut on the source's values and the replacement on the target's | The block that holds the cut |
| `Outcome.Sim.promised`, in [`IRLean/CutPromised.lean`](../IRLean/CutPromised.lean) | `Outcome.Sim.run`, for two functions under a promise to progress: their related blocks also have to be under the promise together | A function marked `mustprogress`, or with a loop marked `llvm.loop.mustprogress`, which is what clang makes of a C loop. The emitter runs it with `runPromised` |

Both halves are about `Outcome.Sim r a b`, which is `Refine.le`'s rule for a run, for results related by `r`, with one
change: a source that stops the model allows anything, where `Refine.le` has it allow nothing. That's what makes it
compose. The code after a cut is the same on both sides, and where it stops the model on the source's values there's
no claim to keep. The stop is accounted for once, at the end: `Refine.le a b` is `Outcome.Sim Refine.le a b` and `a`
not stopping the model (`Refine.le_iff_sim`), so a whole function's theorem also proves its source never stops the
model, as `run_ne_stop` reduces to its blocks, or it says `Outcome.answered`, which takes those inputs out of the
claim, as a claim [about memory](#a-claim-says-where-the-source-has-an-answer) does.

Three things a proof has to supply, each needed, as `tests/cut/CutCases.lean` proves with a case where the conclusion
fails without it:

- **The rest of the function keeps refinement.** The same code on both sides isn't enough: it runs on a value where
  the source had poison, and `returned` on an integer, say, stops the model on a value that isn't its argument
  (`rest_has_to_keep_refinement`). [`IRLean/Mono.lean`](../IRLean/Mono.lean) proves it of the model's integer and
  vector operations, `select`, `noundef`, `llvm.assume`, `switch` and branches, one lemma each, and the tactic
  `refine_mono` chains them. Floating point, `IRLean/Lanes.lean`'s lane-wise forms and x86's intrinsics have no lemma
  yet, so code after a cut that uses one needs its own, unless the cut's replacement returns the same values, where
  the two sides are the same run.
- **The replacement keeps refinement of its inputs.** A cut's proof is at one input for both. In the function the two
  get different inputs, the target's refining the source's, since code before the cut may already have run its
  replacement: in a loop, the round before (`replacement_has_to_keep_refinement`).
- **The blocks stay in step.** `Outcome.Sim.run` is a lockstep simulation: the cut can be in a loop, and can't change
  which blocks run (`blocks_have_to_stay_related`). A cut that spans blocks, or a replacement with other control flow,
  isn't covered.
- **Under a promise to progress, both sides are under it together.** A source that never finishes without breaking
  its promise allows only a target that never finishes, and a target that broke one there would be undefined instead
  (`CutPromisedCases.promise_has_to_agree`). A target that drops the promise needs nothing more
  (`Outcome.Sim.promised_dropped`), and one that adds it isn't covered, and isn't right.

### Its uses

| Theorem | Cut | Function | Rests on |
| --- | --- | --- | --- |
| `Q5Kernel.q5_kernel`, in [`tests/cut/Q5Kernel.lean`](../tests/cut/Q5Kernel.lean) | llama.cpp's q5_0 bit-spreading slice, [`llama_q5_bitspread.ll`](../tests/real/llama_q5_bitspread.ll), whose proof is `LlamaBitspread.same` | [`tests/cut/q5_kernel.ll`](../tests/cut/q5_kernel.ll): a loop whose body holds the slice's six instructions, word for word, joins the low nibbles and adds the bytes up, and the same loop with the slice's two-instruction replacement | The standard axioms and the 32 `bv_decide` axioms of the slice's proof. The kernel's proof adds none |
| `Q5KernelMemory.q5_kernel_memory`, in [`tests/cut/Q5KernelMemory.lean`](../tests/cut/Q5KernelMemory.lean) | The same slice | [`tests/cut/q5_kernel_memory.ll`](../tests/cut/q5_kernel_memory.ll): that loop with memory. It loads each round's word through a pointer, and stores what it adds up through another | The same, and no more |
| `CutCases.drop_nuw_loop` | `add nuw %x, 3` to `add %x, 3`, which is refined and not equal | [`tests/cut/drop_nuw_loop.ll`](../tests/cut/drop_nuw_loop.ll): a loop that divides and `xor`s what the cut gives | The standard axioms |
| `CutPromisedCases.drop_nuw_promised` | The same | [`tests/cut/drop_nuw_promised.ll`](../tests/cut/drop_nuw_promised.ll): that loop, marked `llvm.loop.mustprogress` on both sides | The standard axioms |
| `ClangSum.clang_sum`, in [`tests/cut/ClangSum.lean`](../tests/cut/ClangSum.lean) | `mul %x, 3` to `add (shl %x, 1), %x` | [`tests/cut/clang_sum.ll`](../tests/cut/clang_sum.ll): **a function as clang compiled it**, from [`clang_sum.c`](../tests/cut/clang_sum.c) at `-O1`, a loop that adds up three times each word it loads. It has `memory(argmem: read)`, a pointer that's `noundef`, `readonly`, `nofree` and `captures(none)`, and a loop marked `llvm.loop.mustprogress` | The standard axioms |

`q5_kernel` is `Refines q5_kernel_ir.src q5_kernel_ir.tgt`, on every input, poison included. Its proof knows one thing
about the slice, `slice : Refines LlamaBitspreadIR.src LlamaBitspreadIR.tgt`, so it's the slice's proof and the lemma.
It isn't a theorem about `ggml_vec_dot_q5_0_q8_0`: the fixtures have the kernel's shape, [with](#with-memory) and
without its loads, and not its floating point or its vector loads, and
[the Q5 rewrite](llama-q5.md#what-is-proved-and-checked) says what that leaves trusted.
`drop_nuw_loop_converse` proves the lemma is one-way: from 253 the loop with `add nuw` returns poison where the one
with `add` returns 0.

### With memory

The lemma is the same: `Outcome.Sim.run` and `Outcome.Sim.andThen` don't care what a block carries, and a function
with memory carries a `Mem` among its live values. What memory adds is what the code after a cut has to keep, the
relation between the two sides' memories as well as their values, and `IRLean/MemRefine.lean` proves the model's
memory operations keep it. `q5_kernel_memory` is
`Refines (fun dst qh n m => (src dst qh n m).answered) tgt`: for every pointer and count, on every memory the model
has an answer for.

| Operation | Lemma | Says |
| --- | --- | --- |
| `store` of an integer, of a vector | `Mem.le.storeInt`, `storeVec` | Related memories, pointers and values give related stores. A value stored where the source stored poison leaves bytes the source's allow |
| `load` of an integer | `Mem.le.loadInt`, `loadInt_some`, and `Mono.loadInt` for the same memory | Related memories and pointers give related loads, **or the target's stops the model**: where the source read poison and the target's bytes hold a pointer. A load that gives a value in the source gives it in the target |
| `getelementptr` | `Mem.le.gep`, `gep_eq`, and `Mono.gep` | The same pointer, or poison for a poison pointer or offset |
| `alloca`, and a function's frame | `Mem.le.alloca`, `withFrame` | Both sides give the new allocation the same number, and free the same ones |
| `ptrtoint` and pointer comparison, `nonnull`, `align`, `dereferenceable`, `noundef` on a pointer | `Mem.le.toVal`, `nonnull`, `aligned`, `dereferenceable`, `Mono.noundefPtr` | The layout is the same on both sides |
| A look at a pointer's address | `Mem.le.observeAddress` | For the same pointer on both sides only: one the target has for the source's poison could carry a tag that stops the model |
| A function's promises about memory, `memory(...)`, and a pointer argument's, `readonly`, `captures` and the rest | `Mem.le.call`, `endCall`, `enterCall`, `Mono.call` for the same memory, and `Mem.le.tag` | Both sides give the call the same number and its pointer the same tag, and what `initializes` covers and nothing wrote goes back to uninitialized on both |

Not proved to keep the relation yet: `load` and `store` of a pointer, `load` of a vector, `getelementptr` with several
indices, `memset`, `memcpy`, `llvm.lifetime`, `malloc`, `free`, `strlen`, and of what attributes add, the range
`initializes` names, `returned` and a `noalias` result. Code after a cut that uses one needs its lemma first, or a cut
that leaves the memory and the values it reads the same, where it's the same run on both sides: that's how
`q5_kernel_memory` and `clang_sum` handle their loads, by relating the two loops' blocks with their memories equal,
since their cuts write nothing.

`clang_sum` is the lemma on what clang emits, not on a loop written for it. `tests/cut.sh` compiles `clang_sum.c`
again and checks the function and its attributes are the fixture's `@src`, to the letter. Its proof goes through
everything the emitter wraps such a function in: `noundef` on the arguments, `Mem.call` for `memory(argmem: read)`,
the tag on its pointer, and the run under its loop's promise. Alive2 has no verdict on it: it doesn't take `nofree`.

### What it doesn't cover

- A target that adds a promise to progress, or two sides whose blocks aren't under one together.
- A function whose run makes choices or calls outside the module, which return `Outcomes` or `Talks`.
- Floating point, `IRLean/Lanes.lean`'s lane-wise forms and x86's intrinsics after a cut, and the memory operations
  [above](#with-memory) with no lemma.
- A cut that changes control flow, or spans blocks.
- A cut that takes several values in: `Refines.sim_cut` is for one, and a cut emitted with more arguments is used
  through `Refine.sim_of_le` and `Outcome.Sim.trans` by hand.
- A cut that allocates differently from its replacement, as [memory's relation](#what-it-leaves-out) doesn't.

## What it says about LLVM

`Refines src tgt` is a theorem about `IRLean`'s semantics of two functions. It says the same of LLVM only where all of
these hold. Each is a gap between the model and LLVM, and a certificate that relies on one has to say so.

| Assumption | Where it holds | Where it doesn't |
| --- | --- | --- |
| The source has no more undefined behavior or poison in the model than in LLVM, and the target no less | Integer operations, by the [contracts](llvm-semantic-contracts.md) and `tests/opcheck.py`. Undefined behavior in the source allows anything, so a source the model makes undefined where LLVM doesn't could hide a wrong target | Memory, in the four places [below](#memorys-gaps-each-with-its-side). Since 2026-11-10 memory has an instance, and a claim about it rests on these not arising, each on the side named |
| No argument is `undef` | Arguments that are `noundef` in the source: passing `undef` or poison there is undefined, which the model checks | Any other argument. A `Val` is a value or poison, never `undef`, so `and i8 %x, 0` refines `xor i8 %x, %x` in the model, where LLVM lets `xor` of an `undef` give anything. `tools/binding.py` refuses such a function as `undef_argument` |
| A promise to progress or to return means what LangRef says | `mustprogress`, `willreturn` and `llvm.loop.mustprogress`, as [trust](trust.md#promises-to-progress) reads them: a run that never finishes under one is undefined, unless it waits on a call LangRef allows never to return. Since SEM-07, on 2026-11-08 | Where LangRef doesn't settle it, the model stops, which allows nothing in a source, or the emitter refuses the function |
| A source that stops the model is never certified | For a run that makes no choices, always: a model stop allows nothing. For one that makes choices, the way the source chooses that allows the target never stops the model, but under another way it may: if it's undefined under some way, it allows anything, as LLVM's source does, whatever it does under the rest | It makes the relation incomplete where the model stops, as [trust](trust.md#what-the-model-does-at-its-edges) lists. Until F3 that included `freeze` of poison, so inserting a `freeze`, which is right in LLVM, wasn't a refinement in the model. Since F3 it is: `freezeInserted` |
| A `freeze` that runs twice may choose two values | Each `freeze` a run executes reads its own place in the run's `Choice`, as [above](#runs-that-make-choices) | Nowhere known. It's a reading of LangRef, which unrolling and inlining depend on |
| A source that never finishes needs a target that doesn't either | Always: without a promise LLVM allows a run that never finishes, and nothing else in its place | Under a promise the run isn't `none` but undefined, which allows anything, so deleting a loop under `mustprogress` refines. `loopDeletedUnderPromise` in the tests proves it, and `tests/binding.py` binds a real `loop-deletion` run |

### Memory's gaps, each with its side

The model's memory differs from LLVM's in ways [trust](trust.md#known-gaps-in-the-model) lists. For a refinement
each is wrong on one side only: more undefined behavior or poison than LLVM is wrong in a source, since it allows a
target LLVM's source doesn't, and less is wrong in a target. The relation closes none of them. So a claim about
memory says something of LLVM only where the side it's wrong for doesn't do it:

| Gap | The model has | Wrong in | A claim holds of LLVM where |
| --- | --- | --- | --- |
| A read of an uninitialized byte gives poison, where LLVM 23 gives `undef` | More poison | A source | The source reads no uninitialized byte, or uses what it read only where poison and `undef` do the same. Or under the reading LLVM is moving to, where uninitialized memory is poison. The byte relation itself is right under both: an uninitialized byte doesn't allow a poison one |
| A stack object is gone once its function returns, so a load through a pointer to it is undefined, where LangRef makes it poison | More undefined behavior | A source | The source doesn't load through a pointer to a returned function's `alloca` |
| `inbounds` on a freed allocation is poison, where LangRef only makes an access undefined | More poison | A source | The source doesn't step a pointer into a freed allocation with `inbounds` |
| `tail` and `musttail` promise the callee doesn't touch the caller's `alloca`s, and the model doesn't check it | Less undefined behavior | A target | The target makes no `tail` call whose callee reaches the caller's stack |
| A global another module defines isn't in `initial` | Nothing, for a claim | Neither | Always: a claim is for every memory, the ones that hold the global among them |
| `Mem.base` is unconstrained: allocations can overlap, start at 0, or wrap | More layouts than exist | Neither | Always: a claim for every layout holds for the real ones |
| A stored pointer read as an integer, or integer bytes as a pointer, stops the model | No answer | Neither | Always: a source that stops the model has no claim there, and a target that does isn't allowed |

Nothing checks the first four on a claim yet: no tool refuses a source that loads from an `alloca` it never
initialized. That's the rest of SEM-06, and until it lands a certificate about memory has to say which of these it
rests on, as one about integers says its arguments aren't `undef`.

Equality isn't refinement. Until F3, duplicating a `freeze`, which is wrong in LLVM, gave two functions equal in the
model, since both stopped at a frozen poison. Since F3 their two `freeze`s choose apart, so the functions differ
(`freezeDuplicated_ne`) and don't refine (`freezeDuplicated`). Any other model stop still makes two functions equal
where both stop, which is why `tools/binding.py`'s equivalence claim also says the source never stops the model.

Composition is only what the laws above say. Transitivity chains instances whose target is the next one's source.
Whether a pipeline's runs are such a chain, and functions a pass adds, removes or inlines, are for whoever binds the
runs ([binding](llvm-proof-binding.md#what-isnt-bound-yet)). Nothing here relates two loops, or two calls, by their
bodies.

## Unsupported

These have no claim, or a claim that says nothing about LLVM, and stay that way until their own task lands:

- of memory (the rest of SEM-06): a target that allocates differently from its source, a call outside the module
  that passes a pointer or touches the function's memory, `inttoptr` and exposure, and the four gaps whose side a
  claim has to assume, [above](#memorys-gaps-each-with-its-side). A function that only loads, stores and steps
  pointers has a claim, [guarded](#a-claim-says-where-the-source-has-an-answer);
- `undef`, as a constant, which ir-lean refuses, or as an argument (SEM-02), which stays out of the model by the
  decision of 2026-11-09;
- `freeze` of a vector, a pointer or a struct, which ir-lean refuses (the rest of SEM-03);
- floating point's intrinsics but `llvm.fabs`, `llvm.copysign`, `llvm.is.fpclass` and the saturating
  conversions, which ir-lean refuses until SEM-05's later [slices](float.md#the-slices). A float is its bits, so
  `Refines` on one is bit for bit, as LLVM's is, and a NaN result is a choice;
- a run under a promise to progress that LangRef doesn't settle, which stops the model: a recursive function's, so
  deleting infinite recursion can't be certified, and one waiting on a promised callee that waits itself
  ([trust](trust.md#promises-to-progress)).

## Tests

`tests/refine.sh`, the `refine` test in [testing](testing.md), checks this in about 37 s, one Lean process at a time,
each capped at 2 GB and 300 s, from copies in a temporary directory:

- `IRLean/Refine.lean` builds with warnings as errors, and it and `IRLean/Promise.lean` rest on the standard axioms
  only, and `leanchecker` replays them.
- [`tests/refine/RefineCases.lean`](../tests/refine/RefineCases.lean) proves, of functions written by hand in the shape
  ir-lean emits, that right rewrites refine: `add %x, 0` to `%x`, dropping `nuw`, poison to a value, removing undefined
  behavior, a value in a poison lane, and since F3, inserting a `freeze`, `freeze (freeze %x)` to `freeze %x`,
  removing a `freeze` of a `noundef` value or of one that can't be poison, `freeze poison` to any constant, and
  duplicating a `freeze` of a value. And that known-wrong ones don't, each at the input it fails on: a wrong constant,
  an added `nuw`, a value to poison, removing a `freeze` of a value that can be poison, a duplicated `freeze`, at a
  way the target chooses that no way the source chooses allows, added undefined behavior, swapped lanes, a target that
  never finishes and a source that never finishes. It also proves the laws on these, and that `and i8 %x, 0` to
  `xor i8 %x, %x` is one, which LLVM's `undef` makes wrong. For a loop that never ends on odd
  inputs, it proves the promise is broken exactly there (`promiseBrokenOnSomeInput`), that deleting the loop refines
  under `mustprogress` and doesn't without it, and that dropping the promise refines and adding it doesn't.
- [`tests/refine/RefineClaims.lean`](../tests/refine/RefineClaims.lean) checks that memory has an instance: a
  memory, a pointer, and a function with either, and not a bare `Ptr`, a byte, an allocation or a call. Until
  2026-11-10 it checked that memory had none. What the instance claims is pinned in `RefineCases.lean`:
  `memory_claim`, `memory_result`, `pointer_result`, and `memory_claim_needs_its_guard` with
  `memory_claim_with_its_guard`. It also checks that the claim `tools/binding_check.lean` builds with `mkAppM` is the
  same `Expr` a certificate elaborates.
- A proof of the wrong constant, [`must_fail/WrongConstantProof.lean`](../tests/refine/must_fail/WrongConstantProof.lean),
  fails with an error that isn't a resource limit.
- Four edits to a copy of the model each stop the case guarding them: in `IRLean/Int.lean`, `freeze` keeping poison
  stops `freezeRemoved`, `freeze` always choosing 0, as VeIR's does, stops `freezeDuplicated`, and `add` ignoring
  `nuw` stops `addedNuw`; in `IRLean/Promise.lean`, a broken promise never finishing instead of being undefined stops
  `countPromised_odd`. That copy leaves out `Promise.lean`'s laws,
  which pin the same choice and would fail first.

`tests/binding.py` binds a real `instcombine` run with an `ir_instance_refinement` certificate,
[`tests/binding/AddZeroRefines.lean`](../tests/binding/AddZeroRefines.lean), and refuses an equivalence certificate
offered for that claim. It also binds a real `loop-deletion` run that deletes a loop only `mustprogress` makes
deletable, with [`tests/binding/LoopDeletedRefines.lean`](../tests/binding/LoopDeletedRefines.lean), which proves the
function after refines the one before because the loop breaks the promise wherever it never ends. Since F3 it binds
four real `instcombine` runs on `freeze` as refinements: one that keeps a `freeze` of a shift that can be poison, and
drops an `add %a, 0` after it, which until F3 both sides stopped on, `freeze (freeze y)` to `freeze y`, a `freeze` of
a `noundef` argument dropped, and a frozen poison made 0. In the last two only the source makes choices, and the
claim lifts the target with `Outcomes.det`.

`tests/freeze.sh`, the `freeze` test, checks F3 on what ir-lean emits, in about 6 s: each rewrite in `tests/freeze`,
and each in `tests/undef_freeze/alive2` with a `freeze` and no `undef`, ten in all, is translated, and
[`tests/freeze/FreezeModel.lean`](../tests/freeze/FreezeModel.lean) proves each one's verdict on the standard axioms,
replayed by `leanchecker`: right ones refine, and wrong ones don't, including dropping the `freeze` of a branch
condition, where the target branches on poison. A proof that the duplicated `freeze` refines fails, and Alive2, with
`undef` inputs off, gives each of the ten the theorem's verdict.

`tests/memory_refine.sh`, the `memory_refine` test, checks [memory's relation](#functions-with-memory) on what
ir-lean emits, in about 8 s:

- `IRLean/MemRefine.lean` rests on the standard axioms alone, and `leanchecker` replays it.
- The nine rewrites in `tests/memory_refine` translate, and
  [`MemoryRefine.lean`](../tests/memory_refine/MemoryRefine.lean) proves each one's verdict, about both its
  functions as ir-lean emitted them, on the standard axioms, replayed: four refine, four don't, and one has no claim.
- A proof that removing a store a load reads refines,
  [`must_fail/StoreRemovedRefines.lean`](../tests/memory_refine/must_fail/StoreRemovedRefines.lean), fails with an
  error of its own.
- Four edits to a copy of `IRLean/MemRefine.lean` each stop the law that pins the rule: an uninitialized byte allowing
  poison, a byte of a value allowing any byte, a pointer allowing any pointer, and memories not agreeing on `next`.
- Alive2, with `undef` inputs off, gives eight cases the theorem's verdict, and `alloca_removed_no_claim` the one its
  second line says, correct, where the model has no claim.

```sh
nix develop -c tools/measure.py run --heavy --label memory_refine --max-tree-rss-mb 6000 --timeout 1800 -- \
  tests/memory_refine.sh build/ir-lean
```

On 2026-11-10 that printed 18 lines of `ok` and exited 0 in 7.2 s, with a peak of 1,527 MiB.

`tests/cut.sh`, the `cut` test, checks [the cut lemma](#the-cut-lemma) on what ir-lean emits, in about 40 s:

- `IRLean/Cut.lean`, `IRLean/CutPromised.lean` and `IRLean/Mono.lean` rest on the standard axioms alone, and
  `leanchecker` replays them.
- `tests/cut/q5_kernel.ll` and `q5_kernel_memory.ll` hold every instruction of the slice fixture's `@src` and `@tgt`,
  as text. `clang_sum.ll`'s `@src` and its attributes are what the pinned clang makes of `clang_sum.c`, compiled
  again. The five loops and the slice translate.
- `Q5Kernel.lean`, `Q5KernelMemory.lean`, `ClangSum.lean`, `CutPromisedCases.lean` and `CutCases.lean` build with
  warnings as errors against those modules and replay. The last three rest on the standard axioms alone, and each
  kernel on exactly as many `bv_decide` axioms as its slice's proof, 32.
- Seven wrong versions stop a proof with an error of its own: the cut's proof with its sides swapped,
  [`must_fail/AddNuwLoop.lean`](../tests/cut/must_fail/AddNuwLoop.lean), and a function with its target changed and
  translated again under the unchanged proof. Without memory: a replacement that reads the wrong bit, and a loop that
  skips a round. With memory: the wrong bit, a loop that loads the next word, and one that stores through the other
  pointer. As clang compiled it: a target that adds up five times each word.
- Four edits to a copy of `IRLean/Cut.lean` each stop the lemma that pins them: a source that never finishes allowing
  anything, a result allowing a target with none, the guard hiding every run, and a block that returns matching one
  that jumps.
- Alive2, with `undef` inputs off, gives four loops the theorem's verdict, and has none for `clang_sum`, as its
  second line says. It unrolls a loop a fixed number of times, so its verdict is for runs that short, and the
  theorems are for every run.

```sh
nix develop -c tools/measure.py run --heavy --label cut --max-tree-rss-mb 6000 --timeout 1800 -- \
  tests/cut.sh build/ir-lean
```

On 2026-11-10 that printed 29 lines of `ok` and exited 0 in 37.6 s, with a peak of 1,591 MiB.

A `¬ Refines` theorem is about the model. It never says a rewrite is wrong in LLVM, and no test here counts one as a
counterexample to a pass.

## Where this came from

The relation was drafted, uncommitted, on `research/prove-llvm-optimizations` at `28c2364`, as `IRLean/Refine.lean`
with sha256 `fe538b7d62b72c3b171936af007886d33a30174b0259e158893e7e2cc5a1ba10`. That draft had the instances above,
reflexivity for `Val` and the unfolding lemmas, and no transitivity. Its rules are unchanged here. What's new is
transitivity as part of the class, `Refine.Reflexive`, and the laws. Its tactic, `IRLean/RefineTactic.lean`, and the
scorer's `checkRefines` in `tests/check_axioms.lean` aren't part of this, and are left on that branch. The scorer is
rebuilt as [`tests/passes.py`](passes.md), which binds equivalence certificates and doesn't prove refinement yet.
