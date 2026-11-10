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

`Refines src tgt` says `tgt` only does what `src` allows. The instances say what that is for each type ir-lean emits for
code without memory:

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

There's no instance for `Mem`, `Ptr` or `PtrVal`. The emitter gives every function that mentions a pointer or touches
memory a `Mem` argument and a `Mem` in its result, so such a function has no `Refines` claim at all, rather than one
under rules nobody has checked.

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

The unfolding lemmas are `Iff.rfl` or `trivial`, so a proof through them proves the same statement as one unfolding the
instances, and doesn't depend on what the instances are named.

## What it says about LLVM

`Refines src tgt` is a theorem about `IRLean`'s semantics of two functions. It says the same of LLVM only where all of
these hold. Each is a gap between the model and LLVM, and a certificate that relies on one has to say so.

| Assumption | Where it holds | Where it doesn't |
| --- | --- | --- |
| The source has no more undefined behavior or poison in the model than in LLVM, and the target no less | Integer operations, by the [contracts](llvm-semantic-contracts.md) and `tests/opcheck.py`. Undefined behavior in the source allows anything, so a source the model makes undefined where LLVM doesn't could hide a wrong target | Memory, where the model has more undefined behavior than LLVM, and so has no instance |
| No argument is `undef` | Arguments that are `noundef` in the source: passing `undef` or poison there is undefined, which the model checks | Any other argument. A `Val` is a value or poison, never `undef`, so `and i8 %x, 0` refines `xor i8 %x, %x` in the model, where LLVM lets `xor` of an `undef` give anything. `tools/binding.py` refuses such a function as `undef_argument` |
| A promise to progress or to return means what LangRef says | `mustprogress`, `willreturn` and `llvm.loop.mustprogress`, as [trust](trust.md#promises-to-progress) reads them: a run that never finishes under one is undefined, unless it waits on a call LangRef allows never to return. Since SEM-07, on 2026-11-08 | Where LangRef doesn't settle it, the model stops, which allows nothing in a source, or the emitter refuses the function |
| A source that stops the model is never certified | For a run that makes no choices, always: a model stop allows nothing. For one that makes choices, the way the source chooses that allows the target never stops the model, but under another way it may: if it's undefined under some way, it allows anything, as LLVM's source does, whatever it does under the rest | It makes the relation incomplete where the model stops, as [trust](trust.md#what-the-model-does-at-its-edges) lists. Until F3 that included `freeze` of poison, so inserting a `freeze`, which is right in LLVM, wasn't a refinement in the model. Since F3 it is: `freezeInserted` |
| A `freeze` that runs twice may choose two values | Each `freeze` a run executes reads its own place in the run's `Choice`, as [above](#runs-that-make-choices) | Nowhere known. It's a reading of LangRef, which unrolling and inlining depend on |
| A source that never finishes needs a target that doesn't either | Always: without a promise LLVM allows a run that never finishes, and nothing else in its place | Under a promise the run isn't `none` but undefined, which allows anything, so deleting a loop under `mustprogress` refines. `loopDeletedUnderPromise` in the tests proves it, and `tests/binding.py` binds a real `loop-deletion` run |

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

- memory, pointers, provenance and every function that uses them (SEM-06);
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

`tests/refine.sh`, the `refine` test in [testing](testing.md), checks this in about 25 s, one Lean process at a time,
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
- [`tests/refine/RefineClaims.lean`](../tests/refine/RefineClaims.lean) checks that memory has no instance, and that
  the claim `tools/binding_check.lean` builds with `mkAppM` is the same `Expr` a certificate elaborates.
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

A `¬ Refines` theorem is about the model. It never says a rewrite is wrong in LLVM, and no test here counts one as a
counterexample to a pass.

## Where this came from

The relation was drafted, uncommitted, on `research/prove-llvm-optimizations` at `28c2364`, as `IRLean/Refine.lean`
with sha256 `fe538b7d62b72c3b171936af007886d33a30174b0259e158893e7e2cc5a1ba10`. That draft had the instances above,
reflexivity for `Val` and the unfolding lemmas, and no transitivity. Its rules are unchanged here. What's new is
transitivity as part of the class, `Refine.Reflexive`, and the laws. Its tactic, `IRLean/RefineTactic.lean`, and the
scorer's `checkRefines` in `tests/check_axioms.lean` aren't part of this, and are left on that branch. The scorer is
rebuilt as [`tests/passes.py`](passes.md), which binds equivalence certificates and doesn't prove refinement yet.
