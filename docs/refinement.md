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
| `α → β`, a function | For every input, the same input to both, the results are related. A `Val` input is a value or poison |

There's no instance for `Mem`, `Ptr` or `PtrVal`. The emitter gives every function that mentions a pointer or touches
memory a `Mem` argument and a `Mem` in its result, so such a function has no `Refines` claim at all, rather than one
under rules nobody has checked.

Every instance is transitive. Values, vectors, structs and functions into them are also reflexive, as the class
`Refine.Reflexive` says. Runs aren't: a model stop refines nothing, itself included. So `Refines f f` holds exactly when
`f` never stops the model on any input, and that's how equality of two functions becomes refinement.

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
| The target makes no promise the model trusts | A target without `mustprogress` or `willreturn` | A target that spins under one is undefined in LLVM, and runs forever in the model, which a source that runs forever allows. `tools/binding.py` refuses such a target as `trusted_promise` |
| A source that stops the model is never certified | Always: a model stop allows nothing | It makes the relation incomplete. Inserting a `freeze` is right in LLVM, and isn't a refinement in the model, since the target stops at `freeze` of poison |
| A source that never finishes needs a target that doesn't either | Always | It's stricter than LLVM, which lets a `mustprogress` source that never finishes do anything. So deleting such a loop can't be certified |

Equality isn't refinement. Duplicating a `freeze` is wrong in LLVM, and the two functions are equal in the model, since
both stop at a frozen poison. They don't refine, since the source stops. `freezeDuplicated` in the tests proves both.

Composition is only what the laws above say. Transitivity chains instances whose target is the next one's source.
Whether a pipeline's runs are such a chain, and functions a pass adds, removes or inlines, are for whoever binds the
runs ([binding](llvm-proof-binding.md#what-isnt-bound-yet)). Nothing here relates two loops, or two calls, by their
bodies.

## Unsupported

These have no claim, or a claim that says nothing about LLVM, and stay that way until their own task lands:

- memory, pointers, provenance and every function that uses them (SEM-06);
- `undef`, as a constant, which ir-lean refuses, or as an argument (SEM-02);
- `freeze` of poison, a model stop, and any rewrite inserting or moving one (SEM-03);
- floating point, which ir-lean refuses (SEM-05);
- `mustprogress` and `willreturn` as promises, which the model trusts instead of checking (SEM-07).

## Tests

`tests/refine.sh`, the `refine` test in [testing](testing.md), checks this in about 10 s, one Lean process at a time,
each capped at 2 GB and 300 s, from copies in a temporary directory:

- `IRLean/Refine.lean` builds with warnings as errors, rests on the standard axioms only, and `leanchecker` replays it.
- [`tests/refine/RefineCases.lean`](../tests/refine/RefineCases.lean) proves, of functions written by hand in the shape
  ir-lean emits, that right rewrites refine: `add %x, 0` to `%x`, dropping `nuw`, poison to a value, removing undefined
  behavior, a value in a poison lane. And that known-wrong ones don't, each at the input it fails on: a wrong constant,
  an added `nuw`, a value to poison, `freeze` to poison, a duplicated `freeze`, added undefined behavior, swapped
  lanes, a target that never finishes and a source that never finishes. It also proves the laws on these, that
  inserting a `freeze` isn't a refinement in the model, which is a limit of the model and not a counterexample, and
  that `and i8 %x, 0` to `xor i8 %x, %x` is one, which LLVM's `undef` makes wrong.
- [`tests/refine/RefineClaims.lean`](../tests/refine/RefineClaims.lean) checks that memory has no instance, and that
  the claim `tools/binding_check.lean` builds with `mkAppM` is the same `Expr` a certificate elaborates.
- A proof of the wrong constant, [`must_fail/WrongConstantProof.lean`](../tests/refine/must_fail/WrongConstantProof.lean),
  fails with an error that isn't a resource limit.
- Two edits to a copy of `IRLean/Int.lean` each stop the case guarding them: `freeze` keeping poison stops
  `freezeDuplicated`, and `add` ignoring `nuw` stops `addedNuw`.

`tests/binding.py` binds a real `instcombine` run with an `ir_instance_refinement` certificate,
[`tests/binding/AddZeroRefines.lean`](../tests/binding/AddZeroRefines.lean), and refuses an equivalence certificate
offered for that claim.

A `¬ Refines` theorem is about the model. It never says a rewrite is wrong in LLVM, and no test here counts one as a
counterexample to a pass.

## Where this came from

The relation was drafted, uncommitted, on `research/prove-llvm-optimizations` at `28c2364`, as `IRLean/Refine.lean`
with sha256 `fe538b7d62b72c3b171936af007886d33a30174b0259e158893e7e2cc5a1ba10`. That draft had the instances above,
reflexivity for `Val` and the unfolding lemmas, and no transitivity. Its rules are unchanged here. What's new is
transitivity as part of the class, `Refine.Reflexive`, and the laws. Its tactic, `IRLean/RefineTactic.lean`, the
scorer, `tests/passes.py`, and the scorer's `checkRefines` in `tests/check_axioms.lean` aren't part of this, and are
left on that branch.
