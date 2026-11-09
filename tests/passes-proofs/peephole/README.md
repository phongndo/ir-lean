# Chunk 1's rewrites, proved for every input

Lean models of the folds in InstSimplify, InstCombine, AggressiveInstCombine and Reassociate at `llvmorg-23.1.3`, and
proofs that each rewrite they make is right for every input: G2 for chunk 1. The rewrites, and their IDs, are
[`tests/llvm_scope/rewrites`](../../llvm_scope/rewrites), from [the rewrite inventory](../../../docs/rewrite-inventory.md).
`lake build Peephole` checks every proof, with each Lean process capped at 4 GB.

## The core

| Module | What it is |
| --- | --- |
| `Peephole.Term` | `Term w`, an operand as a matcher sees it, with an `id` for each instruction's address. `Repl w`, what a fold answers with. `Env`, a run's values, and `denote`, `Consistent` and `eval` |
| `Peephole.Match` | `PatternMatch.h`'s matchers on `Term`, and what a match says about values |
| `Peephole.Oracle` | The analyses folds ask, as an `Oracle`, and `Oracle.Sound`: every answer true in the run |
| `Peephole.Fold` | A fold as a list of `Step`s in the C++'s order, `run`, and `run_sound`, which builds a fold's theorem from one per step |
| `Peephole.Lemmas.*` | Facts about values that rewrites rest on, at every width: candidates for the lemma store |

`Peephole.IS.Add`, InstSimplify's `simplifyAddInst`, is the worked example the others follow.

## Conventions

- **One step per site.** A fold's model is `<fold>.steps`, a list of `Step`s, one for each C++ statement that can end
  the function, in the C++'s order, each with the C++ comment above it. A step that rewrites fires with its ID from
  the inventory, such as `"IS.simplifyAddInst.L609"`. A forward to another fold modelled here is a step too; one to
  code not modelled is `.delegate`, which claims nothing.
- **One theorem per site, named by its ID:** `Peephole.IS.simplifyAddInst.L609`. It says the replacement refines the
  instruction, `IRLean.Refines`, whenever the step fires, for every width, flag and operand, poison included.
- **One theorem per fold:** `<fold>.sound`, built with `run_sound` from the sites' theorems. It's theorem 1 of
  [the binding approach](../../../docs/binding-approach.md#two-theorems-per-unit): it's about the model, and a proof
  about the compiled C++ meets it at the model's name and type.
- **Hypotheses a reader should notice:** operands are `Consistent` with the run, have no `undef` (`hasUndef = false`),
  and analyses' answers are `Oracle.Sound`, which is PASS-01's to prove. Scalars only: no vectors.
- **Entry points:** a fold InstSimplify or InstCombine calls on an instruction has `<fold>.onInst (o : Oracle) :
  {w : Nat} → Term w → Result w`, which the comparison with `opt` runs.
- **Facts about values** go in `Peephole/Lemmas/<Family>.lean`, for every width, with no hypothesis a counterexample
  can't show is needed, and are offered to the lemma store. Look in the store first: `tools/store/store.py lookup`.
  No `bv_decide` and no `sorry`: every module rests on the standard three axioms.
- **A family's registry,** `folds/<family>.json`, names its modules, its entry points and the opcodes they take, each
  fold's `sound` theorem and sites, and each site it didn't prove, with why.

## How it's checked

`lake build Peephole` checks the proofs. [`tests/peephole.py`](../../peephole.py) checks the rest, as
[rewrite proofs](../../../docs/rewrite-proofs.md) says:

- `compare --family F --write` runs each entry point's model against the pinned `opt` on LLVM's regression tests and
  generated cases, and records the result in `compared/<family>.json`, keyed by a hash of the model's sources, with
  the folds its compared runs reached. A changed model has to be compared again.
- `score --check` counts a site only if its theorem rests on the standard axioms, its fold's `sound` theorem uses it,
  its family's comparison is current, a compared run reached its fold, and, for a site the inventory says needs more
  than integers, the registry's `"covers": {"<ID>": [...]}` names those types. It fails if a registry lists a site
  whose proof or comparison doesn't hold; a proved site whose fold no comparison reached, or an integer instance, is
  reported and not counted.
- `store --family F` offers the registry's `lemmas` to the lemma store, with the counterexamples in the family's lemma
  file, `LemmaStore.Counter.<lemma>.drop_<hypothesis>` and `.sat`.
