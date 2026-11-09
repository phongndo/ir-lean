# Rewrite proofs: chunk 1's G2

How chunk 1's peephole rewrites are proved for every input, how each model is checked against the pinned `opt`, how
the score is counted, and what E3 measures over the proofs. Chunk 1 is InstSimplify, InstCombine,
AggressiveInstCombine and Reassociate at `llvmorg-23.1.3`, and its G2 is every rewrite in them proved for every
input. The rewrites are [the inventory](rewrite-inventory.md)'s, by ID. The proofs are in
[`tests/passes-proofs/peephole`](../tests/passes-proofs/peephole), and [its README](../tests/passes-proofs/peephole/README.md)
has the conventions a family of folds follows. For what any theorem here means, read [trust](trust.md) first.

Facts here were checked on 2026-11-09 on branch `chunk1/g2-core`, at commit `29938ba` and the commits after it that
change only this page and its neighbors, on an Apple silicon Mac with 16 cores and 64 GB, in the dev shell, with Lean
4.35.0 and LLVM 23.1.3, while other lanes' jobs held slots in the machine's pool of heavy jobs.

## What it found

- **8 of chunk 1's 3,000 rewrites are proved for every input,** all of them in InstSimplify's `simplifyAddInst`, the
  worked example: 1.48% of InstSimplify's 540 and 2.62% of its 305 that need only integers.
- **`simplifyAddInst`'s model agrees with the pinned `opt`** on all 6,318 cases compared, 127 of them distinct `add`s
  from LLVM's own regression tests, and every one of its 8 sites fires on some. Two broken models are caught: dropping
  the `nuw` guard of `add nuw x, -1` gives 193 mismatches, all at that site, and dropping the flag guard of the
  sign-mask rule, which no theorem can catch since the rewrite is right without flags, gives 4.
- **The store took all 11 of the worked example's value lemmas:** 4 meet all four rules of the bar and 7 are
  candidates. None was refused as `trivial`. Two were refused until their counterexamples were written.
- **E3 so far:** every one of the 8 proofs uses a stored rewrite lemma, but 7 use only lemmas cut from these same
  proofs, so 1 shows reuse. 21 stored lemmas meet all four rules, 4 of them rewrites. The kernel checks a proof using
  a stored lemma faster than the same proof with the lemma's proof inlined, at the median 0.36 ms against 0.88 ms.
- **Peak memory is what importing costs:** each module of the library peaks between 669 and 725 MiB, and importing
  alone takes 652 MiB. The targets [below](#peak-memory-targets) are 1.25 GB a module.

## What a proof claims

Each fold is a model: a Lean function written from the C++, step by step in its order, one `Step` for each statement
that can end the function, as the [README](../tests/passes-proofs/peephole/README.md) says. Each site has a theorem
named by its ID, such as `Peephole.IS.simplifyAddInst.L609`, and each fold a `sound` theorem built from them. That's
theorem 1 of [the binding approach](binding-approach.md#two-theorems-per-unit): about the model, not the compiled C++.
It says that whenever the step fires, the replacement refines the instruction, `IRLean.Refines`, for every width, every
flag and every operand, poison included, in every run the operands are consistent with.

What it doesn't claim:

| Not claimed | Why |
| --- | --- |
| Vectors, and any type but a scalar integer | `Term` has no vectors, so a model can't express one. A rewrite whose inventory entry needs floating point, memory or calls is blocked, as [below](#the-scoreboard) |
| Anything about `undef` | IRLean has no `undef`. Each theorem assumes no operand reaches one, `hasUndef = false`, as #47's does |
| That LLVM's analyses are right | A fold's theorem holds for every `Oracle` that's `Oracle.Sound`: every answer true in the run. That they are is [PASS-01](llvm-verification-tasks.md#pass-01-analyses-are-sound) |
| Recursive calls into InstSimplify | A model either delegates them, which claims nothing, or takes the recursive simplifier as a parameter with a named soundness hypothesis, listed in the registry's `rests_on` |
| Constant folding, and code no model follows | Each is a `.delegate` step, which claims nothing |
| That the model is the C++ | Written by hand. The comparison with `opt` below is evidence on finitely many cases, not proof |
| The pass around the fold | Replacing uses, deleting dead code, revisiting users and dominance aren't modelled, as in [#47](llvm-cpp-correspondence.md#what-isnt-established) |
| That the compiled code is the model | Theorem 2 of the binding approach, which nothing here attempts |

## How it's checked

[`tests/peephole.py`](../tests/peephole.py) does four things, each through [`tools/irlean`](python.md#the-shared-library).
Its Lean side is [`tests/peephole/Harness.lean`](../tests/peephole/Harness.lean), which it compiles into
`build/peephole` on each run. Nothing proved rests on either.

| Command | What it does | Time today |
| --- | --- | --- |
| `compare [--family F] [--write]` | Each registered model against the pinned `opt`, as [below](#each-model-against-opt). `--write` records the result | 2.6 s for `is-add` |
| `score [--check]` | Chunk 1's G2 per pass, by the rules [below](#the-scoreboard). `--check` fails if a registry lists a site that doesn't count | 2.7 s |
| `measure [--family F]` | E3's numbers, [below](#e3-so-far) | 16.6 s, one Lean process at a time through `tools/measure.py --heavy` |
| `store --family F [--dry-run]` | Offers a registry's `lemmas` to [the lemma store](lemma-store.md), one family at a time | 14 s for `is-add`, `store.py check --write` included |

### Each model against `opt`

`compare` reads every registry in `tests/passes-proofs/peephole/folds`, and for each entry point, each opcode it takes:

1. **Cases from LLVM's own tests.** It reads each regression test of the entry's pass at the pin, such as
   `llvm/test/Transforms/InstSimplify/*.ll`, as `opt -S` prints it, and takes every instruction with that opcode whose
   type is a scalar integer. Its operands become a tree `Term` holds, as deep as five instructions, with one identity
   for one value. An argument, an instruction `Term` can't hold, and one deeper than that become arguments. Two
   instructions of the same shape, with the same sharing, are one case, which keeps the tests it came from.
2. **Generated cases,** as #47 made for `add`: every pair of operands from arguments, constants such as 0, 1, -1 and
   the sign mask, poison, `undef` and simple instructions, and operands built to match each other, such as `~p`,
   `0 - p`, `q - p` and a copy of `p` that isn't `p`, at several widths, with each set of flags the opcode takes. At
   most 12,000 an opcode.
3. **Each case as a function,** whose arguments are its arguments, which computes its instructions, calls a function
   with the root's operands so they stay alive, and returns the root. `opt -passes=<the entry's pass>` runs on all of
   them at once, and what the `ret` names is its answer.
4. **The model's answer,** from its entry point with `Oracle.none`, in one Lean process for all the cases. A fold's
   answer doesn't say which step gave it, so the harness also runs a copy of the fold, and of each definition between
   it and `Peephole.run`, whose `run` answers with the site of the step that fired. A definition it can't copy, a
   recursive or `partial` one, leaves its fold's sites unknown, which the report says.

Each case comes out one of these ways:

| Outcome | When | Fails `compare` |
| --- | --- | --- |
| Matched | The model fires and `opt` answers the same value | |
| Neither folds | Both leave the root | |
| Mismatched | The model fires where `opt` doesn't, or answers another value | Yes |
| Delegated | The model hands over to code it doesn't follow. Not compared | |
| An operand changed first | `opt` changed a line other than the root, so the fold would see other operands. Not compared | |
| An analysis explains it | `opt` folds, the model with `Oracle.none` doesn't, and does with an oracle that answers yes to everything: every bit known zero, every bit known one, or the sign bit known zero | |
| Nothing explains it | `opt` folds and no such oracle makes the model fire. Listed with its IR as the first place to look for a missing step | With `--strict` |

`--write` records each family's result in `tests/passes-proofs/peephole/compared/<family>.json`, schema
`ir-lean.peephole.comparison/1`, with a SHA-256 hash of the registry and of every module of the library the model
imports, the core included. `score` counts a site only if that hash is the sources' now, so a changed model has to be
compared again.

**InstCombine's folds** answer with new IR, not an existing value, so for them `compare` reads only whether each
fires, and leaves comparing the new IR to `compare_new_ir` in `tests/peephole.py`, which answers "not compared" today.
To fill it in: build the function the model's answer gives, its new instructions in place of the root, and check it
against `opt`'s output for the same case, the same after `opt -passes=instsimplify` has normalized both, or else
equivalent by Alive2's `alive-tv`. InstCombine also changes operands, so more of its cases will land in "an operand
changed first".

### `simplifyAddInst` against `opt`

| | Cases |
| --- | ---: |
| All | 9,915 |
| From LLVM's regression tests: the 301 scalar `add`s in 31 of InstSimplify's 190 test files, as 127 distinct cases | 127 |
| Generated | 9,788 |
| Compared | 6,318 |
| Matched | 2,162 |
| Neither folds | 4,156 |
| Mismatched | 0 |
| Delegated: 1,080 to `simplifyXorInst` for `i1`, 576 to the constant folder and 569 to `simplifyAssociativeBinOp` | 2,225 |
| An operand changed first | 1,372 |
| An analysis explains it, or nothing does | 0 |

| Site | Fired, and matched `opt` | Regression tests it fired on |
| --- | ---: | --- |
| `IS.simplifyAddInst.L601` | 369 | `add.ll` |
| `IS.simplifyAddInst.L605` | 368 | None: only generated cases |
| `IS.simplifyAddInst.L609` | 371 | `compare.ll` |
| `IS.simplifyAddInst.L613` | 290 | `add.ll` |
| `IS.simplifyAddInst.L621` | 233 | `add.ll` |
| `IS.simplifyAddInst.L626` | 328 | None: only generated cases |
| `IS.simplifyAddInst.L633` | 24 | None: only generated cases |
| `IS.simplifyAddInst.L637` | 179 | `constantfold-add-nuw-allones-to-allones.ll` |

A test file is listed against a site only if a case from it reached the site with its operands unchanged. Of the 127
cases from LLVM's tests, 10 fire and match, 104 are `add`s that neither the model nor `opt` folds, mostly the operands
of whatever fold the test is about, and 13 delegate. None had an operand changed first.

[`tests/peephole_test.py`](../tests/peephole_test.py) `--tier live` checks the comparison can fail. Dropping `isNUW &&`
from the `add nuw x, -1` step gives 193 mismatches, all at `IS.simplifyAddInst.L637`, among them cases from 11
regression test files, such as `@pow2_decrement` in `AndOrXor.ll`. Dropping `(isNSW || isNUW) &&` from the sign-mask
step gives 4, all at `IS.simplifyAddInst.L633`, all generated. Each mutant is the model without its theorems, put in
front of the library with `PEEPHOLE_OVERLAY`: with them, the first wouldn't compile, and the second would.

## The scoreboard

`score` counts a rewrite as proved for every input only if every one of these holds, and
[`irlean.verdict`](trust.md#where-python-decides-a-verdict) decides it:

- `Peephole.<ID>` is a theorem, and rests on the standard three axioms only: no `sorry`, and nothing from `bv_decide`,
  whose proofs rest on `Lean.ofReduceBool`.
- Its fold's `sound` theorem, named by the registry, is a theorem on the standard three axioms only, and its proof uses
  `Peephole.<ID>`, directly or through any declaration of the library. Lean reads that from the proof terms, not the
  names.
- Its module passes `tests/check_axioms.lean`, which reads it as data, with nothing from `bv_decide`, and `leanchecker`
  replays it, and `lake` has nothing left to build.
- Its model's comparison with `opt` is recorded for the sources it has now, with no mismatch.

A registry lists its sites under `folds`, and each one it didn't prove under `unproved` with why. `score --check`
fails if a site a registry lists as proved doesn't count, if two list one site, or if a registry names an ID the
inventory doesn't have. It writes JSON, schema `ir-lean.peephole.score/1`, to `build/peephole/score.json`, with the ID
of every blocked rewrite by what it waits for, and prints a table. On 2026-11-09:

| Pass | Rewrites | Proved | % | Integers only | Proved of those | % | Need fp (SEM-05) | Need memory (F4) | Need calls |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| InstSimplify | 540 | 8 | 1.48 | 305 | 8 | 2.62 | 189 | 32 | 109 |
| InstCombine | 2,392 | 0 | 0.0 | 1,600 | 0 | 0.0 | 428 | 178 | 381 |
| AggressiveInstCombine | 25 | 0 | 0.0 | 13 | 0 | 0.0 | 3 | 7 | 5 |
| Reassociate | 43 | 0 | 0.0 | 29 | 0 | 0.0 | 13 | 0 | 1 |
| All | 3,000 | 8 | 0.27 | 1,947 | 8 | 0.41 | 633 | 217 | 496 |

"Need calls" waits for the external-calls lane. The three overlap, as in [the inventory](rewrite-inventory.md#totals).
A site proved by `sorry` keeps every site of its fold from counting, since the fold's `sound` theorem then rests on
`sorry` too, and its module fails the axiom audit, which `tests/peephole_test.py --tier live` checks.

## The lemma store and the rewrites

[`tools/store/store.py`](../tools/store/store.py) counts the `Peephole` library's proofs as uses: `check` and `add`
import every module of it, and refuse one that imports the store, since `store/LemmaStore.lean` imports a family's
lemma file once its lemmas are stored. A family's lemma file holds its own counterexamples, as
`LemmaStore.Counter.<lemma>.drop_<hypothesis>` and `.sat`, which the store finds once the file is imported.

Each index entry has an optional `rewrites`: the IDs of the rewrites whose theorems use the lemma, directly or through
theorems of the library that aren't stored themselves, which `check --write` records. A use through another stored
lemma doesn't count: `Peephole.Lemmas.add_refines_of_sum` has no `rewrites`, since the site theorems reach it only
through stored lemmas cut from them.

`tests/peephole.py store --family is-add` offered the registry's 11 lemmas, as family `peephole-is-add`, with the
family's site IDs as their provenance:

| Lemma | Status | Uses | Rewrites |
| --- | --- | ---: | --- |
| `add_comm` | admitted | 4 | L613, L621, L626 |
| `add_none_right` | admitted | 4 | L601, L605 |
| `add_refines_of_sum` | admitted | 5 | |
| `add_sub_cancel_refines` | admitted | 3 | L613, L621 |
| `add_sub_sub_refines` | candidate | 1 | L613 |
| `add_not_left_refines` | candidate | 1 | L626 |
| `add_not_right_refines` | candidate | 1 | L626 |
| `add_intMin` | candidate | 1 | |
| `add_xor_signMask_refines` | candidate | 1 | L633 |
| `eq_zero_of_not_uaddOverflow_allOnes` | candidate | 1 | |
| `add_nuw_allOnes_refines` | candidate | 1 | L637 |

Each is `Peephole.Lemmas.<name>`, and each rewrite is `IS.simplifyAddInst.<line>`. None is `trivial`: `simp`,
`bv_normalize`, `grind` and `decide` each failed to close every one alone within 20,000 heartbeats. The first try refused
`add_refines_of_sum` and `eq_zero_of_not_uaddOverflow_allOnes` as `hypothesis_unwitnessed`, since nothing showed their
hypotheses were needed, and their counterexamples are now at the end of `Peephole/Lemmas/Add.lean`. The store then
held 175 lemmas: 21 admitted and 154 candidates, up from 17 and 147.

## E3 so far

E3, in [Phase 6](roadmap.md#phase-6-the-engine-and-the-lemma-store), asks that over 20 proofs at least half use a
stored lemma, at least 10 lemmas meet all four rules, and a proof using the store checks faster, at the median, than
the same proof without it. `measure` counts the proofs in order, registries by name and each one's sites as it lists
them. There are 8 so far.

| Site | Elaboration and kernel | Kernel alone | Stored rewrite lemmas it uses | Refinement's laws |
| --- | ---: | ---: | --- | --- |
| `L601` | 3.1 ms | 0.22 ms | `add_none_right` | `outcome_ok_ok`, `val_none` |
| `L605` | 3.1 ms | 0.21 ms | `add_none_right` | `outcome_ok_ok`, `val_none` |
| `L609` | 3.4 ms | 0.32 ms | `IRLean.Generic.add_zero` | `outcome_ok_ok`, `refl_val` |
| `L613` | 67.6 ms | 1.68 ms | `add_comm`, `add_sub_cancel_refines`, `add_sub_sub_refines` | `outcome_ok_ok` |
| `L621` | 10.4 ms | 0.25 ms | `add_comm`, `add_sub_cancel_refines` | `outcome_ok_ok` |
| `L626` | 8.8 ms | 0.34 ms | `add_comm`, `add_not_left_refines`, `add_not_right_refines` | `outcome_ok_ok` |
| `L633` | 9.0 ms | 0.82 ms | `add_xor_signMask_refines` | `outcome_ok_ok` |
| `L637` | 2.8 ms | 0.10 ms | `add_nuw_allOnes_refines` | `outcome_ok_ok` |

"Elaboration and kernel" is the time to elaborate the site's theorem, the kernel's check included, with any theorem
named after it, such as `L621_swapped`, one command at a time in one process. "Kernel alone" is the median of 11
checks of its proof again. A lemma counts as used when the proof reaches it directly or through theorems of the
library that aren't stored. Rewrite lemmas are those of `generic-rewrites` and the `peephole-` families; refinement's
laws and LangRef's contracts are counted apart, so reuse isn't inflated by `Refine.outcome_ok_ok`, which every proof
uses.

| E3's criterion | So far |
| --- | --- |
| At least half the proofs use a stored lemma | 8 of 8 use a stored rewrite lemma. Only `L609`'s, `IRLean.Generic.add_zero`, wasn't cut from these same proofs, so 1 of 8 shows reuse |
| At least 10 lemmas meet all four rules | 21 do, 4 of them rewrites, all four `simplifyAddInst`'s |
| A proof using the store checks faster than without it, at the median | Yes: over the 13 pairs of a site and a stored rewrite lemma its proof names, the kernel took 0.36 ms with the lemma and 0.88 ms with the lemma's proof put in its place, and each pair was faster with the store |

The last compares kernel checks only: a proof written without the store would also elaborate the lemma's proof, so it
understates the difference. 8 proofs of one fold aren't E3's 20, and their lemmas were cut from them, so these numbers
say the machinery works, not that the store makes later proofs cheaper. The families now being proved are the first
test of that.

### Peak memory targets

Each module, elaborated alone by `lean -M 4096` with what it imports already built, through `tools/measure.py --heavy`:

| Module | Wall | Peak |
| --- | ---: | ---: |
| `Peephole.Term` | 0.99 s | 725 MiB |
| `Peephole.Match` | 0.60 s | 702 MiB |
| `Peephole.Oracle` | 0.32 s | 669 MiB |
| `Peephole.Fold` | 0.32 s | 673 MiB |
| `Peephole.Lemmas.Add` | 0.31 s | 677 MiB |
| `Peephole.IS.Add` | 0.60 s | 702 MiB |

A file that only imports `Peephole.IS.Add`, or only `Peephole.Oracle`, peaks at 652 MiB, so each module's own
definitions and proofs add 17 to 73 MiB to what importing costs. Proposed, for the library and
[Phase 8](roadmap.md#phase-8-speed):

- **Each module of the library at most 1.25 GB,** one and a half times the largest peak measured, rounded up to
  256 MB. A family's module above it most likely has a proof that should be cut into lemmas.
- **The cap stays at 4 GB a process,** the lakefile's `-M 4096`, which no module should come near. A proof that hits it
  is missing a lemma; the cap isn't raised.
- **Each site's theorem in under a second,** elaboration and kernel included. The slowest today, `L613`, takes 68 ms.

`measure` proposes the per-module figure again from what it measures, in its JSON's `targets`.

## CI

`lake build` builds `Peephole` by default, so CI's setup checks every proof: 2.4 s from nothing on top of `IRLean`
here. Four tests run in ctest, as [testing](testing.md) lists: `peephole_static` in the `rest` job, under a second, and
`peephole_compare`, `peephole_score` and `peephole` in the `semantics` job, 2.6 s, 2.9 s and 9.5 s here. No CI run has
measured them on its 4-core runners yet.

## When a family lands

```console
lake build Peephole
tests/peephole.py compare --family F --write    # commit tests/passes-proofs/peephole/compared/F.json
tests/peephole.py score --check
tests/peephole.py store --family F              # commit store/index.json and store/LemmaStore.lean
```

`store` runs `store.py check --write` after storing, since a family's proofs can give a stored lemma its second use,
and `store.py check` fails on a status the index doesn't record. Families are stored one at a time: the index is one
file.

## Reproducing

In `nix develop`, after `lake build`:

```console
tests/peephole.py compare
tests/peephole.py score --check
tests/peephole.py measure
tests/peephole_test.py --tier static
tests/peephole_test.py --tier live
```

On a shared machine, run each under `tools/measure.py run --heavy`; `measure` takes its own slots for its Lean
processes. Nothing here needs Linux.

## Gaps

- **One fold.** The scoreboard counts `simplifyAddInst`'s 8 sites. Other families are being proved on branches of
  their own, and count once their registries and comparisons land.
- **The comparison is finite.** It covers what LLVM's tests and the generator reach, at a few widths. Vectors,
  constant expressions and `undef` inside instructions aren't generated, and an argument stands for anything deeper
  than five instructions.
- **"An analysis explains it" is a heuristic.** It asks three oracles that answer yes to everything. A fold that fires
  only on particular known bits would show as "nothing explains it", which is reported, not a failure.
- **LLVM's tests reach 5 of `simplifyAddInst`'s 8 sites.** `L605`, `L626` and `L633` fire only on generated cases.
- **InstCombine's new IR isn't compared yet,** only whether each fold fires, as [above](#each-model-against-opt).
- **E3 is measured on 8 proofs** whose lemmas were cut from them.
