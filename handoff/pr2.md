This is the base of chunk 1's G2: every rewrite in #79's inventory, proved for every input, with each proof in the lemma store under its rewrite ID. It adds four things:
- a Lean library that models LLVM's folds;
- one family, InstSimplify's `simplifyAddInst`, as the worked example;
- the harness that checks each model against the pinned `opt`;
- the scoreboard, and the store's link to rewrites.

The other InstSimplify families come in their own PRs, one per family, on top of this one.

## The library: `tests/passes-proofs/peephole`, lake library `Peephole`

The core modules:
- `Peephole.Term`:
  - `Term w`: an operand as LLVM's matchers see it, with an `id` for each instruction's address, so `m_Specific` compares identities, as the C++ does;
  - `Repl w`: what a fold answers with;
  - `Env`, `denote`, `Consistent` and `Repl.eval`.
- `Peephole.Match`: `PatternMatch.h`'s matchers, and what a match says about values.
- `Peephole.Oracle`: the analyses folds ask, and `Oracle.Sound`, which says every answer is true in the run. That is PASS-01's to prove, so each theorem rests on it by name.
- `Peephole.Fold`: a fold as a list of `Step`s in the C++'s order. `run_sound` builds a fold's theorem from one theorem per step.

`Peephole.IS.Add` models `simplifyAddInst` step by step, as #47 did, and has one theorem per rewrite, named by its ID (`Peephole.IS.simplifyAddInst.L609` and the others). Seven of its eight rewrites count. L605 (`X + undef` to `undef`) doesn't: without `undef`, only poison reaches its step, and L601 takes poison first. `simplifyAddInst.sound` is BIND's theorem 1 for it: every value the model returns refines the `add`, for every width, flag and recursion budget, poison included, and for no input that reaches `undef`.

`lake build` builds `Peephole` (it's now a default target), and each Lean process is capped at 4 GB.

## The harness: `tests/peephole.py`

- **`compare`**:
  - Takes each registered fold's entry point and runs it in Lean with `Oracle.none`. It runs on the instructions LLVM's own regression tests hold and on generated ones, comparing each answer with the pinned `opt`.
  - A model that fires where `opt` doesn't, or answers otherwise, fails the command.
  - It records which folds each compared case reached, and which test files exercised each site. A fold counts as reached only from a case that matched or where neither side folded. A site counts as exercised only by cases with no `undef` anywhere.
  - A case counts as "an analysis explains it" only if the model, under that oracle, gives `opt`'s answer.
- **`score`**: chunk 1's G2 per pass. A rewrite counts only if all of these hold:
  - `Peephole.<ID>` exists and rests on the standard three axioms (audited, and replayed by `leanchecker`);
  - its fold's `sound` theorem uses it, as Lean's proof terms show;
  - a comparison with `opt` actually ran that fold, with no mismatch, recorded for the sources it has now;
  - its proof covers the types the inventory says it needs;
  - it was reached by some case with no `undef`, if it was reached at all.

  Proved sites that miss one of these are reported, not counted.
- **`measure`**: E3's numbers, which are per-site proof time, each module's peak memory through the heavy-job pool, and which stored lemmas each proof uses. Reuse of rewrite lemmas is reported apart from reuse of refinement's laws.
- **`store`**: offers a family's value lemmas to the store, one family at a time.

`tools/store/store.py check` now counts uses in `Peephole`. Each index entry gains `rewrites`, the IDs of the rewrites whose theorems use it. A `Peephole` module that imports the store's root is refused.

## `simplifyAddInst`, measured on 2026-11-09 on a 16-core Mac

- **Compare:**
  - 9,915 cases: 127 from the scalar `add`s in 31 of InstSimplify's 190 test files, the rest generated.
  - 6,318 compared and 0 mismatched. The 7 counted sites were all exercised by `opt`. L605 fired 368 times, each time with an `undef` operand.
  - Dropping the `nuw` guard of L637 gives 193 mismatches; dropping L633's flag guard gives 4.
- **Store:** its 11 value lemmas are admitted as 4 admitted and 7 candidates, none refused. The store now holds 175 lemmas.
- **E3:**
  - Each site's proof takes 2.8 to 68 ms, and each module peaks at 669 to 725 MiB.
  - Over 13 site–lemma pairs, the kernel's median check is 0.36 ms with the stored lemma and 0.88 ms with its proof inlined.
  - Only L609 reuses a lemma that wasn't cut from these same proofs: #48's `add_zero`. One family can't show the store making later proofs cheaper; the families after this one can.
- **Score:** InstSimplify, 7 of 541 rewrites (1.29%), and 7 of its 300 integer-only rewrites (2.33%), all 7 exercised by `opt`. The other passes are at 0.

## Tests and docs

- New ctest tests:
  - `peephole_static`: Python only, under a second, in `rest`.
  - `peephole_compare`, `peephole_score` and `peephole` (the harness can fail: two broken models and a `sorry`), about 15 s together, in `semantics`.
  - `tests/store_test.py` gains the `rewrites` link and the import refusal.
- `docs/rewrite-proofs.md` holds the method, what a proof claims and doesn't, the scoring rules and E3. It also has rows in `docs/testing.md`, and the store's changes are in `docs/lemma-store.md`.
- PASS-03 and AUTO-02 are now "in progress" with gate waivers.

Run locally, on macOS, after merging `main` at `e17a1ef`:
- `lake build`, then `lake build --wfail Peephole`;
- `tools/store/store.py check`: 175 lemmas, 0 refused;
- `tests/peephole.py compare` and `score --check`;
- `tests/peephole_test.py --tier static` and `--tier live`;
- `tests/llvm_rewrites.py check` and `tests/llvm_scope.py check --offline`;
- ruff, ty, rumdl, gersemi, cmakelint and editorconfig-checker on what this touches.

Ruff reports I001 in `tools/prooftest/bench.py`; it was already on `main`. `tests/store_test.py` passed on the branch before the merge. The full ctest suite is left to CI.

Nothing here is Linux-only. One difference across hosts: on a case-insensitive disk, as on macOS, ruff takes `irlean` imports to be local because of `IRLean/`, and sorts them differently than on Linux CI. `tests/peephole_test.py` is arranged to sort the same on both.

Independent review: 2 rounds, approved. It found:
- L605 counted although only `undef` reaches it;
- a fold credited as reached from a case that was delegated, not compared.

Both are fixed, each with a regression.
