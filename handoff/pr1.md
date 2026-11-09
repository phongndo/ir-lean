INV-04 for chunk 1: every rewrite in InstSimplify, InstCombine, AggressiveInstCombine and Reassociate at `llvmorg-23.1.3`, each with a stable ID and a source location, derived from the pinned source. This is the denominator of chunk 1's G2. Nothing here proves a rewrite.

## The split rule

C++ doesn't say where one rewrite ends and the next begins, so [`docs/rewrite-inventory.md`](docs/rewrite-inventory.md) states it, and lists where it can be wrong. That's INV-04's trust gap, so it needs a reviewer's reading. In short:

- **A rewrite is a site,** where a fold commits a change. There are three kinds:
  - a return of something other than null, `false` or `nullopt`;
  - a changed flag (`Changed`, `MadeChange`, `MadeIRChange`) set to `true`;
  - an in-place change, such as `replaceUse` or `setOperand`, with no site after it in its block to commit it.
- **A fold** is a function that can decline, with a null result or a false flag, and that either is an entry point, is forwarded to by a fold, or builds or changes IR.
- **A forward isn't a site.** Examples: `return g(...)`, `if (Value *V = g(...)) return replaceInstUsesWith(I, V);`, `if (g(I)) return &I;`, `Changed |= g(I);`, and a driver installing a fold's result. A name an `if`'s condition binds is bound only inside that `if`. A name bound by a matcher (`return Y;`) is the site's own value, so that return is a site.
- **Not counted:**
  - Helpers: they decline, build nothing, and aren't forwarded to.
  - Builders: they never decline, like `getFalse`. Returning a builder's result is the caller's site.
  - Both are listed in each file for review.
- **Counted once:** a pass's rewrites are the sites in its own files. InstCombine calling `simplifyAddInst` counts that function's 8 sites under InstSimplify only.

As a check of the rule, `simplifyAddInst` gets exactly the 8 return sites that #47's hand-written model has.

## Totals

| Pass | Rewrites | Integers only | Need floating point | Need memory | Need calls |
| --- | --- | --- | --- | --- | --- |
| InstSimplify | 541 | 300 | 200 | 31 | 115 |
| InstCombine | 2,536 | 1,499 | 607 | 281 | 515 |
| AggressiveInstCombine | 37 | 20 | 6 | 11 | 8 |
| Reassociate | 60 | 18 | 42 | 0 | 3 |
| All | 3,174 | 1,837 | 855 | 323 | 641 |

The last three columns overlap. What each blocked rewrite waits for:

- floating point: SEM-05;
- memory: F4;
- calls: the external-calls lane.

Each rewrite also records:

- `also`: `vector`, `cfg` or `undef`;
- the analyses it reads, which a proof takes as hypotheses for PASS-01 to discharge;
- the intrinsics it names. Integer intrinsics the emitter translates count as integers only.

The tags are triage, read from identifiers on the site's path. A site in a function that handles floating point, or anywhere in Reassociate, needs `fp` unless its path says its values are integers.

## Files

- `tests/llvm_rewrites.py`: `generate`, `check` and `summary`. It reads only source, so its output doesn't depend on the host.
- `tests/llvm_scope/rewrites/{instsimplify,instcombine,aggressive-instcombine,reassociate}.json`: one rewrite or fold per line, so a diff shows each one that moved.
- `tests/llvm_rewrites_test.py` checks two things:
  - the rule on small C++ files: each kind of site and forward, a helper and a builder, plus each case review found;
  - on a copy of the pinned source, that removing, adding and changing a rewrite are each reported by ID.
- `docs/rewrite-inventory.md`: the rule, IDs, tags and gaps.
- `ir-lean.rewrites/1` added to `tools/irlean/schemas.py`. Hashes and the pin come from `tools/irlean`.
- INV-04 is now "in progress", with this as evidence. DAGCombiner, GlobalISel and TableGen aren't started. Also: a row in `docs/testing.md`, an item in `docs/status.md`, and two `add_test`s in `CMakeLists.txt`.

## Tests

Run locally in the dev shell, on macOS arm64:

- `tests/llvm_rewrites.py check`: ok, about 1 s, after merging `origin/main` at `091275e`.
- `tests/llvm_rewrites_test.py`: ok, about 4 s.
- `tests/llvm_scope.py check --offline` and `tests/llvm_scope_test.py`: pass.
- `tests/irlean_test.py`: passed before the merge. After it, one test fails locally because my compiled IRLean predates `main`'s new UB reason; CI builds fresh.
- ruff format and check, ty on the new files, rumdl, gersemi, cmakelint and editorconfig-checker: pass.

Not run locally:

- the full ctest suite, which is left to CI;
- `needs_tests_test.py`, which needs a configured build directory.

Two lint findings show up on macOS in files this PR doesn't touch, and both predate it:

- ty reports `os.waitid` in `tools/irlean/proc.py`, which macOS doesn't have;
- ruff reports I001 in `tests/verdict_test.py`.

Independent review: 4 rounds, approved. Its findings, all fixed with a regression each:
- a name bound in an `if` read across the whole function, which hid `IC.Shifts.visitLShr.L1640`;
- in-place changes with no site, such as `MaybeSimplifyHint`'s `replaceUse`;
- changes wrongly committed by a later forward or a returned flag;
- opcode-generic functions, all of Reassociate's among them, tagged integers only;
- top-level changes not grouped with the site after them, and losing those statements' tags.
