## Context (shared by every family agent)

Repo: ir-lean (github.com/phongndo/ir-lean), a Lean 4 semantics for LLVM IR. You are one of several agents working in parallel, each in its own git worktree, on "chunk 1, gate G2" of proving LLVM's peephole optimizations: every rewrite in InstSimplify (and later InstCombine) at the pinned `llvmorg-23.1.3`, proved for every input, in Lean.

Your worktree starts at branch `chunk1/g2-core` (commit 3209c3e or later). Create your branch `chunk1/g2-<family>` from it immediately (`git checkout -b chunk1/g2-<family>`).

Read first, in this order:
1. `tests/passes-proofs/peephole/README.md`: the conventions. Follow them exactly.
2. `tests/passes-proofs/peephole/Peephole/{Term,Match,Oracle,Fold}.lean`: the core you build on.
3. `tests/passes-proofs/peephole/Peephole/IS/Add.lean` and `Peephole/Lemmas/Add.lean`: the worked example (InstSimplify's `simplifyAddInst`, 8 sites, model + one theorem per site + the fold's `sound` theorem). Copy its structure.
4. `tests/passes-proofs/peephole/folds/is-add.json`: the registry format.
5. `docs/rewrite-inventory.md` and `tests/llvm_scope/rewrites/instsimplify.json`: the rewrite IDs. Get your sites with e.g. `python3 -c 'import json; [print(r["id"], r["needs"], r["code"]) for r in json.load(open("tests/llvm_scope/rewrites/instsimplify.json"))["rewrites"] if r["function"] in {...}]'`.
6. The pinned C++: inside `nix develop`, `$LLVM_PROJECT_SRC/llvm/lib/Analysis/InstructionSimplify.cpp`, `llvm/include/llvm/IR/PatternMatch.h`, `llvm/lib/Analysis/ValueTracking.cpp`. The model must be what the C++ does, step by step, in the C++'s order, with each matcher's exact semantics (operand order, commutative or not, what binds when). Not what you think it does.
7. `IRLean/Int.lean` (the integer semantics: `Val w = Option (BitVec w)`, `none` is poison), `IRLean/Refine.lean` (`Refines`, and the laws `Refine.outcome_ok_ok`, `Refine.val_none`, `Refine.val_iff`, `Refine.refl_val`), `IRLean/Generic/*.lean` (#48's every-width rewrite lemmas, already in the lemma store), `docs/lemma-store.md`.

### What to deliver, on your branch
- **Models:** `tests/passes-proofs/peephole/Peephole/IS/<Family>.lean` (one or a few modules), namespace `Peephole.IS`. One `<fold>.steps` list per C++ function, one `Step` per C++ statement that can end the function, each step with the C++ comment above it and, if it rewrites, firing with its exact inventory ID. A forward to another fold you model is a step whose soundness is that fold's `sound` theorem; a call to code you don't model is `.delegate` (claims nothing). Entry folds InstSimplify's dispatcher calls get `<fold>.onInst (o : Oracle) : {w : Nat} → Term w → Result w`, with the arguments `simplifyInstructionWithOperands` passes (flags from the instruction; `MaxRecurse` = `RecursionLimit` = 3).
- **One theorem per rewrite site,** named exactly `Peephole.<ID>` (e.g. `Peephole.IS.simplifyAndInst.L2090`), and one `<fold>.sound` per fold, built with `run_sound` (or `run_sound_ordered` when a site needs that earlier steps fell through). Every width `w`, every flag, every operand including poison. Hypotheses allowed: operands `Consistent` with the run, `hasUndef = false`, `Oracle.Sound` (analyses' soundness, which is PASS-01's), and for a recursive call into InstSimplify (`simplifyBinOp`, `simplifyICmpInst` etc. with `MaxRecurse - 1`), either `.delegate` it or take the recursive simplifier as a parameter with a named soundness hypothesis. Name any hypothesis beyond these in the theorem's docstring and in the registry's `rests_on`.
- **Analyses:** use the core `Oracle`'s fields where they are what LLVM computes (e.g. `MaskedValueIsZero(V, M)` is `computeKnownBits(V).Zero ⊇ M`; `isKnownNonNegative` is the known-zero sign bit). Don't edit `Oracle.lean`. If you need an analysis it lacks, define a family-local extension structure with its own `Sound`, in your namespace, passed as an extra parameter, and say so.
- **Facts about values** that rewrites rest on: `Peephole/Lemmas/<Family>.lean`, namespace `Peephole.Lemmas`, stated for every width with `IRLean.Refines` or `=`, minimal hypotheses. Reuse stored lemmas first (`IRLean.Generic.*`, `Peephole.Lemmas.*`, `IRLean.Refine.*`; search with `tools/store/store.py lookup --statement '...'` after `lake build LemmaStore StoreTool`). For each hypothesis of a new value lemma, also write the store's counterexamples in the same file: `LemmaStore.Counter.<full lemma name>.drop_<hyp>` and `.sat`, in the exact form `store/LemmaStore/Counter/Generic.lean` uses. Don't run `store.py add` and don't edit `store/`: the store is admitted serially at merge time, from your registry.
- **Registry:** `tests/passes-proofs/peephole/folds/is-<family>.json`, as `is-add.json`, plus `"lemmas": [new value lemmas offered to the store]`, `"rests_on": {ID: [hypotheses beyond the standard ones]}` and `"unproved": {ID: "reason"}` for every site of your functions you didn't prove (the reason must be specific: e.g. "needs a model of computeKnownBits through shl", "vector-only", "the C++ forwards to simplifyX, which isn't modelled").
- **New helpers** (matchers, value lemmas about `Term`): in namespace `Peephole.IS.<Family>` (e.g. `Peephole.IS.Logic`) so families never clash. You may import and reuse `Peephole.IS.Add`'s helpers.

### Rules
- Don't edit `Peephole/{Term,Match,Oracle,Fold}.lean`, `Peephole/IS/Add.lean`, `Peephole/Lemmas/Add.lean`, `lakefile.toml`, `store/`, `CMakeLists.txt`, `docs/`, or anything outside `tests/passes-proofs/peephole/`. If the core is wrong or missing something you can't work around locally, stop and say so in your report, with the smallest change you'd want.
- No `sorry`, no `bv_decide`, no `native_decide`, no new axioms. Every theorem is for a variable width. Check axioms: `IRLEAN_CHECK_MODULE=<Module> LEAN_PATH=.lake/build/lib/lean lean -M 4096 tests/check_axioms.lean` must say "at most the standard three, and 0 from bv_decide".
- Build only through the machine's heavy-job pool, in the dev shell: `nix develop -c tools/measure.py run --label <family>-<what> --heavy --max-tree-rss-mb 5000 --timeout 1800 -- lake build --wfail Peephole.IS.<Module>`. The lakefile already caps each Lean process at 4 GB (`-M 4096`). If a proof hits the memory or heartbeat limit, a lemma is missing: factor it out; never raise a limit. The pool may make you wait for memory; that's expected. The first build in a fresh worktree builds `IRLean` too. Never run the full ctest suite.
- Record, for your final report, each module's build wall time and peak memory from measure.py's output line.
- Commit as you go with plain messages (no tool or model names anywhere: not in commits, comments or files). Push your branch: `git push -u origin chunk1/g2-<family>`. Don't open a PR, don't merge, don't touch other branches.
- Integer-only, scalar sites first. A site whose inventory `needs` isn't `["int"]`, or that is only about vectors, stays in `unproved` with its reason.
- Quality over count: a site counts only if its model is the C++'s and its theorem is real. If the C++ is ambiguous to you, say so in the registry rather than guess.

### Final report (your last message), in this shape
- Branch and head SHA.
- Sites proved (IDs), sites unproved with reasons, and counts.
- New value lemmas, and which stored lemmas you reused (names).
- Each module's build time and peak memory.
- Anything in the model you're unsure matches the C++, and anything the core lacked.
