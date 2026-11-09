# Shared rules for chunk 1 G2 family agents (on machine z, NixOS)

Repo: ir-lean (github.com/phongndo/ir-lean), a Lean 4 semantics for LLVM IR pinned to `llvmorg-23.1.3`. Chunk 1's
gate G2: every rewrite in LLVM's peephole passes proved for every input, each proof stored as a lemma under its rewrite
ID. The core (#97) and InstSimplify's seven families (#103) are on `main`; new families branch from `main`.

## Read first
- `git show origin/chunk1/g2-handoff:handoff/family-common.md`: the conventions every family follows (models, one
  theorem per site named `Peephole.<ID>`, a `sound` per fold, registry format, allowed hypotheses, rules). Follow it.
- `git show origin/chunk1/g2-handoff:handoff/pr-arith.md`: a finished PR body for the `is-arith` family. Copy its
  shape for yours.
- `tests/passes-proofs/peephole/README.md`, `docs/rewrite-proofs.md` (scoring rules 1-7), `tests/peephole.py --help`.

## Environment
- `IN_NIX_SHELL` is unset: run tools as `nix develop -c <cmd>` from your worktree.
- The machine has 32 cores and 30 GB shared with four other lanes. Every build, `compare` and `measure` goes through the
  heavy-job pool: `nix develop -c tools/measure.py run --label <x> --heavy --max-tree-rss-mb 6000 --timeout 3600 --
  <cmd>`. Lean processes are capped at 4 GB (`-M 4096`, in the lakefile for `Peephole`); a proof that needs more is
  missing a lemma: factor it out, never raise a limit. A build takes seconds; `compare` for a family takes minutes.
- Pushing: if the global git credential helper is stale, push with
  `git -c credential.https://github.com.helper= -c 'credential.https://github.com.helper=!gh auth git-credential' push origin HEAD:<your branch>`.
  Never force-push. Never push to `main`, `chunk1/g2-core` or any branch not named in your task.
- Long jobs: start them with Bash `run_in_background` and wait for them; never end your turn while a job you started
  runs. Kill nothing you didn't start.
- Never run the full ctest suite. Run what your change touches: `lake build --wfail`, `tests/peephole.py compare
  --family F --write`, `tests/peephole.py score --check`, `tests/peephole.py store --family F --dry-run`,
  `tests/peephole.py measure --family F`, the axiom check
  (`IRLEAN_CHECK_MODULE=<Module> LEAN_PATH=.lake/build/lib/lean lean -M 4096 tests/check_axioms.lean`), and lint:
  `nix develop -c bash -c 'uv run --quiet ruff format --check && uv run --quiet ruff check'` on Python you touch,
  `rumdl check` on Markdown you write.

## Rules
- No `sorry`, `bv_decide`, `native_decide` or new axioms. Every theorem for a variable width.
- No tool or model names anywhere (commits, comments, files, PR text): name no AI model, assistant, review loop or
  reviewer tool. Plain commit messages saying what changed.
- No calendar estimates (weeks, months). Describe progress by gates and dependencies.
- Quality over count: a site counts only if its model is the C++'s (pinned source at `$LLVM_PROJECT_SRC` inside
  `nix develop`) and its theorem is real. If unsure, list it unproved with a specific reason.
- Don't open PRs, don't merge into `main`, don't edit `store/` or run `store` without `--dry-run`: the lane owner
  admits lemmas serially at merge time.
- Commit as you go and push your branch when a step is done, so nothing is lost.

## Deliverables
1. Your branch pushed, every check above passing on its head.
2. A PR body draft (Markdown, in the shape of `pr-arith.md`, with the numbers your runs printed, dated 2026-11-09, no
   tool/model names) written to the path your task gives. Not committed.
3. Final report (your last message): branch and head SHA; sites counted, listed unproved (with reasons), integer
   instances, undef-only and not compared; `compare` totals and mismatches (must be 0); store dry-run verdict; E3
   numbers (per-site proof time range, module peak memory and wall time, reuse of stored rewrite lemmas); anything you
   are unsure matches the C++; anything the core lacked.
