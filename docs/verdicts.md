# Verdicts

The design of stage A: one default-deny place that decides every verdict a tool gives, which closes
[bug class 1](bug-classes.md#1-a-limit-or-a-failure-counted-as-a-pass), a limit or a failure counted as a pass. Its
first pull request, the core, is built; the rest isn't. This is its revision after the design review, under
[the process](process.md), step 0. Facts were checked on 2026-11-11 at `9a11118`, and for the harness at `5258d5a`, the
head of #117's unmerged branch.

## The claim

A *grant* is an output a reader acts on as settled: a status, a field such as `proved: true`, a count of grants, a
verdict nested in another record, an `ok` line, or an exit code that means one of these. After stage A, every grant a
tool on `main` outputs comes from `decide` in [`tools/irlean/verdict.py`](../tools/irlean/verdict.py), through an
adapter that takes a granted `Decision`. `decide` grants only when every requirement the grant's contract fixes was
observed and is clean, and every case the run planned was observed exactly once. Anything else is `unknown` or
`error`, as [the outcome table](#what-each-failure-gives) says. `tools/verify_claims.py` keeps the rule in its own code.

Clean means: a process ended on its own, with the exit its requirement names, no limit, no signal, and a first Lean
error, if it printed one, that isn't a limit; a fact is exactly `True`; a file is there as recorded; an answer carries
the nonce, is the only one, and is a value its contract allows; another tool's record passes `schemas.check`, says a
status and exit code that grant, and came from a process that ended with that exit.

The grants, each with what it needs besides that:

- **proved**, from `tools/verify.py`, `tools/rules/proved.py`'s `proved: true`, the store's `admitted` and `candidate`,
  and a shell test's module `ok`: `lean` compiling the module, the axiom audit and `leanchecker`'s replay, each clean;
  its outputs there; nothing it read changed while it ran; and every check the grant lists.
- **certified**, and `tools/binding.py`'s **bound**: as proved, about at least one file; or a verdict this checker
  stored for exactly these files and the live toolchain; or another tool's `bound` or `proved` record.
- **passed_tier1**: every planned input observed once, none failing, crashed or stopped at a limit; no input where a
  call of a generated function stopped the model, in any property; `min_satisfied` inputs meeting the hypotheses,
  unless the whole domain ran; and the harness exiting 0 when asked to quit.
- **exact** and **instance**, from `store.py lookup`: `lake build --no-build` clean; the requester's statement, with no
  tactic block, compiled in a process of its own; the answering process clean, with exactly one answer, carrying a
  nonce only that process was given; and each lemma it names `admitted` or `candidate` in the index.
- **counted**, from the peephole scorer in `tests/peephole.py`: proved, and the scorer's nine rules as fixed checks.
- **ok**, a line a shell test prints, and the test's exit 0: each check it planned observed once and granted.
- **win**, on the board, once #117 is cut again: each planned comparison granting **faster**, and the proof's own
  record, `proved` or `bound`, about the entry's current artifacts by hash, under the live toolchain. A test registered
  in `CMakeLists.txt` isn't evidence.
- **replayed** and **verified**, from `tools/verify_claims.py`: every check of a fixed list passed once, over every
  planned module.

A settled negative a reader consumes as a success is a grant too. **counterexample** needs the answering process
clean, its answer nonce'd and its witness a literal, as since #111. **caught** needs a diagnosis that isn't a limit,
from a process that ended on its own with a diagnosis's exit; a Lean check killed at a limit after printing the
expected error is `unknown`. Any negative a test reads as catching something wrong asks for `caught`, with the tool's
process as the step and its reason as the finding: a denial `tests/verify_negative.py` expects, a refusal
`tests/verify.py` or `tests/binding.py` expects of a planted bug, a rule `tests/rules_test.py` expects not proved.
Other refusals keep their own code, and move to `decide` only where that's free.

## What it holds against

In scope, each giving `unknown` or `error` and never a grant: a bug in a tool or the library; a process that crashes,
is killed, or stops at a time, memory, heartbeat, stack or solver limit; the model stopping; an operator's mistake,
such as a stale build or cache, another toolchain on `PATH`, a copied plan or a flag left out; a caller that filters,
skips or drops a run, an input or a check; and concurrent processes in the same checkout. Out of scope, as
[what the gates promise](rules.md#what-the-gates-promise) says: code running as the same user that rewrites files,
tools or `decide` on purpose, and proofs from untrusted authors, which need a sandbox the operating system enforces.

## Where grants come from today

`decide` has 15 callers: `tools/verify.py`, `prooftest/prooftest.py`, `rules/proved.py`, `rules/certify.py`,
`store/store.py` and `binding.py`; `bench/instcombine/stage1.py`; and the tests `passes.py`, `llvm.py`, `llama.py`,
`superopt.py`, `cpp_correspondence.py`, `verify_negative.py`, `peephole.py` (1297) and `rules_test.py` (732, 931).
Each picks the `checks` it passes, so a check it leaves out counts as passed. The forms a grant takes, and where each
is decided outside `decide`:

- **A status word**: `prooftest.py` 1806-1871, `passed_tier1`; `store.py` 708-745, `exact` and `instance`;
  `peephole.py` 1297-1318, `counted`; `verify_claims.py` 756 and 895, `replayed` and `verified`.
- **A field**: `proved.py` 241, `proved: true`; `store.py` 734, a match's `closes`; `stage1.py` 807, `replayed`.
- **A count**: `rules.py` 174-181's `slices_certified` and `functions_certified`; `search.py` 357; the board's, on #117.
- **A nested or joined verdict**: `stage1.py` 1236-1239 joins two records into `certified`; `rules.py` 119,
  `search.py` 279, `tests/replay_challenge.py` 342-374 and `verify_claims.py` 870 read a nested one's status.
- **Another tool's record**: `bench/kernels/pairs.py` 143-151 and 214-218, and `tools/prooftest/bench.py` 637-686, read
  `prooftest.py`'s status with no schema, exit or limit.
- **An `ok` line or exit 0**: 14 shell tests print `ok` for a Lean process: `cut.sh`; the nine named before,
  `proofs`, `calls`, `contracts`, `float`, `freeze`, `refine`, `generic_rewrites`, `undef_freeze` and `memory_refine`;
  and four the first inventory missed, `exec_memory`, `llama-bitspread`, `llvm_heap` and `emitter`. Each that reads a
  limit has its own pattern, and ten lack `SAT solver timed out`. `pairs.py --check` passes with a project skipped.
- **An enum**: a `Verdict` claim, which only `decide` returns today; test 5 keeps it so.
- **A serializer**: 83 calls of `json.dump` or `json.dumps` in 15 files write records, besides `schemas.dumps` and
  `write`, so a guard on the serializer can't see every grant.

`decide` reads a limit anywhere in a failed Lean process's output, and the store reads any exit 124 as a limit.
`artifacts_modified` is `refused` in `binding.py` and `verify_claims.py`, and `error` in `verify.py` and `certify.py`;
a `SIGSEGV` is `unknown` in `binding.py`'s runner, and `error` in `decide`.

### Live bugs

The review confirmed these on `main`. Each is closed by the pull request named, in [the migration](#the-migration).

1. `tests/cut.sh` 289: `must_fail` reaches `ok` after the expected error even when Lean exited 124 or 137. PR 4.
2. `tools/prooftest/prooftest.py` 1865: `passed_tier1` never reads the harness's end that `stop` records. PR 6.
3. `bench/kernels/pairs.py` 143: it reads `prooftest.py`'s JSON with no schema or exit check. PR 6.
4. `tools/store/store.py` 719 and 161: `lookup` elaborates the requester's statement in the process that answers, and
   takes the first `STORE-JSON` line, with no nonce, the pattern of #111. PR 7.
5. `tests/verdict_test.py` 443: the lint matches six words, in files not on its list. PR 1.
6. #118's open one: `model_hypotheses` is set only for an equivalence (`prooftest.py` 1462), so a hand-written
   hypothesis false because the model stopped discards the input. PR 6.

## The design

### Grants with fixed requirements

`Step`, `Evidence` and `Decision` stay, and grow by three things:

- `GRANTS`, in `verdict.py` beside `UPSTREAM`: each grant a tool gives, by name, with its status word and exit code,
  the steps, checks and files it requires, the grants it excludes, and, for a run over many cases, how a case counts.
  The caller names the grant, not what's checked. A check the caller fills that the grant doesn't list is `error`,
  `internal_error`, so a typo can't add a check nothing requires. A step a request can leave out, such as `verify.py`'s
  witnesses, is required by a condition on the request, never on what ran.
- `Evidence.steps`: the named processes a grant rests on, besides `lean`, `replay`, `axioms` and `step`.
- `Evidence.plan` and `Evidence.cases`: the identities the run planned, from its request before anything ran, and the
  raw outcome of each case observed, as a `Step`, in order and unfiltered. `decide` derives every count from `cases`,
  so `min_satisfied`, model stops and discards are its arithmetic, not the caller's. A run its own budget stopped
  records that as a limit on a step, so the cases it didn't reach are `unknown`, not `incomplete`.

```python
GRANTS = {
    "verify.proved": Grant(
        "proved",
        0,
        schemas.VERIFY,
        steps=("lean", "axioms", "replay"),
        files=True,
        checks=VERIFY_CHECKS,
        excludes=("verify.counterexample",),
    ),
    "prooftest.passed_tier1": Grant(
        "passed_tier1",
        0,
        schemas.PROOFTEST,
        steps=("harness",),
        cases=Cases(holds=..., discards=..., at_least="min_satisfied"),
    ),
}
d = verdict.decide("verify.proved", verdict.Evidence(lean=..., axioms=..., replay=..., checks=..., files=...))
status, reason, code = verdict.status(d, STATUSES)  # a grant's word only from a granted Decision
```

`decide(name, evidence)` is the only function that grants, and denies by default. In order: a limit on any required
step or case gives `unknown`; a crash gives `error`; then come an absent requirement, the plan against the cases, each
requirement that isn't clean, and a grant it excludes that the same evidence grants. Otherwise it grants.

### What each failure gives

| What | Outcome |
| --- | --- |
| A time, memory, heartbeat, stack, recursion, step or solver limit; `SIGKILL`, 137, 124 | `unknown`, its reason |
| The model stopped where the property needs an answer | `unknown`, `model_stopped` |
| Too few cases met the hypotheses, and the domain didn't all run | `unknown`, `too_few_satisfying` |
| A crash: another signal, an exit of 128 or more not named, or one not an integer | `error`, `tool_failed` |
| A required step, check or file absent | `error`, its reason or `internal_error` |
| A planned case missing or observed twice, or a case not planned | `error`, `incomplete` |
| Files a check read changed while it ran | `error`, `artifacts_modified`, in every tool |
| A record of the wrong schema, status or exit, or from a process that didn't end so | `error`, `upstream` |
| Otherwise not clean: an exit named, a check `False`, a file gone, no nonce | its reason, at the tool's status |
| Two grants that exclude each other, both granted | `error`, the contradiction's reason |

`model_stopped` and `too_few_satisfying` are `unknown` with no limit: more inputs, or a model that answers, might
decide them. `limit_of(step)` alone says which limit stopped a process: its runner's, `SIGKILL` or 137, `timeout`'s
124, Lean's memory exception or panic line, or a limit in its first Lean error, by `irlean.lean.LIMITS` with #91's
`not enough memory` and `cannot allocate memory` added. The first error decides, as in `classify_lean`, since what
fails after a limit often fails because of it. `decide`'s match anywhere in the output goes.

### Adapters

Each tool keeps its own tables of statuses, reasons and exit codes. `verdict.status(decision, table)` is the one way
from a `Decision` to them, and gives a grant's word only for a granted one. A count of grants counts granted ones. A
record nested in another, or read from another tool, is read by `schemas.check` and then `_upstream` (`verdict.py`
173). A verdict joined from two records, as `stage1.py`'s, asks `decide` for the joined grant with both as evidence.
`IRLEAN_DENY_ALL=1` in the environment makes `decide` deny every grant, with `error`, `denied`. It can only take a
grant away, and it holds in every process a tool starts.

### The shell tests

Bash can't call `decide`, and a copy of its rule in bash is what #115's review had to fix three times. So the shell
tests keep their orchestration in bash, and each `ok`, `FAIL` or `UNKNOWN` line about a process comes from one small
command, `tools/irlean/check.py`:

- `module NAME` compiles a module with warnings as errors, audits its axioms, replays it, and asks for proved.
- `must-fail WHAT FILE THEOREM` runs Lean, and asks for `caught`, with the first error at `THEOREM` as the finding
  when it isn't a limit, isn't at the imports and isn't a name Lean can't read.
- `run WHAT -- ARGV` is a step that has to succeed, such as translating a case.
- `plan ID...` names the test's checks before they run, and `end` exits 0 only when each was observed once and
  granted, and the test reported no failure of its own.

Each limits its process through `irlean.proc`, classifies its end with `limit_of`, and appends its decision to a
ledger in the test's work directory. A test's own `FAIL` lines, such as a case with no theorem, can only deny.
`cut.sh` is rewritten whole in stage A only if that's smaller.

### `tools/verify_claims.py`

It imports nothing of `irlean`, for BIND-03, and gets a default-deny guard of its own. `REPLAYED` lists the checks a
replay needs: `pin`, `anchors`, `ir_replay`, `translation_replay`, `compile_generated`, `compile_evidence`, `axioms`,
`unchanged` and `kernel_replay`. `complete(replay)` alone writes `replayed`: each check passed exactly once, and the
compiles and `kernel_replay` over every planned module, the units' namespaces and the evidence's files. `verified`
needs each evidence file's replay `complete`. `verdict` refuses a grant's status. `artifacts_modified` is `error`,
exit 5. It reads `IRLEAN_DENY_ALL` itself.

## Classes touched, and the guard each reuses

- **1, a limit or a failure counted as a pass**: `decide`, with fixed requirements, the plan against the cases, and
  the deny-all test. Stage A closes it on `main`. Over the harness it's closed only once #117, cut again on top of
  PR 1, asks `decide` for `faster`, `slower` and `win`, and its entry points pass the deny-all test.
- **3, reading another tool's text**: `irlean.lean.LIMITS`, through `limit_of`, is the one reader of Lean's limits.
  Answers carry a nonce, as `verify.py`'s have since #111. Parsing IR and machine code is stage B.
- **4, a reader that skips the check**: `schemas.check` and `_upstream` for each record read from another tool.
- **6, a total that hides a failing part**: #118's counting by why, in `decide`, which judges each case by itself.
- **2, a check then a use of something else**: its guards stay. No step reads a file again by path after it's
  checked, and a win binds the proof's record to the entry's artifacts by hash, as certify binds files since #109.

## The invariants, as tests

Each pull request adds its tests before its code. "Fails on main" marks those that fail today.

1. **Deny-all**, in `tests/deny_all_test.py`. Each public entry point runs its smallest input that grants twice, as a
   reader runs it: once as it is, which has to grant, and once with `IRLEAN_DENY_ALL=1`. The second run's exit code,
   output, the files it writes and the records nested in them hold no grant, in any form of the inventory. The entry
   points are `verify.py`; `prooftest.py run` and `tools/prooftest/bench.py`; `rules.py`'s `proved`, `certify` and
   `search`; `store.py`'s `add`, `check` and `lookup`; `binding.py`; `stage1.py`; `pairs.py --check`; the peephole
   scorer; `check.py` and the smallest shell test; and, on #117, `compare` and the board. `verify_claims.py` runs
   under its own switch. One not migrated yet is on a list that can only shrink.
2. **The plan against the cases**, through each public entry point that plans: a case filtered out after it ran, a
   check skipped, an input dropped, and a case observed twice each give no grant. Each tool's plan is its request's,
   by a test. Fails on main for `prooftest.py`, `pairs.py` and the shell tests.
3. **Fixed requirements**: `GRANTS` matches `tests/verdict/grants.json`, each grant's requirements, byte for byte.
   Each requirement has a fault planted on the public path in its tool's own tests, such as a `leanchecker` that exits
   1, or an `.olean` deleted after it's built, which takes the grant away. Deleting a requirement and its breaker
   together still fails both.
4. **The evidence, bounded**, in `tests/verdict_test.py`, for each grant: every value of each kind with the rest
   clean, such as the 16 unclean ends of `STEPS` with 124 and 139; each requirement left out; every pair, at one value
   of each failure category; and named interactions: a limit and an ordinary error in either order, Lean killed after
   the expected error, a clean retry after a failure, a model stop beside a failing input, and a proof beside a
   refutation. Each outcome is the table's: about 2,700 cases for 18 requirements, not their product's 387,420,489.
5. **One lint**: an AST check of `tools/`, `tests/` and `bench/` fails on a grant's word returned, assigned, passed as
   `status` or `verdict`, or set as their value, outside an adapter, and on a `Decision` made outside `verdict.py`. A
   second fails on a shell test that runs Lean and prints `ok` or exits 0 but through `check.py`. Exceptions are per
   function, each with why, on a list that can only shrink: at the end of stage A, only `verify_claims.py` and the
   fixtures that write one tool's record to feed another. It replaces the six-word lint. Fails on main.
6. **No legacy calls**: an AST count of calls of `decide` with a claim, not a grant's name, which can only fall. The
   old form goes in the pull request that brings it to zero, and from then `decide` refuses a claim.
7. **The live bugs**, through the public path, each failing on main: Lean killed at 124 or 137 after a `must_fail`'s
   error is `UNKNOWN`; a harness that didn't exit 0 gives no `passed_tier1`; `pairs.py --check` fails on a record of
   the wrong schema or exit; a statement printing a `STORE-JSON` line answers nothing; test 5 fails on a new grant
   word anywhere; and a hand-written hypothesis false where the model stopped is `unknown/model_stopped`.
8. **`verify_claims.py`**, through `replay_evidence` and `main`: a replay with its `kernel` step (591) skipped isn't
   `replayed`; a check of `REPLAYED` skipped, one passed twice, or a planned module not replayed is `incomplete`;
   `verdict("replayed", ...)` (722) raises; `IRLEAN_DENY_ALL=1` gives no grant and a non-zero exit; and files changed
   during a replay give `error`, exit 5. Fails on main.

## The migration

Each estimate counts added and deleted lines of code and tests, as `git diff --shortstat` does, from the lines each
pull request rewrites. For scale, #71, which made `decide` and moved ten callers onto it, was 1,514.

| PR | What it does | Lines | Live bug |
| --- | --- | ---: | --- |
| 1 | The core: `GRANTS`, `steps`, `plan`, `cases`, `limit_of`, the outcomes, the switch; tests 3 to 6 | ~1,200 | 5 |
| 2 | `verify_claims.py`'s own guard, and `artifacts_modified` as `error`; test 8 | ~400 | |
| 3 | `verify.py` on its grants, with its planted faults; test 1, with `verify.py` its first entry point | ~850 | |
| 4 | `tools/irlean/check.py`, and `tests/cut.sh`'s decisions on it | ~800 | 1 |
| 5 | The other 13 shell tests' decisions on `check.py`; the shell list is empty | ~1,000 | |
| 6 | `prooftest.py` from raw cases and the harness's end; model stops in `Harness.lean`; readers | ~1,000 | 2, 3, 6 |
| 7 | `store.py`: `lookup` in two processes, with a nonce; `exact`, `instance`, `admitted`, `candidate` | ~800 | 4 |
| 8 | `rules/`: `proved: true`, `certify`, the counts, `search`; `rules_test.py`'s `caught` | ~600 | |
| 9 | `binding.py`; readers `passes.py`, `verify_negative.py`, `replay_challenge.py`, `stage1.py` | ~1,300 | |
| 10 | `llvm.py`, `llama.py`, `superopt.py`, `cpp_correspondence.py`, the peephole scorer; old form gone | ~800 | |

Each leaves every tool working, as the old form of `decide` stays until PR 10. PR 1 comes first. PR 2 touches nothing
of the others, and can go in at any time. PRs 3 to 10 each add to `GRANTS` and its snapshot, so they go in this order,
each after the one before merges. PR 5 moves decisions only: the nine shell tests named before total 1,563 lines, too
many to port whole in one pull request. PR 7 costs one more Lean process for each lookup.

The harness, #117, is on hold. When it's cut again, it goes on top of PR 1: `GRANTS` gets `faster`, `slower` and
`win`; `compare` puts each timed run in `cases` and `protocol_problems` in `checks`, so a comparison that isn't by the
protocol is `inconclusive`; and the board asks for `win`, with each comparison and the proof's record as upstream.
Until it merges and passes test 1, class 1 isn't closed over the harness.

The JSON stays compatible, and no schema is bumped: status words, reason codes, exit codes and meanings stay, and the
new reasons, `incomplete` and `denied`, go at the end of their status. Some answers become `unknown` or `error`, none a
grant: `artifacts_modified` in `binding.py` and `verify_claims.py` is `error`, exit 5, not `refused`, exit 1; so is a
`SIGSEGV` in `binding.py`'s runner; and so is each live bug's case.

## Not in scope

- Rewriting the shell tests whole, after stage A; and stages B, C and D.
- Alive2's verdicts, read in `tests/alive.py`, and the tests that compare ours with them. Alive2 decides those;
  `alive.py` is default-deny on its own, and its `None` (79-92), a pair a batch proved, is on purpose and stays.
- Sandboxing untrusted proofs; deliberate tampering; the protocol's statistics; and the board's other rules.

## Decided

The maintainer answered the first design's questions, and the design above follows: 1, settled negatives a reader
consumes as a success go through `decide`; 2, `artifacts_modified` is `error` everywhere; 3, a win needs the proof's
`proved` record, bound to the entry's artifacts and toolchain; 4, a must-fail Lean check killed at a limit after its
error is `unknown`; and 5, the other shell tests are rewritten after stage A, and their verdicts move within it.

The maintainer answered the revision's two questions on 2026-11-11:

- **A run that plans nothing** exits 77, which `ctest` reads as skipped, only when a precondition it names is missing,
  such as a project's source not in the Nix store. A plan empty for any other reason, such as a glob that matched no
  case, is `unknown`, which fails CI.
- **At the end of stage A,** [the ledger](bug-classes.md) marks class 1 closed on `main`, and names the harness as open
  until #117 is cut again on the core, merges, and passes the deny-all test.

## Review

The review, by gpt-6.1-sol at xhigh, is answered above: S1 and S4 by fixed requirements, the plan, `verify_claims.py`'s
guard and tests 2, 3 and 8; S2 and S5 by the inventory, adapters, the win and test 1; S3 and S7 by the callers, test 6
and the estimates; S6 and S8 by three additions, test 4, the outcome table and the classes. Where this disagrees:

- Deleting a requirement and its breaker together fails tests here, but deleting its planted fault and its line in
  the snapshot as well passes. No test can tell that from a contract weakened on purpose; test 3 makes it a visible,
  reviewed change to `tests/verdict/grants.json`.
- "Independently of the caller" holds for a plan as far as the request does: test 2 checks the plan is the request's,
  but a request planned short on purpose is the operator's choice, and shows in its record.
- Test 1 covers our tools' entry points, not Alive2's cross-checks, which say what Alive2 says.
