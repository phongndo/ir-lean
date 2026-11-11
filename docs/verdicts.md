# Verdicts

The design of stage A: one default-deny place that decides every verdict a tool gives. Nothing here is built. Facts
were checked on 2026-11-10 at `f140938`, and for the harness at `5258d5a`, the head of #117's unmerged branch.

## The claim

A *grant* is a status a reader acts on as settled. After the change, every grant comes from `decide` in
[`tools/irlean/verdict.py`](../tools/irlean/verdict.py), and only when every piece of evidence its contract requires
was observed and is clean. Anything else is the tool's `unknown` status, when a limit could explain it, or its `error`
status. A limit, a crash, a model stop or a failure is never a grant, and never dropped: it's counted, and it decides.

A process is clean when it ended on its own, with exactly the integer exit its contract names, no limit, no signal,
and no Lean limit in its first error. A fact is clean when it's exactly `True`; a count, an integer within its bound;
files, at least one, each there as recorded; an answer, nonce'd and a value its contract allows; another tool's
record, of a schema, status and exit that tool's contract grants, from a process that ended with that exit.

- **proved**, in `tools/verify.py`, `tools/rules/proved.py`, and the store's `admitted` and `candidate`, which rest
  on it: the theorem is about the target and kernel-checked. It needs `lean` compiling the module, `leanchecker`
  replaying it and the axiom audit, each clean; its files there; nothing the checks read changed while they ran;
  every check the contract lists passed; and no witness of the same statement failing.
- **certified**, and `tools/binding.py`'s **bound**: as proved, about at least one file; or a verdict this checker
  stored for exactly these files and the live toolchain, with the files still there.
- **passed_tier1**: tested, not proved. It needs every planned input run, none failing, timed out or crashed, no
  limit, `min_satisfied` inputs meeting the hypotheses unless the whole domain ran, no input where a call of a
  generated function stopped the model, in any property, and each harness process exiting 0 when asked to quit.
- **exact** and **instance**, from `store.py lookup`: the statement's key is a stored lemma's, or a stored lemma's
  conclusion instantiates to it. It needs `lake build --no-build` and the lookup's Lean process clean, its answer
  nonce'd, a statement with no tactic block, as `verify_check.lean` requires since #111, and each lemma it names
  `admitted` or `candidate` in the index.
- **win**: a rewrite that counts on the board. Each of its comparisons grants **faster**: the protocol's rule held,
  with no protocol problem, every timed run clean on its plan's cores, and every planned session there once.
- **replayed** and **verified**, from `tools/verify_claims.py`: the same rule, in the independent verifier's code.

Settled negatives are grants too, as readers act on them. **counterexample** needs the answering process clean, its
answer nonce'd and its witness a literal, as since #111. **refused**, **vacuous**, the store's **none** and a must-fail
check's **caught** need a diagnosis, not a limit, from a process that ended on its own with a diagnosis's exit code.

## The inventory

At `f140938`, and at `5258d5a` for the harness. "Asks" is whether it asks `irlean.verdict.decide`. "Bugs" are those
of #91, #105, #111, #115, #117 S9, #118 S1 and the open one that came from it.

1. **`tools/verify.py`**: `decide` 1096-1201, `compile_module` 775-809, `evaluate_witnesses` 993-1069,
   `assert_contract` 1312-1333. `proved` 0, `counterexample` 2, `unsupported` 3, `timeout` 4, `error` 1, and 32
   reasons, in `STATUSES`, `EXIT_CODES` and `REASONS`, 62-110. Reads each Lean step's exit, `timed_out` and first
   error, its 18 checks, the `.olean` files, nonce'd witness answers, and a snapshot. Asks: for `proved` (1168) and a
   witness's refutation (1116); the other statuses are its own. Bugs: #111.
2. **`tools/prooftest/prooftest.py`**: `decide` 1806-1871, `search` 1537-1608, `refutes` and `confirm` 1686-1736,
   `Harness.stop` 1146-1160, `assert_contract` 2012-2041. `passed_tier1` 0, `counterexample` 2, `vacuous` 3,
   `unknown` 1, and 28 reasons, 96-189. Reads the harness's code per input (1 holds, 2 fails, 0 or 2 + k a hypothesis
   false), nonce'd answers, timeouts, crashes, time left, the kernel's answer, and `verify.py`'s record and witness
   step. Asks: for `counterexample` only. Bugs: #118 S1, and the open one: `model_hypotheses` is set only for an
   equivalence (1462), so where a hand-written hypothesis is false because the model stopped, the input is discarded.
3. **`tools/rules/proved.py`**: `check` 188-253, `replay` 170-185. Per rule, `proved: true`, or false with the
   checker's or `decide`'s reason, which no table registers. Reads `rules_check.lean`'s process and nonce'd answers,
   each `leanchecker`, and four checks. Asks: yes. Bugs: none.
4. **`tools/rules/certify.py`**: `gate` 254-470, `conclude` 473-504, `failed` 507-529. `certified` 0, `refused`,
   `unsupported`, `unknown`, `error`, with reasons inline, from `decide` and from the checker. Reads `opt`,
   `ir-lean --report`, Lean in a scope, the checker's nonce'd answer, the audit, `leanchecker`, and seals.
   Asks: for `certified`; the other statuses are its own. Bugs: none.
5. **`tools/store/store.py`**: `verdict` 468-549, `proved` 403-422, `axiom_check` 333-364, `replay_check` 367-379,
   `check` 575-676, `add` 748-864, `lookup` 708-745. `admitted`, `candidate`, `refused`, `accepted`, `ok`, `exact`,
   `instance`, `none`, `error`; 18 refusal reasons, 78-111, and `StoreError`'s codes. Reads exits, which `run`
   (141-150) makes 124 at any limit, a limit pattern, the first `STORE-JSON` line, with no nonce, and `index.json`.
   Asks: for `admitted` and `candidate`, as an assertion; not for `exact` or `instance`. Bugs: #105.
6. **`tools/binding.py`**: `Runner.__call__` 196-222, `_verify` 622-745, `replay` 767-964. `bound` 0, `refused` 1,
   `unsupported` 3, `unknown` 4, `error` 5, with 19 reasons inline and the checker's. Reads `proc.Ran`'s limit, any
   signal or 137, the limit pattern, hashes, the checker's nonce'd answer, the audit, `leanchecker`, and a cache entry
   keyed by the manifest and live toolchain. Asks: for `bound`, on a replay and a cache hit. Bugs: none.
7. **`tools/verify_claims.py`**: `need` 159-171, `Ran.limited` 120-122, `replay_evidence` 727-765, `_decide_claim`
   795-895. `replayed` 0, `verified` 0, `refused` 1, `partial` 2, `unknown` 4, `error` 5, with about 25 reasons
   inline. Reads its own runner's exit and `timed_out`, its own limit pattern, nonce'd answers, hashes and stamps.
   Asks: no, by design. Bugs: #91, #105.
8. **`tests/cut.sh`**: `check` 182-215 with `stopped_at_limit` 172-180, `must_fail` 287-305, the module loop 51-58,
   `translate` 136-143, the slice's audit 266-273. Lines `ok`, `FAIL`, `UNKNOWN`; exit 0 only with neither of the
   last two. Reads exits 124 and 137, Lean's error headers, its own limit pattern (46-47), Lean's memory lines, the
   audit's `and N from bv_decide`, and `diff`s of IR. Asks: no. Bugs: #115.
9. **`bench/kernels/harness.py`** on #117: `run_once` 1271-1303, `compare` 1687-1792, `protocol_problems` 1805-1880;
   `protocol.py`'s `verdict` 107-181 and `figures_verdict` 184-221; `board.py`'s `problems` 216-310. `faster`,
   `slower`, `inconclusive`, with `by_the_protocol` beside them, and a board entry that counts. Reads each timed
   run's exit, limit, cores, time, output hash and figures, the plan, seeds and load. Asks: no. Bugs: #117 S9.

Others: `tests/llvm.py`, `llama.py`, `superopt.py`, `passes.py`, `verify_negative.py`, `cpp_correspondence.py` and
`bench/instcombine/stage1.py` ask `decide`. `tests/alive.py`'s `verdict` (79-92) takes `None` for `correct`, and
`bench/kernels/pairs.py` (142-151, 214-218) reads `prooftest.py`'s status without its schema, exit or limit. Nine
more shell tests decide in bash: `proofs`, `calls`, `contracts`, `float`, `freeze`, `refine`, `generic_rewrites`,
`undef_freeze` and `memory_refine`. What the inventory shows:

- `decide` knows four claims. `passed_tier1`, `vacuous`, `exact`, `instance`, `faster`, a win and `cut.sh`'s `ok`
  never reach it, and where it's asked, the caller picks the checks, so a check left out counts as passed. The lint
  in `tests/verdict_test.py` (440-464) matches six words, and `passed_tier1`, `exact` or `faster` pass it.
- Limits are read four ways: `irlean.lean.LIMIT`; `verify_claims.py`'s, with #91's `not enough memory`; `cut.sh`'s,
  without `SAT solver timed out`; and the store's 124. With an ordinary error and a limit, `decide` says `unknown` for
  a limit anywhere in the output, `classify_lean` goes by the first error, and `cut.sh` says `FAIL` for any error.
- `artifacts_modified` is `refused` in `binding.py` and `verify_claims.py`, and `error` in `verify.py` and
  `certify.py`. A `SIGSEGV` is `unknown` in `binding.py`'s runner, and `error` in `decide`.
- Gaps not reported before: `passed_tier1` doesn't read how the harness process ended; `lookup` takes the first
  `STORE-JSON` line, with no nonce, from the Lean process that elaborates the requester's statement, the pattern of
  #111; `compare` writes `faster` when `by_the_protocol` is false, and only `board.py` (297-300) joins them; #115's
  fix covers `check` only, so a limit in the module loop, `translate` or the slice's audit is still `FAIL`; and
  `must_fail` takes any non-zero exit, even Lean killed at 124 or 137.

## The threat model

In scope, each giving `unknown` or `error` and never a grant: a bug in a tool or the library; a process that crashes,
is killed, or stops at a time, memory, heartbeat, stack or solver limit; the model stopping, `IRLean.ModelStop`; an
operator's mistake, such as a stale build, another toolchain on `PATH`, a stale cache, a plan copied under another
name or a flag left out; and concurrent processes: another build in the checkout, an editor, two runs sharing a work
directory or cache. Out of scope, as [what the gates promise](rules.md#what-the-gates-promise) says: code running as
the same user that rewrites files, tools or the toolchain on purpose while a tool runs, which could rewrite `decide`
too, and proofs from untrusted authors, which need a sandbox the operating system enforces first.

## The design

`tools/irlean/contracts.py` names each tool's contract once, as [`schemas.py`](../tools/irlean/schemas.py) names each
schema: statuses with exit codes and meanings, reasons with their status, its `unknown` and `error` statuses, and its
grants with what each requires. Tools keep no tables, and `capabilities` prints the contract as today, for `irl`.

```python
# tools/verify.py: a claim about a generated function. docs/verify.md.
VERIFY = Contract(schemas.VERIFY, unknown="timeout", error="error",
    statuses={"proved": (0, "..."), ..., "error": (1, "...")}, reasons={"kernel_checked": "proved", ...},
    grants=[
        Grant("proved", "kernel_checked", excludes=["counterexample"], needs=[
            Fact("request", "invalid_request"), Process("compile_proof", "proof_failed", lean=True),
            Fact("statement", "statement_mismatch"), Process("axioms", "disallowed_axiom", lean=True), Files("outputs"),
            Process("kernel_replay", "kernel_replay_failed"), Fact("unchanged", "artifacts_modified")]),
        Grant("counterexample", "witness_falsifies", excludes=["proved"], needs=[...])])
```

A requirement names a field, its kind, and the reason it gives when it's there and not clean. The kinds are
`Process`, a `Step`; `Processes`, at least one, each clean; `Fact`; `Count`; `Files`; `Answer`; `Upstream`, another
tool's process and record, read against that tool's contract; and `Problems`, a list, clean when empty.

A tool declares what it observed on an `Observed` for its contract, as it goes, so a run that stops early leaves the
later fields absent. `Observed` refuses a field its contract doesn't name, so a typo can't make a field nothing
requires, and a field set twice, so a retry's clean result can't hide a first failure:

```python
seen = verdict.Observed(contracts.VERIFY)
seen.process("compile_proof", ran)  # an irlean.proc.Ran: exit, limit, output
seen.fact("statement", stated == pinned)
print(schemas.dumps(verdict.record(verdict.decide(seen, contracts.VERIFY.proved), **rest), schemas.VERIFY))
```

`decide(seen, grant)` is the only function that returns a grant, and denies by default. In order:

1. A limit on a process the grant requires: `unknown`, with the contract's reason for that limit.
2. Each requirement, in order. Absent: `error`, `internal_error`, unless the requirement names another. A process
   that crashed, by a signal other than `SIGKILL`, an exit of 128 or more its contract doesn't name, or an exit
   that isn't an integer: `error`, `tool_failed`, never the requirement's reason. Otherwise not clean: its reason.
3. A grant it `excludes` that the same evidence grants: `error`, the contract's contradiction reason, as
   `evaluation_contradicts_proof` is today.
4. Otherwise the grant, with its reason and exit code.

A tool asks for the grants its run aims at, in its contract's order, and reports the first granted, or else the
decision on the one its request aimed at. Only `decide` makes a `Decision`, and `verdict.record` writes `status`,
`reason`, `meaning` and `exit_code` from one, as a `dict` subclass only it makes; `schemas.dumps` and `write` refuse
a record of a contract's schema whose status is a grant and that isn't one. The `assert_contract`s become requirements.

`verdict.limit_of(step)` alone says which limit stopped a process: its runner's, `SIGKILL` or 137, `timeout`'s 124,
Lean's memory exception or panic line, or, for a Lean process, a limit in its first error header, by `irlean.lean`'s
patterns with #91's `not enough memory` and `cannot allocate memory`. The first error decides, as in `classify_lean`,
since what fails after a limit often fails because of it; `decide`'s whole-output match and `cut.sh`'s rule go.

`tests/cut.sh`'s logic moves to Python, as `tests/cut.py`, on two helpers in `irlean.lean`: `check_module`, which
compiles, audits and replays a module and fills an `Observed` for `proved`, and `must_fail`, which fills one for
`caught` from Lean's process and its first error at the expected theorem. Extracting a function, comparing IR and
writing mutants become Python functions, and the output stays `ok`, `FAIL` and `UNKNOWN` lines. Bash can't call
`decide`, and a copy of its rule in bash is what #115's review had to fix three times.

## The invariants, as tests

Each pull request adds its tests before its code. "Fails on main" marks those that fail today.

1. **The evidence matrix**, in `tests/verdict_test.py`: for every contract and grant, no combination of its
   requirements' values grants unless all are clean, and one is `unknown` exactly when a required process holds a
   limit. The values are clean, absent, and each non-clean one of the kind: the 16 of `STEPS` that aren't clean, and
   exits 124 and 139; `False`, `None`, `1`, `"yes"`; `None`, `True`, `1.0` and each side of a bound; no files, one
   missing, `1`; no nonce, another, two answers, a value outside the set; one problem, `None`; each wrong schema,
   status and exit upstream. Each grant gets the full product over clean, absent and one non-clean value of each
   kind, and every break of one or two fields over all the values.
2. **Each tool's mapping.** Each tool has `observe(state) -> Observed`, and its test a clean state, which grants, and
   breakers, each a change to the state naming the requirement it breaks. Each breaker, and each pair, takes the
   grant away, and the test fails if a requirement of the tool's grants has no breaker.
3. **No grant outside `tools/irlean`.** An AST check of the Python in `tools/`, `tests/` and `bench/` fails on any
   contract's grant status as a string literal returned, assigned to or passed as `status` or `verdict`, or the value
   of a `"status"` or `"verdict"` key. Ruff's `TID251` bans `irlean.verdict.Decision` and `irlean.verdict._` names
   outside `tools/irlean`. Its exceptions are listed with why, as `docs/python.md` lists its own:
   `tools/verify_claims.py`, for BIND-03, and fixtures that write one tool's record to feed another. Shell tests that
   print `ok` for a Lean process are on a list that can only shrink. Fails on main.
4. **The past bugs and gaps**, one test each: #91, `not enough memory` is `unknown`, not `refused`; #105, a crashed
   audit is `tool_failed`; #111, a candidate that isn't a literal, or a witness with a tactic block, refutes nothing;
   #115, a limit in each Lean step of `cut` is `UNKNOWN`, an ordinary error before one `FAIL` (fails on main); #117
   S9, a session with a run that exited 1 is never `faster` (fails on #117); #118 S1, a model stop in an equivalence
   is `unknown`. These fail on main: a hand-written hypothesis false where the model stopped is `unknown`; a harness
   that answered every input and didn't exit 0 gives no `passed_tier1`; a lookup whose statement prints a
   `STORE-JSON` line answers nothing; and Lean killed after the expected error isn't caught.
5. **The registry**: every contract's reasons name its statuses, each status has an exit code, and each tool's
   `capabilities` output is byte for byte what `f140938` prints, kept as a fixture. Test 1's matrix also runs through
   `tools/verify_claims.py`'s `need` and `verdict`, which a test may import, though the verifier imports no `irlean`.

## The migration, in pull requests

Each leaves every tool working and changes under about 1,500 lines, by estimate.

1. **The core**, about 900: `Observed`, the kinds, `decide`, `record` and `limit_of`; `contracts.py` with today's
   four claims; tests 1, 3 as a report, and 5. The old `decide(claim, Evidence)` wraps the new for its 13 callers.
2. **`tools/verify.py`**, about 700: its tables move to `contracts.VERIFY`, and its `decide` becomes `observe`.
3. **`tools/prooftest/prooftest.py` with `Harness.lean`**, about 1,200: the harness says, per input, whether a call of
   a generated function stopped the model, in any property, which closes the open bug; `passed_tier1` and `vacuous`
   read the harness's end; `bench/kernels/pairs.py` reads the record as `Upstream`.
4. **`tools/rules/` and `tools/store/`**, about 1,200: `StoreTool.lean` prints the nonce and refuses a statement
   with a tactic block; `exact`, `instance` and `none` become grants; a refusal needs a clean diagnosis.
5. **`tools/binding.py`**, about 800, with its readers `tests/passes.py`, `tests/verify_negative.py` and
   `bench/instcombine/stage1.py`, which read its record as `Upstream`.
6. **The tests that ask `decide`**, about 900: `tests/llvm.py`, `llama.py`, `superopt.py`, `cpp_correspondence.py`
   and `alive.py`. The wrapper goes, and test 3 is strict for Python.
7. **`tests/cut.sh` to `tests/cut.py`**, about 1,000, on `check_module` and `must_fail`.
8. **The nine other shell tests**, about 1,400, onto the same helpers. The shell list is empty.

The JSON stays compatible, and no schema is bumped: status words, reason codes, exit codes and meanings stay, and a
new reason goes at the end of its status, as the tables say today. Only the conditions for a grant change: some
answers become `unknown` or `error`, none a grant. Two are visible: in PR 3, a hand-written property where the model
stops is `unknown/model_stopped`, a reason that exists; in PR 5, `binding.py`'s `artifacts_modified` is `error`, exit 5,
not `refused`, exit 1. `ir-lean.rules.proved/1`'s reasons become registered ones, which no reader matches.

The harness plugs in when #117 is cut again, on top of PR 1. `contracts.py` gets `KERNELS_COMPARISON` and
`BOARD_WIN`. `compare` fills an `Observed` with each timed run as a `Process`, `protocol_problems` as `Problems` and
the rule's conditions as `Fact`s, and asks for `faster` or `slower`, so a comparison that isn't by the protocol is
`inconclusive`, `not_by_the_protocol`; the board asks for `win`, with each comparison as `Upstream`. These schemas
aren't on main, so each keeps #117's version with this meaning, and the committed controls are written again.

## Not in scope

- Stage B: moving the parsing of IR and machine-code text, in `harness.py`, `binding.py` and the tests, to C++.
- Stage C: a content-addressed work area for runs, builds and caches.
- Stage D: one source of truth for each data file.
- Sandboxing untrusted proofs; deliberate tampering; the protocol's statistics; the board's other rules; and what
  each Lean checker checks, but for `StoreTool.lean`'s nonce and statement check and `Harness.lean`'s model stops.

## Open questions

1. Settled negatives, `counterexample`, `refused`, `vacuous`, `none`, `caught` and `slower`, go through `decide` here,
   beyond the positive statuses. Is that the scope you want?
2. `artifacts_modified` becomes `error` in `binding.py`. `verify_claims.py` says `refused`, and this leaves it. Should
   the independent verifier follow?
3. A win rests on its proof's test being registered in `CMakeLists.txt`, which `board.py` reads, not on a record of it
   passing. Should `win` require an `Upstream` `proved` record for the proof?
4. `must_fail` will call a Lean process killed after printing the expected error `unknown`, not caught, so a loaded CI
   runner may print more `UNKNOWN` lines. Is that acceptable?
5. PR 8 is about 1,400 lines in nine tests with reviews of their own. In stage A, or after it?
