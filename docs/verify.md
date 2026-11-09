# Verify

`tools/verify.py` checks one claim about one function in LLVM IR, and answers with JSON that an agent, or a
script, can act on without reading Lean's output. For what any theorem here means, see [trust](trust.md).

Facts here were checked at commit `e952086` on 2026-11-07, with clang 23.1.3 and Lean 4.35.0, on an Apple
silicon Mac in the dev shell.

## An example

From the repo, after `lake build` and building `build/ir-lean`, in `nix develop`:

```console
$ tools/verify.py check --c tests/real/bi_reverse.c --namespace Real --function popcount \
    --proof tests/proofs/Popcount.lean --theorem popcount_correct --pretty
```

That compiles the C with clang, as `tests/proofs.sh` does, translates `popcount`, checks the proof against
what was generated, and prints, shortened here:

```json
{
  "schema": "ir-lean.verify/1",
  "status": "proved",
  "reason": "kernel_checked",
  "exit_code": 0,
  "claim": {
    "statement": "∀ (x : BitVec 32), Real.popcount (Option.some x) = IRLean.Outcome.ok (Option.some (pop x))",
    "shape": "returns_ok",
    "axioms": ["propext", "Classical.choice", "Quot.sound",
               "pop_step._native.bv_decide.ax_1_6", "popcount_loop._native.bv_decide.ax_1_10"]
  },
  "assumptions": [
    {"id": "scope.modeled_ir", "text": "The claim is about the function as this LLVM IR, ..."},
    {"id": "statement.unpinned", "text": "No statement was pinned, so a person has to read claim.statement ..."},
    {"id": "llvm.mustprogress", "text": "The IR has llvm.loop.mustprogress, which the model checks as it reads LangRef ..."}
  ],
  "reproduce": {"command": ["tools/verify.py", "check", "build/verify/0c1f…/request.json"]}
}
```

That took 5 s. To look for a counterexample instead, give a statement and inputs to try:

```console
$ tools/verify.py check --c tests/real/bi_reverse.c --namespace Real --function popcount \
    --statement '∀ x : BitVec 32, Real.popcount (some x) = IRLean.Outcome.ok (some (x &&& 1#32))' \
    --witness '{"x": "1#32"}' --witness '{"x": "3#32"}'
```

```json
{
  "status": "counterexample",
  "reason": "witness_falsifies",
  "exit_code": 2,
  "counterexample": {
    "assignment": {"x": "3#32"},
    "instance": "Real.popcount (Option.some 3#32) = IRLean.Outcome.ok (Option.some (3#32 &&& 1#32))",
    "evidence": "compiled_evaluation"
  }
}
```

The same request can be a JSON file, with paths relative to it: `tools/verify.py check request.json`.
`tools/verify.py capabilities` prints the whole contract below as JSON.

## The contract

Every answer has a `status`, which is one of five, and a `reason`, which says which case of it this is. Both are
stable: a status or a reason keeps its meaning, and new reasons only get added. The exit code follows the
status, so a script can branch on either. Malformed requests, crashed tools and bugs in the tool itself still
answer in JSON, as `error`.

| Status | Exit | Means | Says the claim holds |
| --- | --- | --- | --- |
| `proved` | 0 | A kernel-checked theorem about the generated function, with every check below passed | Yes, in the terms of `claim.statement` and `assumptions` |
| `counterexample` | 2 | On the inputs in `counterexample`, the model's compiled code finds the claim false | No: it's false there |
| `unsupported` | 3 | The emitter refuses the function, or no witness could be decided | Nothing was decided |
| `timeout` | 4 | A resource limit stopped it before a verdict. `limit` says which. More may help | Nothing was decided |
| `error` | 1 | No verdict: the request, a tool or the proof failed, or nothing was proved or refuted | Nothing was decided |

| Reason | Status | Means |
| --- | --- | --- |
| `kernel_checked` | `proved` | Every check passed |
| `witness_falsifies` | `counterexample` | A witness makes the claim false |
| `function_unsupported` | `unsupported` | The emitter left the function out. `detail` has its reason |
| `witness_unsupported` | `unsupported` | No witness could be decided, and nothing else settled the claim |
| `time_limit` | `timeout` | `limits.timeout_seconds` ran out, including a witness whose run never ends |
| `memory_limit` | `timeout` | Lean ran past `limits.memory_mb` |
| `heartbeat_limit` | `timeout` | Lean ran out of heartbeats, `maxHeartbeats` in the proof |
| `recursion_limit` | `timeout` | Lean hit `maxRecDepth` |
| `stack_limit` | `timeout` | Lean ran out of stack |
| `solver_limit` | `timeout` | `bv_decide`'s SAT solver ran out of time, its `timeout` in the proof |
| `step_limit` | `timeout` | `simp` ran out of steps, its `maxSteps` in the proof |
| `invalid_request` | `error` | The request is malformed, including any field it doesn't know |
| `input_not_found` | `error` | A file the request names doesn't exist |
| `toolchain_missing` | `error` | ir-lean, Lean, the `IRLean` library, clang, `opt` or `leanchecker` isn't there |
| `tool_failed` | `error` | A tool crashed, or answered in a way this doesn't understand |
| `compile_failed` | `error` | clang couldn't compile the C input |
| `ir_invalid` | `error` | LLVM couldn't read the IR, or its verifier rejects it |
| `function_not_found` | `error` | The module has no such function |
| `generated_module_failed` | `error` | Lean rejected what ir-lean generated, which is a bug in ir-lean |
| `support_failed` | `error` | A support module didn't compile |
| `proof_failed` | `error` | The proof didn't check. `diagnostics` has Lean's errors |
| `artifacts_modified` | `error` | A checked file changed while Lean ran the proof's code |
| `theorem_not_found` | `error` | The proof module has no such declaration |
| `not_a_theorem` | `error` | The declaration isn't a theorem of a proposition |
| `statement_invalid` | `error` | The given statement doesn't elaborate |
| `statement_not_about_target` | `error` | The statement doesn't name the generated function itself |
| `statement_mismatch` | `error` | The theorem doesn't state what `statement` pinned |
| `disallowed_axiom` | `error` | The theorem or a module rests on an axiom outside the allowed ones |
| `kernel_replay_failed` | `error` | `leanchecker`'s replay through the kernel rejected a declaration |
| `evaluation_contradicts_proof` | `error` | The kernel accepted the proof, and compiled code refutes its statement |
| `not_proved` | `error` | No proof was given, and no witness made the statement false |
| `internal_error` | `error` | A bug in this tool |

### What `proved` needs

`checks` lists each of these with `pass`, `fail`, `skip`, `inconclusive` or `not_run`. `proved` needs every
required one to pass and none of the others to fail. The decision is one function, `decide`, and a second one,
`assert_contract`, turns any result that breaks this into `internal_error` before it's printed.

| Check | Required | What passing means |
| --- | --- | --- |
| `request`, `toolchain`, `inputs` | Yes | The request is well formed, the tools are there, and every input is copied and hashed |
| `compile_c` | If C | clang compiled it, with `PROOF_CFLAGS` and `-O2 -fno-strict-aliasing` unless `cflags` says otherwise |
| `ir_valid` | Yes | `opt -passes=verify` accepts the IR. ir-lean doesn't run LLVM's verifier, and hand-written or generated IR can fail it |
| `translate`, `generate` | Yes | ir-lean translated the function, and wrote the module |
| `compile_generated`, `compile_support`, `compile_proof` | Yes | Lean checked each, in that order |
| `claim`, `theorem` | Yes | The theorem is declared in the proof module, and is a theorem of a proposition |
| `mentions_target` | Yes | Its statement names the target, such as `Real.popcount`, and that constant comes from the generated module |
| `statement` | If pinned | The theorem's statement is the pinned one, syntactically or by reducible definitional equality |
| `axioms` | Yes | Every axiom in the proof and support modules is one [`tests/check_axioms.lean`](../tests/check_axioms.lean) allows. Each `bv_decide` axiom has to be `verifyBVExpr` of a formula and a certificate built from constructors and literals, and the toolchain's checker is rerun on them |
| `kernel_replay` | Yes | `leanchecker` replays the generated, support and proof modules through the kernel |
| `artifacts_unchanged` | Yes | The IR, the generated module and the `IRLean` library hash the same at the end as before the proof's code ran |
| `witnesses` | If given | No witness makes the statement false |

## A request

| Field | Meaning |
| --- | --- |
| `input` | `{"ir": PATH}` for `.ll` or `.bc`, or `{"c": PATH, "cflags": [...]}` |
| `function` | The LLVM name, without `@` |
| `namespace` | The Lean namespace and module the proof imports. Defaults to the input's name |
| `proof`, `theorem` | A Lean file and the theorem in it, by full name or its last components |
| `support` | Lean files the proof imports, compiled in this order |
| `lean_root` | The directory module names are relative to. Defaults to the proof's |
| `statement` | A Lean proposition. Pins the theorem, or stands alone to be refuted with witnesses |
| `witnesses` | A list of `{"x": "3#32"}`: a Lean term for each binder that isn't a hypothesis, by name or as `#0`, `#1`, ... |
| `limits` | `{"timeout_seconds": 600, "memory_mb": 4000}` by default |

A field it doesn't know is an error, so a misspelling can't be ignored quietly. A proof can import `IRLean`,
Lean's own libraries, the generated module and its support modules, and nothing else.

## Reading a result

`claim.statement` is what was proved, printed with full names. It's the theorem's own type, so a proof can't
pass by proving something else under the right name. The rest of `claim` takes it apart:

- `binders` lists each argument. A binder with `"hypothesis": true` is a precondition, and the theorem only
  covers inputs meeting it. A hypothesis of `False` makes any statement true, and still comes back `proved`.
- `shape` is `returns_ok` when the conclusion is `target ... = Outcome.ok _`, perhaps under `∃`, which rules out
  undefined behavior, model stops and runs that never end. Anything else is `other`, and gets an assumption saying
  to read it. `inc = inc` is a theorem about `inc`, and comes back `proved` with shape `other`.
- `axioms` is everything the theorem rests on.

`assumptions` lists what the answer rests on that nothing here checks, each with a link to where it's
explained: the scope of a theorem, the target, the front end, the trusted pipeline, `bv_decide`, the hypotheses,
how the model reads promises such as `mustprogress`, memory, and that the proof's code isn't sandboxed.

`diagnostics` has Lean's errors and warnings, with paths pointing at the request's own files rather than the
copies that were checked.

### Pinning a statement

A tool can check that a theorem is about the function, but not that it says what anyone wanted. That's for a
person to read, as [trust](trust.md#trust-boundaries) says. Give `statement`, and the theorem has to be exactly
that, or the answer is `statement_mismatch`. A statement copied from `claim.statement` always matches. Pin the
statement when the proof comes from somewhere untrusted, such as an agent, so the claim can't get weaker without
anyone noticing.

A pinned statement can name Lean's libraries, `IRLean` and the generated module, and nothing from the proof or
its support modules. A definition there would let the proof choose what the statement means. A statement that
names one is `statement_invalid`.

## Counterexamples

A counterexample needs a statement that names the target, and witnesses. Each witness is substituted for the
statement's binders, hypotheses stay as implications, and Lean decides the result by running the model's
compiled code. Only `false` counts, so a witness that misses a hypothesis holds. The answer is about the model,
on those inputs. It trusts Lean's compiler, as `native_decide` does, and the kernel doesn't check it. Only
statements naming Lean's libraries, `IRLean` and the generated module are evaluated. Evaluating anything from the
proof or its support modules would run the proof's own code, so a witness for a theorem that names one comes back
`unsupported`.

- **With a proof that fails** and a pinned statement, witnesses are tried against the statement. So are the
  assignments `bv_decide` prints when it finds a counterexample to some goal. Those count only if they make the
  pinned statement false, since they're about a goal inside the proof. Without a pinned statement they're listed
  with result `unsupported`.
- **A run that never ends** shows up as `timeout`, never as a counterexample, though the model says `none` there,
  which does make a claim of `= Outcome.ok` false.
- **A witness counts only if the Lean process that evaluated it ended cleanly.** All of a request's witnesses are
  evaluated in one process, so if it then runs out of time or memory, a witness it found false is `timeout`, and if
  it crashes or fails, `tool_failed`, never a counterexample. That holds since 2026-11-09, when
  [`irlean.verdict`](trust.md#where-python-decides-a-verdict) began deciding it.
- **A proof that passes** and a witness that fails means Lean's compiler, an `implemented_by` or `extern` in
  Lean or `IRLean`, or the kernel is wrong. That's `evaluation_contradicts_proof`, never `proved`.
- **What can be decided:** functions without memory, in practice, whose results have `DecidableEq`. Memory
  doesn't, so a witness for a function using memory comes back `unsupported`.

## What `proved` rests on

Everything in [trust](trust.md), and also:

- **The proof's own code runs only while Lean compiles it**, `#eval`, `run_cmd` and macros in the support
  modules and the proof, and isn't sandboxed. A module's code also runs wherever it's imported: its
  initializers, elaborators and other extensions. So nothing after compiling imports the proof. The checks
  read its modules as data, with `importModules (loadExts := false)`, which gives their declarations and the
  module each came from. They run `leanchecker`, which reads them the same way, and print statements with
  Lean's and `IRLean`'s notation only. The IR, the generated module and the library are hashed before any of the
  proof's code runs. A proof that edits files outside those, such as the tool itself or the toolchain, or
  leaves a process running, isn't detected.
- **The checks catch cheating that's been tried:** `sorry`, an axiom, `native_decide`, a theorem about a
  function named like the target, a theorem about something else, a declaration added with
  `debug.skipKernelTC`, fake `bv_decide` axioms, a proof or support module that rewrites the module it's checked
  against, and an initializer that prints an answer of its own. [`tests/verify.py`](../tests/verify.py) has
  each one.
- **Resource limits:** the first error decides. If Lean's first error is a resource limit, the answer is
  `timeout`, since what fails after a limit often fails because of it. Lean's later errors are still in
  `diagnostics`.

`tests/proofs.sh` and `tests/llvm.py` check axioms with `tests/check_axioms.lean`, which reads a proof and its imports
as data, with the same policy as this tool, and they run `leanchecker`. They also check that each theorem names its
function, from the generated module. What they don't do is hash the files a proof's code could change while Lean
compiles it: they compile proofs from the repo, which a person reviews, and this tool is for proofs from anywhere else.

## Reproducing a run

Each run keeps a directory, given by `--work-dir`, or under `build/verify/`, which keeps the last 20:

| Path | What |
| --- | --- |
| `inputs/`, `lean/` | Copies of every input, as checked, with the generated module and what Lean compiled |
| `request.json` | The request, pointing at those copies. `reproduce.command` reruns it |
| `result.json` | The answer |
| `check/` | What `tools/verify_check.lean` was given, and asked |

The result's `artifacts` has each input's SHA-256, and `versions` has Lean's, clang's, the emitter's commit and
binary hash, and a hash of the `IRLean` library. `reproduce.commands` lists every command that ran, with its
working directory, exit code and time. Rerunning the same request gives byte-identical IR: clang runs from the
input's directory, so the IR names no path.

## Extending it

- **The API.** `verify(request, base, tool, work)` in `tools/verify.py` takes a request as a dict and returns
  the result. The command line is a thin layer over it.
- **A new reason** goes at the end of its status in `REASONS`, and in the table above. `tests/verify.py` fails if
  this doc leaves one out. Existing reasons keep their meaning.
- **A new check** goes in `CHECKS`, and in `REQUIRED` if `proved` needs it. `tests/verify.py` already checks that
  no required check can be missing from a proved result, whatever it's called.
- **New evidence for a counterexample**, such as Alive2 for a refinement, is a new `counterexample.evidence`,
  saying what it trusts.
- **What Lean is asked** is in [`tools/verify_check.lean`](../tools/verify_check.lean). It imports only Lean,
  `IRLean` and the generated module, and reads the proof's modules as data. It reads its question from a JSON
  file and prints its answers on lines tagged with a nonce, so nothing a request says is pasted into Lean, and
  nothing Lean prints otherwise can pass for an answer. A new question about the proof has to be answered from
  its declarations, never by importing it or running its code.
- **A breaking change** to the result's shape changes `schema` to `ir-lean.verify/2`.

## Limits

- One theorem about one function at a time, from one module. Contracts between functions are
  [Phase 2](roadmap.md#phase-2-reusable-contracts-and-frame-reasoning).
- The emitter is trusted. A bug that changes what a function means, and still type-checks, makes a proof about
  the wrong function, and nothing here can see it.
- Statements are checked for naming the target directly. One that only reaches it through a definition is
  `statement_not_about_target`, so a reader sees what's claimed about it.
- Only the dev shell is supported, since it pins clang, `opt` and `PROOF_CFLAGS`. Outside it, C compiles for the
  host, and the answer says so.
