# Scoring passes with replayable evidence

What [`tests/passes.py`](../tests/passes.py) measures about LLVM's optimizer, what each result means, and what it
doesn't. Each counted result is a [bound certificate](llvm-proof-binding.md): a bundle anyone can check again from
scratch with `tools/binding.py verify`. For what any theorem here means, see [trust](trust.md).

**No pass is done, and nothing here can make one done.** A bound instance is translation validation of one run: one
function, in one test file, after one run of `opt` with one pass spec and triple, is the same function in IRLean's
semantics before and after, and never stops the model. It says nothing about the pass on any other input, about its
C++, about native code, or about a pipeline. [The task list](llvm-verification-tasks.md) has what would.

## What it does

For each test in `llvm/test/Transforms` whose `RUN` line runs one pass in `opt` with `-passes=`, from the pinned
llvm-project, `tests/passes.py`:

1. Runs `opt -S -passes=verify` and `opt -S -passes=SPEC` on the test, reading it from stdin, with the `RUN` line's
   `-mtriple`, exactly as `tools/binding.py` does, so the IR scored is the IR a bundle holds.
2. Finds the instances: the functions whose text changed, attribute groups included, and every function calling one.
3. Rules out, as `unsupported`, what the model or a bundle can't judge, by the same tests `tools/binding.py` applies:
   a function the pass added or removed, one ir-lean leaves out, one using memory or pointers, an argument that isn't
   `noundef` in the source, a target with `mustprogress` or `willreturn`, and a name a manifest can't hold.
4. Writes a certificate for each of the rest, stating the claim `tools/binding_check.lean` builds for the claim kind,
   with a proof its own automation found: every argument split into poison and a value, both sides run a block at
   a time, each branch split, and each path closed with `bv_decide`. The automation is in the certificate, untrusted,
   and imports only Lean, `IRLean` and the two generated modules.
5. If Lean accepts it, records a bundle with `tools/binding.py record`, and checks it with `tools/binding.py verify`.

A `RUN` line with any `opt` option besides `-passes=`, `-mtriple`, `-S`, `-o`, `-`, `-disable-output`, its input
and shell redirections is `unsupported`, as a run: a bundle can't represent the option, and scoring the pass without
it would be about another configuration. The research scorer dropped such options. Of the 12,662 single-pass runs in
the pinned tests, 6,444 give one, most often `-mattr`, `-mcpu`, a pass's own options, `-debug-only` or
`-aa-pipeline`.

The pass names come from [`tests/llvm_scope/inventory.json`](../tests/llvm_scope/inventory.json): every transform
the pinned LLVM registers in `PassRegistry.def`, which `tests/llvm_scope.py check` derives again from the source.

## Statuses

Each instance has exactly one. Only `bound` counts.

| Status | Means | From |
| --- | --- | --- |
| `bound` | `tools/binding.py verify` said `bound`, in this run, with exit code 0, in a verdict of schema `ir-lean.binding.verdict/1` about this manifest and this claim kind | The verdict |
| `refused` | `verify` said `refused`: the evidence doesn't bind. Never a counterexample | The verdict |
| `unsupported` | The model or a bundle can't state the claim, or `verify` said so | Step 3, or the verdict |
| `failed` | The automation found no proof (`proof_not_found`), or can't state one (`no_automation`). Never a counterexample: nothing here finds one | Lean |
| `unknown` | A time or memory limit stopped a step (`time_limit`, `resource_limit`). More may help | Any step, or the verdict |
| `error` | A tool failed, a verdict couldn't be read (`verdict_unreadable`), or a bug here | Any step |

A verdict that isn't valid JSON, has another schema, has a status whose exit code isn't the process's, names
another manifest, or is `bound` about another claim kind, is `error`, never `bound`. A test run is `skipped` when
`opt` rejects the test or fails running the pass, and `unsupported` as a run when its options or configuration can't
be represented.

The claim kind is `ir_instance_equivalence` by default. `--kind ir_instance_refinement` is accepted, and every
instance is `unsupported`, `claim_kind_unavailable`, until `IRLean` has `IRLean.Refines`. After that it's `failed`,
`no_automation`, until the automation proves refinement.

## The contract

Every file is under `WORK`, `build/passes` by default.

| File | Schema | Holds |
| --- | --- | --- |
| `bundles/KEY/manifest.json`, and the six files it names | `ir-lean.binding.manifest/1` | One instance's evidence, as `tools/binding.py record` writes it. Unchanged from [binding](llvm-proof-binding.md#the-contract) |
| `verdicts/KEY.json` | `ir-lean.binding.verdict/1` | The last verdict on `bundles/KEY`, as `tools/binding.py verify` printed it |
| `binding-cache/` | `tools/binding.py`'s own | Its `bound` verdicts, used only after it rehashes the bundle and the toolchain |
| `runs/RUNKEY.json` | `ir-lean.passes.run/1` | One `RUN` line's results, as the cache |
| `score.json` | `ir-lean.passes.score/1` | The report |
| `score.instances.json` | A list of `ir-lean.passes.instance/1` | Every instance, bound or not |

An instance record has exactly these keys: `schema`, `pass`, `test` (relative to `LLVM_PROJECT_SRC`, or absolute),
`spec`, `mtriple`, `options`, `function`, `status`, `reason`, `detail`, `bundle` (the manifest, relative to `WORK`,
or `null`), `verdict` (relative to `WORK`, or `null`), `binding_cache` (`hit`, `miss`, `stale_ignored`, or `null`)
and `source` (`fresh` or `cache`).

`RUNKEY` is the SHA-256 of the scorer's version, every hash and version `tools/binding.py` records as the toolchain,
this scorer's own bytes, the claim kind, `--timeout`, `--lean-memory`, the heartbeat limit and whether cgroups cap
memory, then the test's bytes, the pass spec, `-mtriple` and the other options. `KEY` is the first 32 hex digits of
the SHA-256 of `RUNKEY`, the function and the claim kind.

To check one instance by hand, independent of the scorer and its caches:

```console
nix develop -c tools/binding.py verify build/passes/bundles/KEY/manifest.json
```

### The cache

A run's entry is used only if its schema, key and salt are exactly this run's, and every instance's status is one
of `candidate`, `refused`, `unsupported`, `failed` or `unknown`. Anything else, such as an entry saying `bound`, a
research-scorer entry saying `certified`, or a file that isn't JSON, is `stale_ignored` and the run is done again.

**The cache never holds `bound`.** A bound instance is stored as a `candidate`, and verified again on every run,
from the bundle at the key the scorer works out itself, not at a path the entry names. `tools/binding.py` may then
answer from its own cache, but only after it rehashes the bundle, the toolchain and the pin. A bundle that's
missing or changed is `refused`. A run with an `error` isn't stored at all, since the error may not happen again.
A stored `unknown` is reused only with the same limits, which are in the key.

The research scorer's results, in `build/passes/cache` on `research/prove-llvm-optimizations`, are never read. Their
certificates were deleted, so none of the 3,679 instances it called `certified` can be replayed. `score.json`'s
`cache.legacy_cache_ignored` says whether such a directory is in `WORK`.

## The self-check

Before scoring, seven known-wrong rewrites have to fail in the proof, as `failed` or `unknown`, and one right one,
`instcombine` folding `add 1` then `sub 1`, has to be bound end to end, or nothing is scored and the exit code is 1.
The wrong ones each have `noundef` arguments, so they reach the proof: a wrong constant, an added `nuw`, poison
where there was a value, added undefined behavior, a dropped branch guard, a duplicated `freeze`, which both sides
stop the model on, and a loop that never ends. A wrong rewrite that comes back `unsupported` fails the check too,
since it never reached the proof. `score.json`'s `self_check` has each one's result.

A self-check where every mutant failed is kept in `WORK/selfcheck/SALT.json`, and its mutants' results are reused
by a run with the same salt, the run key's first part: a mutant never reaches `tools/binding.py`, so its result
depends only on this scorer, Lean, `IRLean` and the limits. A stored self-check where any mutant was proved, or is
missing, or from another salt, is ignored. The control is scored, and its bundle verified, every time.

## Limits

An uncapped run of the research scorer once filled 30 GB and the OOM killer took the agent that started it.

| Limit | Default | What enforces it |
| --- | --- | --- |
| The scorer and everything it starts, but `tools/binding.py`'s processes | 60% of RAM, less if that isn't free, keeping 3 GB, with no swap: `--memory` | A systemd scope it re-runs itself in, `OOMPolicy=continue`. `--no-scope` turns it off |
| Each process it starts | `--lean-memory` plus 512 MB, with no swap | A cgroup each, in that scope, killed whole when the process exits |
| Each Lean process | `-M` at `--lean-memory`, 3000 MB, `-j1`, and 2,000,000 heartbeats in the certificate | Lean |
| Each process | `--timeout`, 300 s, on the wall clock | The scorer, which kills its process group and cgroup |
| `tools/binding.py`'s processes | The same `--timeout` and `--lean-memory`, in scopes of their own | `tools/binding.py`, and the scorer kills those scopes if it kills `tools/binding.py` |
| Test runs at once | 1: `--jobs`, at most 2 | The scorer |

So the most it holds at once is the scorer's cap plus `--jobs` times `--lean-memory` plus 512 MB. A process stopped
by any limit, or by any signal, makes its instances `unknown`, never `bound` or `refused`. A signal to the scorer
kills everything it started, and nothing is reported.

## The report

`tests/passes.py` prints one line:

```text
done 0 passes | L4 0 | L3 0 | L2 N2 | L1 N1 | bound B of A changed functions in R runs (refused ..., unsupported ..., failed ..., unknown ..., error ...) | S s
```

L1 is a pass with a bound instance. L2 is a pass with one and nothing in its runs `refused`, `unsupported`,
`failed`, `unknown` or `error`. Both are translation validation, and neither is a step any proof here takes for
granted. L3 and L4, a pass's rewrites proved for every input and its C++ proved to make only those, and done, are 0.
`score.json` has the counts per pass, the commonest reasons, the cache's counts, every limit, the memory each tool
peaked at, and the self-check.

## Assumptions

Everything [binding](llvm-proof-binding.md#what-a-bound-verdict-rests-on) rests on, and these:

| Assumption | Why it's reasonable | What would break it |
| --- | --- | --- |
| Running one pass alone, as its regression test does, stands for the pass | It's how LLVM tests a pass | Nothing: this is part of why nothing here is done |
| The functions whose text changed, and their callers, are what the run changed | Pure functions can't read globals, and a claim is per function | A change only outside functions, which `tools/binding.py` lists in `uncovered_changes` and no claim covers |

## Not covered

- Every claim kind but `ir_instance_equivalence`. Equivalence fails on rewrites that only refine, such as removing
  undefined behavior or poison, so those come back `failed`, not wrong.
- Functions with memory or pointers, vectors (ir-lean refuses `noundef` on a vector argument), arguments that aren't
  `noundef`, functions a pass adds or removes, and target IR with `mustprogress` or `willreturn`.
- Loops and recursion: the automation runs the blocks without an invariant, so a loop runs it out of heartbeats
  or recursion depth, which is `unknown`.
- Any `opt` option but `-passes=` and `-mtriple`, pipelines, codegen, and `llc`.
- The full corpus hasn't been run with this version. The research scorer's partial results are kept, unread, on
  its branch.

## Tests

[`tests/passes_test.py`](../tests/passes_test.py) runs the scorer on three small tests in
[`tests/passes/`](../tests/passes/), not on llvm-project. See [testing](testing.md).
