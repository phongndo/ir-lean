# Python

What the repo's Python is for, the library every script shares, and the rules that keep it small. Facts here were
checked on 2026-11-09: the code before the library at commit `3d7bffb`, and the rest once `tools/` and `tests/` were on
it.

## Python is glue

The project is a Lean semantics, a C++ emitter and proofs. Python runs them: it starts `opt`, `clang`, the emitter,
Lean and Alive2, compares what they print, and writes results as JSON. It stays the glue, and nothing more. Anything in
it that shows a memory or speed problem moves to C++. Since
[2026-11-10](roadmap.md#names-and-languages-decided-on-2026-11-10), most work is C++, and the command line and MCP
server agents use, [irl](irl.md), are Go.

It had grown past that. It was 1,534 lines in 5 files at `70bfcb3`, the last commit before 2026-11-07 UTC, 5,401 in 12 at
`2bf52f0`, the last that day, and 25,641 in 48 at `3d7bffb`, more than all the Lean, 20,464 lines, and five times the
model, 4,712 lines in `IRLean.lean` and `IRLean/`. Every lane wrote its own glue: its own command runner, SHA-256
helper, Lean invocation and process killing, and the readers of four schemas declared them again.

Python is also in the trust path. Lean's kernel checks a proof, but Python decides which file, which theorem and which
verdict count, and that has gone wrong three times: a crashed native check counted as catching a wrong rewrite, a slice
that failed to compile counted as a refutation, both in [#57](https://github.com/phongndo/ir-lean/pull/57), and a scorer
counted cached results whose certificates were gone, in [#51](https://github.com/phongndo/ir-lean/pull/51).

## The shared library

[`tools/irlean`](../tools/irlean) is the one place each of these is done. It needs nothing beyond the standard library,
as [`pyproject.toml`](../pyproject.toml) requires.

| Module | What it does |
| --- | --- |
| [`proc`](../tools/irlean/proc.py) | Runs a command in a session of its own, under a timeout and a memory cap, and kills everything it started at either limit, descendants in sessions of their own included. The cap is sampled from `ps`, a systemd scope, or `RLIMIT_AS`. Measures wall and CPU time and peak RSS, and holds a slot in the machine's [pool of heavy jobs](corpus.md#measuring-a-heavy-job), one per 3.5 GB of RAM, which waits while memory is short. A limit is never a success |
| [`hashing`](../tools/irlean/hashing.py) | SHA-256 of bytes, text and files, a piece at a time, and of trees, on several threads, read back one way, refusing links to anything unhashed, as [binding](llvm-proof-binding.md) needs |
| [`lean`](../tools/irlean/lean.py) | `lean` with `-M` and 64 MB thread stacks, `leanchecker`, `LEAN_PATH`, the pinned toolchain, Lean's messages, the limits it reports, and the axiom audit through [`tests/check_axioms.lean`](../tests/check_axioms.lean) |
| [`schemas`](../tools/irlean/schemas.py) | Every versioned JSON schema the repo writes, named once, and reading, writing and checking records of them |
| [`model`](../tools/irlean/model.py) | What the model declares that Python needs: `IRLean.UB`'s and `IRLean.ModelStop`'s constructors, read from `IRLean/Basic.lean` and checked against what Lean reads, so no tool keeps a copy that goes stale |
| [`pins`](../tools/irlean/pins.py) | The toolchain the repo pins, in `tests/llvm/targets.toml`, `lean-toolchain` and `nix/shell.nix`, and the binaries on `PATH`, each by resolved path, SHA-256 and version |

A script reaches it by adding `tools/` to its path, as Python looks only next to the script. It goes last, not
first, since `tools/` holds `measure.py`, `verify.py` and `binding.py`, which would shadow the scripts of those names in
`tests/`:

```python
ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import hashing, proc  # noqa: E402
```

[`tools/measure.py`](../tools/measure.py) is now a command-line tool over `proc`, with the same options and the same
record, `ir-lean.measurement/1`, as before. The `irlean` test checks the library in about 3 s, with no Lean or LLVM.

### What changed in how a command runs

`proc.run` keeps what each of the runners it replaces did, and does four things some of them didn't:

- It waits for a command without reaping it, then stops the timer and the sampler and kills its group, and only then
  reaps it. A runner that reaped first could, in principle, kill a process that had since been given the same pid.
- Captured output goes through temporary files, as `tools/binding.py`'s runner did, not pipes. A command is done when it
  exits, not when everything it started closes its output.
- Output comes back as bytes, decoded with replacement where text is asked for, rather than failing on bytes that
  aren't UTF-8.
- A systemd scope gets `OOMPolicy=kill`, so past its cap the kernel kills everything in it at once, and the result says
  `resource_limit`. Without it, the OOM killer killed one process, and a parent that ignored the child it lost could
  exit 0, which a test on 2026-11-09 reproduced. `tools/binding.py`'s scopes didn't have it.

### Before and after

Lines of Python at `3d7bffb`, before the library, and on 2026-11-09, once `tools/` and `tests/` were on it. The
Python of F3 and BIND-01, which landed in between, is set apart:

| Directory | Before | After | F3's and BIND-01's | This work's |
| --- | ---: | ---: | ---: | ---: |
| `tests/` | 14,242 in 27 | 15,577 in 29 | +94 | +1,241 |
| `tools/` | 3,056 in 3 | 2,695 in 3 | 0 | −361 |
| `tests/llama/` | 2,608 in 11 | 2,604 in 11 | 0 | −4 |
| `tools/prooftest/` | 2,428 in 2 | 2,452 in 2 | +3 | +21 |
| `tools/irlean/` | 0 | 1,728 in 8 | 0 | +1,728 |
| `prototypes/lemma-reuse/` | 1,724 in 2 | 1,724 in 2 | 0 | 0 |
| `tools/store/` | 943 in 1 | 972 in 1 | 0 | +29 |
| `tools/corpus/` | 568 in 1 | 556 in 1 | 0 | −12 |
| `.github/` | 72 in 1 | 72 in 1 | 0 | 0 |
| `prototypes/binding/` | 0 | 53 in 1 | +53 | 0 |
| Total | 25,641 in 48 | 28,433 in 59 | +150 | +2,642 |

There's more Python, not less. The library is 1,728 of the 2,642 new lines, 355 of them `tools/measure.py`'s, and its
tests, `tests/irlean_test.py` and `tests/verdict_test.py`, are 1,313. The code that moved onto the library is 399 lines
shorter, after the lines it gained to send each verdict through `irlean.verdict`.

What each script did for itself, outside the library, its tests and the prototypes:

| Done in each script | Before | After | What's left |
| --- | ---: | ---: | --- |
| Files importing `subprocess` | 40 | 2 | `.github/needs-tests.py`, `tests/verify.py`: exceptions, below |
| Files importing `hashlib` | 26 | 1 | `tests/llama/rewrite.py`: an exception |
| SHA-256 helpers | 19 | 1 | `tests/llama/rewrite.py`'s, an exception |
| Kills, new sessions and rlimits | 22 | 0 | One `os.kill` is left, in a child `tests/replay_challenge.py` starts to crash itself |
| Lean limit patterns | 6 | 0 | Each is `irlean.lean.LIMIT`. `tests/store_test.py` keeps a broader one, on purpose: a refusal it expects mustn't mention a limit at all |
| Lean error patterns | 4 | 1 | `tests/passes.py`'s, which also captures the message |
| Schema names outside the registry | 28 | 2 | `tests/replay_challenge.py` writes `tools/binding.py`'s contract out to catch a change to it, and `tests/verify_negative.py` bumps a schema to check it's refused |
| Copies of `IRLean.UB` | 1 | 0 | |

Every `run` or `sh` left in a script, but for the exceptions below, calls `proc.run`. Nine are 3 to 10 lines. Three do more around the call:

- `tests/passes.py`'s registers what it starts for its owner token and kills scopes left behind;
- `tools/verify.py`'s gives each command what's left of the check's time limit, and records it in the result;
- `tests/llama/reproduce.py`'s writes each command's log for the record.

## The rules that keep it this way

- **Commands, hashes and process killing go through the library.** `ruff check` bans `subprocess`, `hashlib`,
  `os.kill`, `os.killpg`, `os.wait4`, `os.waitpid`, `os.waitid`, `os.setsid`, `os.setpgid` and `resource.setrlimit`
  everywhere else, through its banned-API rule, `TID251`, in [`pyproject.toml`](../pyproject.toml). The lint job runs it
  on every pull request.
- **A verdict comes from [`irlean.verdict`](../tools/irlean/verdict.py).** Proved, certified, refuted and caught are
  granted there and nowhere else: see [trust](trust.md#where-python-decides-a-verdict).
- **A schema is named once, in [`irlean.schemas`](../tools/irlean/schemas.py).** No file in `tools/` but BIND-03's
  verifier, below, names one any other way, and a schema a tool writes that the registry doesn't name fails the `irlean`
  test.
- **What the model declares is read from it, through [`irlean.model`](../tools/irlean/model.py).** No Python file
  but BIND-03's verifier keeps a copy of `IRLean.UB`'s or `IRLean.ModelStop`'s constructors, or reads
  `IRLean/Basic.lean` itself, and a constructor added to `IRLean.UB` has to change what each tool that reads them sees.

The `irlean` test checks the exceptions to the first rule are these, so adding one means saying why:

| File | Why it's an exception, on 2026-11-10 |
| --- | --- |
| `tools/irlean/*.py` | The library, where these live |
| `tests/irlean_test.py` | It checks `irlean.proc` and `irlean.hashing` from outside, against the standard library |
| `.github/needs-tests.py` | It runs in CI before the dev shell exists, on the runner's own Python, so it stands alone |
| `prototypes/**/*.py` | Research prototypes outside CI, which reproduce what [lemma reuse](lemma-reuse.md) and [binding](binding-approach.md) measured, and which nothing here runs, so they aren't changed untested |
| `tests/llama/rewrite.py` | Its own SHA-256 is recorded in committed evidence, `tests/llama/results/2026-11-07/rewrite-witness.json`, so editing it invalidates that evidence |
| `tests/verify.py` | It checks `tools/verify.py` leaves nothing running, which `irlean.proc` would clean up before it looked |
| `tools/verify_claims.py`, `tools/verify_claims/**/*.py` | [BIND-03](llvm-verification-tasks.md#bind-03-an-independent-verifier)'s independent verifier, which shares no code with any scorer: it runs commands and hashes itself and never imports `irlean`. The schema and model rules don't reach it either |

## Python is glue, and what moves to C++

The rule, the maintainer's on 2026-11-09: Python is glue, and anything in it that shows a memory or speed problem
moves to C++, as the emitter is.

Measured on 2026-11-09 on z, with 32 cores and 31,129 MB, after `tools/` and `tests/` moved onto the library: each
main tool once on a CI-sized input, one at a time under the heavy-job lock. `tools/measure.py` measured the whole tree,
and a wrapper read the Python process's own CPU time and peak RSS, apart from the processes it started:

| Run | Wall | Python CPU | Python peak | CPU of what it ran | Tree peak | Largest process |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `tools/verify.py check`, `control_mul2_to_shl1` | 2.1 s | 0.07 s | 32 MiB | 2.4 s | 2,431 MiB | `lean`, 2,399 MiB |
| `tools/binding.py record`, `tests/binding/add_zero.ll` | 1.1 s | 2.34 s | 100 MiB | 0.1 s | 101 MiB | `python3`, 101 MiB |
| `tools/binding.py verify`, that bundle | 4.9 s | 2.84 s | 100 MiB | 3.6 s | 1,591 MiB | `lean`, 1,503 MiB |
| `tools/prooftest/bench.py --check-t1`, two workers | 56.2 s | 1.39 s | 41 MiB | 128.6 s | 3,286 MiB | `lean`, 1,635 MiB |
| `tools/store/store.py check` | 6.9 s | 0.06 s | 27 MiB | 18.9 s | 4,618 MiB | `leanchecker`, 1,689 MiB |
| `tools/corpus/capture.py capture`, every seed | 0.3 s | 0.11 s | 31 MiB | 0.9 s | 31 MiB | `python3`, 31 MiB |
| `tests/passes.py`, the two `passes` fixtures | 96.6 s | not separated | 105 MiB | about 238 s | 5,668 MiB | `lean`, 3,558 MiB |
| `tests/llvm_scope.py check` | 10.2 s | 9.37 s | 206 MiB | 3.7 s | 748 MiB | `python3`, 202 MiB |
| `tests/differential.py`, `differential`'s three files | 3.4 s | 0.06 s | 28 MiB | 4.1 s | 892 MiB | `lean`, 863 MiB |

The scorer runs itself again in a systemd scope of its own, which the wrapper doesn't follow, so its own CPU time isn't
separated. Its Python processes peaked at 105 MiB, and the tree's 238 s of CPU is mostly Lean's.

No Python process peaked above 206 MiB, so none shows a memory problem. Two spend their time in Python, and are the
candidates for C++, not ported here:

- **`tests/llvm_scope.py check`**, 9.4 s of Python CPU in a 10.2 s run: it derives the inventory of LLVM's passes
  again from its source, `opt` and `llc`, and its time is its own, not `opt`'s or `llc`'s. It grows with LLVM, not with what the repo proves, and runs once per CI run, in `rest`.
- **`tools/binding.py`'s toolchain hash**, 2.3 to 2.8 s of Python CPU each time it records or verifies a bundle: it
  hashes the Lean toolchain and IRLean's library, on several threads since #63. It's paid per bundle, so the scorer,
  which verifies every bound instance, pays it per instance: about 2.8 s each, against the seconds Lean takes. It's the
  one to move if scoring grows to a whole corpus.

Everything else spends under 1.4 s in Python, against Lean's seconds or minutes.
