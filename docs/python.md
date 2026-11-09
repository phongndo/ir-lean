# Python

What the repo's Python is for, the library every script shares, and the rules that keep it small. Facts here were
checked at commit `3d7bffb` on 2026-11-09 unless they say otherwise.

## Python is glue

The project is a Lean semantics, a C++ emitter and proofs. Python runs them: it starts `opt`, `clang`, the emitter,
Lean and Alive2, compares what they print, and writes results as JSON. It stays the glue, and nothing more. Anything in
it that shows a memory or speed problem moves to C++.

It had grown past that. It was 1,534 lines in 5 files at `70bfcb3`, the last commit before 2026-11-07 UTC, 5,401 in 12 at
`2bf52f0`, the last that day, and 25,641 in 48 at `3d7bffb`, more than all the Lean, 20,464 lines, and five times the
model, 4,712 lines in `IRLean.lean` and `IRLean/`. Every lane wrote its own glue: its own command runner, SHA-256
helper, Lean invocation and process killing, and the readers of four schemas declared them again.

| Directory | Lines at `3d7bffb` | Files |
| --- | ---: | ---: |
| `tests/` | 14,242 | 27 |
| `tools/` | 3,056 | 3 |
| `tests/llama/` | 2,608 | 11 |
| `tools/prooftest/` | 2,428 | 2 |
| `prototypes/lemma-reuse/` | 1,724 | 2 |
| `tools/store/` | 943 | 1 |
| `tools/corpus/` | 568 | 1 |
| `.github/` | 72 | 1 |
| Total | 25,641 | 48 |

Python is also in the trust path. Lean's kernel checks a proof, but Python decides which file, which theorem and which
verdict count, and that has gone wrong three times: a crashed native check counted as catching a wrong rewrite, a slice
that failed to compile counted as a refutation, both in [#57](https://github.com/phongndo/ir-lean/pull/57), and a scorer
counted cached results whose certificates were gone, in [#51](https://github.com/phongndo/ir-lean/pull/51).

## The shared library

[`tools/irlean`](../tools/irlean) is the one place each of these is done. It needs nothing beyond the standard library,
as [`pyproject.toml`](../pyproject.toml) requires.

| Module | What it does |
| --- | --- |
| [`proc`](../tools/irlean/proc.py) | Runs a command in a session of its own, under a timeout and a memory cap, and kills everything it started at either limit, descendants in sessions of their own included. The cap is sampled from `ps`, a systemd scope, or `RLIMIT_AS`. Measures wall and CPU time and peak RSS, and holds the machine's heavy-job lock. A limit is never a success |
| [`hashing`](../tools/irlean/hashing.py) | SHA-256 of bytes, text and files, a piece at a time, and of trees, on several threads, read back one way, refusing links to anything unhashed, as [binding](llvm-proof-binding.md) needs |
| [`lean`](../tools/irlean/lean.py) | `lean` with `-M` and 64 MB thread stacks, `leanchecker`, `LEAN_PATH`, the pinned toolchain, Lean's messages, the limits it reports, and the axiom audit through [`tests/check_axioms.lean`](../tests/check_axioms.lean) |
| [`schemas`](../tools/irlean/schemas.py) | Every versioned JSON schema the repo writes, named once, and reading, writing and checking records of them |
| [`pins`](../tools/irlean/pins.py) | The toolchain the repo pins, in `tests/llvm/targets.toml`, `lean-toolchain` and `nix/shell.nix`, and the binaries on `PATH`, each by resolved path, SHA-256 and version |

A script reaches it by putting `tools/` on its path first, as Python looks only next to the script:

```python
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
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
