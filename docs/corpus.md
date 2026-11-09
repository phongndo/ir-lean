# The corpus

Real rewrites from LLVM, as pairs of IR: the exact module before a pass changed it, and after.
[`tools/corpus/capture.py`](../tools/corpus/capture.py) gets them by running the pinned `opt` on some inputs, one pass at a
time. It writes them to `build/corpus/`, which git ignores. Generate the corpus when you need it. Nothing in it is
committed.

The corpus is for two things:

- **Problems for the superoptimizer.** Each `before` holds code that LLVM improved, and its `after` is one answer
  that's known to exist.
- **Sources of lemmas.** Each step is one rewrite by one pass. A rewrite that turns up again and again is a candidate
  for a lemma in the store.

A pair shows what `opt` did. It doesn't show the rewrite is right. To check that, give the step to
[`tools/binding.py`](llvm-proof-binding.md) as its own claim.

## Generating it

```sh
nix develop -c tools/corpus/capture.py capture
```

If `IN_NIX_SHELL` is set, the dev shell is already active, so leave out `nix develop -c`. The command works the same
on Linux and on Apple silicon Macs. With no inputs, it captures the ten small functions in
[`tools/corpus/seeds/`](../tools/corpus/seeds/) under `default<O1>`, and writes `build/corpus/default-O1/`. That takes
about 0.4 s.

- Other inputs: pass `.ll` paths. Each input has to declare the target triple, which is `x86_64-unknown-linux-gnu`
  unless you pass `--mtriple`. An input that declares another triple is refused, because `-mtriple` would change it.
- Another pipeline: pass `--passes 'function(instcombine)'`, or any other spec `opt` accepts. Each spec gets its own
  directory, such as `build/corpus/function-instcombine/`.
- Another directory: pass `--out DIR`.

What it writes:

```text
build/corpus/default-O1/
  pin.json                         the toolchain that made every entry
  sub_add_cancel/
    capture.json                   the record for this input
    input.ll  output.ll
    steps/03-instcombine/before.ll
    steps/03-instcombine/after.ll
    ...
```

## How it finds the steps

For each input, `capture` runs `opt -S -passes=SPEC -mtriple=TRIPLE`. That's the argument list `tools/binding.py` uses.

1. It runs `opt` twice. The two outputs have to match.
2. It runs `opt` a third time with `-debug-pass-manager -print-changed -print-module-scope`. Each pass that changed
   the module becomes a step, with the whole module before and after.
3. It matches each pass that ran, in order, to the pipeline that `opt -print-pipeline-passes` prints. It uses the class
   the [inventory](../tests/llvm_scope/inventory.json) registers for each pass. That gives each step its exact spec,
   with parameters, and the adaptors around it. Some passes run without being in the pipeline, such as the
   `loop-simplify` and `lcssa` that every loop adaptor runs first. Those steps are marked `implicit`, and they're named
   after their class.
4. It runs each step again on its own. First it tries the pass in its own unit's adaptor, such as
   `function(instcombine<max-iterations=1;no-verify-fixpoint>)`. Then it tries the pass inside every adaptor around
   it. A step counts as `reproduced` only if one of those runs gives its `after` byte for byte.

A replay can miss only because of `; preds =` comments. LLVM writes those from use-list order, and a text round trip
doesn't keep that order. Those steps are flagged `replay_differs_only_in_comments`, and they don't count as
reproduced.

On the seeds, with this pin, on z on 2026-11-08: 10 inputs and 79 steps. 53 steps replayed alone byte for byte, and
the other 26 differ only in those comments. Those are the same counts the O1 pilot in #52 got on y.

`capture.json` has these fields:

| Field | Meaning |
| --- | --- |
| `status` | `captured`. Or `inconsistent` when a check below fails, `refused` for the wrong triple, or `error` when `opt` failed |
| `deterministic` | Both runs gave the same output |
| `trace_output_matches`, `trace_starts_from_input`, `trace_ends_at_output` | The traced run gave the same output, its first module is the input as `opt` prints it, and its last module is the output |
| `opt_sha256`, `pipeline_sha256`, `input_sha256`, `output_sha256` | What made the entry, and what it's about |
| `steps[]` | `k`, `name`, `spec`, `class`, `unit` (what it ran on), `pos` (where it is in the printed pipeline), `implicit`, `again` (a loop, CGSCC or function pass run again), `before` and `after` with their SHA-256, `replay_tried`, `replay`, `reproduced`, `replay_differs_only_in_comments` |

## The toolchain

`pin.json` records:

- the path, SHA-256 and version of `opt`;
- the pipeline it prints for the spec, with that pipeline's SHA-256.

On Nix, the runpath of `opt` names its libLLVM by store path, so the hash of `opt` changes whenever that library
changes. Every `capture.json` repeats both hashes.

`capture` refuses to run in any of these cases:

- `opt` isn't the LLVM pinned in [`tests/llvm/targets.toml`](../tests/llvm/targets.toml);
- the pipeline isn't the inventory's, byte for byte;
- the directory holds a corpus that another `opt` or pipeline made.

`tools/corpus/capture.py pin --check` runs the same checks without capturing anything. No pin is committed: the hash
of `opt` differs between Linux and macOS, and it changes whenever `flake.lock` does, so each corpus records its own.

## Measuring a heavy job

[`tools/measure.py`](../tools/measure.py) runs a command under a timeout and a memory cap, through the shared
library's [`irlean.proc`](../tools/irlean/proc.py), which every tool and test runs its commands with
([Python](python.md)). It records:

- wall and CPU time;
- the exact peak RSS of the process, from `ru_maxrss`, which is in bytes on macOS and KiB on Linux, both turned into
  MiB;
- the sampled peak RSS of the whole process tree.

When the command hits the cap or the timeout, `measure.py` kills every descendant, including descendants in sessions of
their own, as `tools/binding.py` starts its steps.

With `--heavy`, it first takes a slot in a pool of heavy jobs shared by every checkout on the machine, so they don't
run the machine out of memory together:

- **Slots:** one per 3.5 GB of RAM, a Lean process's peak in the `binding` test, at least one, or
  `IR_LEAN_HEAVY_SLOTS`. Each is an `flock` of its own.
- **Memory:** a job declares what it needs with `--max-tree-rss-mb`, which is also its cap, or 3.5 GB without one. It
  takes a free slot only if available memory, less what the jobs in other slots may still grow into, less its need,
  stays above a reserve: a tenth of RAM, at least 2 GB, or `IR_LEAN_HEAVY_RESERVE_MB`. Otherwise it waits, up to
  `--lock-wait` seconds. A job alone in the pool starts whatever memory says.
- **Older checkouts:** one still on the single lock takes `heavy-job.lock` exclusively, and each slot holds it shared,
  so such a job still runs alone.
- **Where:** in the platform's cache directory, `~/Library/Caches/ir-lean/` on macOS and `$XDG_CACHE_HOME/ir-lean/`,
  or `~/.cache/ir-lean/`, on Linux. Every lock is released when its process exits, however it exits.

`tools/measure.py pool` prints the slots, the reserve, what's available and who holds each slot.

```sh
nix develop -c tools/measure.py run --label 'lake build' --heavy --max-tree-rss-mb 16000 \
  --out build/measurements.jsonl -- lake build
```

The `corpus` test checks the capture in under a second, and `irlean` checks `measure.py` and the library under it in
about 3 s. Neither needs Lean. When the pinned `opt` is on `PATH`, `corpus` also captures one seed, and otherwise it
skips that part.
