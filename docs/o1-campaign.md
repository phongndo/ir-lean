# The O1 campaign

The goal is a machine-checked proof that LLVM's whole default `O1` pipeline is correct, at one pinned LLVM and one
target configuration, tied to the code that runs and covering every permitted input. This page pins what `O1` means
here, splits the pipeline into the obligations that proof needs, and keeps count of them. It also records the
evidence collected so far, what that evidence can and can't show, and what each run cost. For what any theorem here
means, see [trust](trust.md). For how a certificate is tied to an `opt` run, see [proof binding](llvm-proof-binding.md).

**`O1` isn't done, and nothing here is close.** No pass in it has an all-input proof, a binding to its C++, or a
composition proof. What exists is translation validation: 24 single steps of real `default<O1>` runs on 10 small
inputs, each bound to the exact IR before and after it. That evidence is finite. It says nothing about the next
input, so it never counts toward any of those three kinds of proof, and `complete` stays false in
[`ledger.json`](../campaign/o1/ledger.json) whatever it holds.

<!-- o1-summary: {"level": "O1", "positions": 100, "passes": 76, "families": 14, "adaptors": 13, "cases": 10, "steps": 79, "verdicts": {"bound": 24, "bound_stale": 0, "bound_unlinked": 0, "bound_unreplayed": 0, "error": 0, "not_attempted": 51, "refused": 4, "unknown": 0, "unsupported": 0}, "whole_run": {"refused:certificate_compile_failed": 2, "unsupported:trusted_promise": 8}, "discharged": 0, "complete": false, "evidence_sources": "3316530479f01c916c792d2c8acacf245bc563964632d58595e0c0d5af5a7161"} -->

## The pin

Every file in [`campaign/o1/`](../campaign/o1/) names its level, `O1`, and its pass spec, `default<O1>`.
[`pin.json`](../campaign/o1/pin.json) records the pin for each machine it was taken on. `o1.py pin --check` derives the
pin again and fails on any difference.

| What | Pinned to |
| --- | --- |
| Level | `default<O1>`: the default per-module pipeline at `O1`, not the `thinlto`, `lto` or pre-link variants |
| llvm-project | `llvmorg-23.1.3`, commit `0d261d1ca552c95a8f007e061c787ac7132fbcbc`, the repo's pin in [`tests/llvm/targets.toml`](../tests/llvm/targets.toml). GitHub resolves the tag (tag object `856f0005`) to that commit. The source tree in the dev shell has the pinned NAR hash `sha256-+e5Yv…0t4=` |
| `opt` on y, an Apple silicon Mac | `/nix/store/5lca6gn9…-llvm-23.1.3/bin/opt`, SHA-256 `2c5c0685…cb94`. Its NAR hash, deriver and the signature it was substituted with, from `cache.nixos.org`, are in `pin.json`. It's the `aarch64-darwin` build, so its hash isn't Linux's |
| Invocation | `opt -S -passes=default<O1> - -o - -mtriple=x86_64-unknown-linux-gnu`, exactly the argv `tools/binding.py` replays |
| Options | None besides those. Every `cl::opt` has its default. No `-mcpu` and no `-mattr`, so x86-64's generic CPU |
| Target | `x86_64-unknown-linux-gnu`, data layout `e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128`, which clang gives that triple. Each input has to declare both, or it's refused |
| Pipeline | What `opt -print-pipeline-passes` prints for that spec and triple, SHA-256 `ba284b24…c1a7`. It's byte for byte the merged inventory's `default<O1>` entry, which was taken on Linux, and `check` keeps it so |
| Lean | 4.35.0, from [`lean-toolchain`](../lean-toolchain) |

Why this configuration: the repo's proofs, the inventory and `tools/binding.py` all use x86-64 Linux, so evidence
taken on the Mac is about the same IR as evidence taken on Linux. Function attributes such as `target-cpu`,
`optsize` or `minsize` in an input are part of that input, and the claim covers them only as that input has them.
`O1` with `optsize` or `minsize` isn't `Os` or `Oz`: at this pin those are `O2` with the attribute, as the
[task list](llvm-verification-tasks.md) says.

## What the work is

`default<O1>` has **100 pass positions**, 73 distinct passes printed and 3 more that run implicitly:

- `loop-simplify` and `lcssa`, which every loop adaptor runs first;
- `inliner-wrapper`, the `ModuleInlinerWrapperPass` that runs the CGSCC pipeline.

Those 76 passes sit inside 13 adaptors, such as `cgscc`, `devirt<4>`, `function<eager-inv;no-rerun>` and
`loop-mssa`. [`pipeline.json`](../campaign/o1/pipeline.json) lists each position: its exact spec with parameters, the
adaptors around it, its IR unit, its inventory entry with source anchors, and its family. `opt`'s `-S` printer runs too,
but it's part of the invocation, not of `O1`, and it's recorded as such.

The obligations, as [`ledger.json`](../campaign/o1/ledger.json) counts them:

| Obligation | Count | Discharged |
| --- | --- | --- |
| All-input correctness of each pass, or soundness for an analysis | 76 | 0 |
| Each pass's C++ at the pinned hashes making only proved rewrites | 76 | 0 |
| Each position correct in its context: the adaptors around it, the analyses it reads and invalidates | 100 | 0 |
| Each adaptor: repetition, as in `devirt<4>`, SCC order, invalidation, loop canonicalization | 13 | 0 |
| Each analysis the passes read, seen on this corpus, so a lower bound | 29 | 0 |
| Checked lemmas, and instances discharged by one | none yet | 0 |

The analyses are split into 17 facts transforms rely on, such as `DominatorTree`, `ScalarEvolution`, `MemorySSA` and
`BasicAA`, 4 heuristics, such as the inline advisor, and 8 pieces of pass-manager infrastructure. Each one stays
an obligation. A heuristic's obligation is that no transform's correctness depends on it, and infrastructure's is that
every pass reads a result that's still true.

### Families

Passes whose rewrites share proof machinery are one family, so a lemma checked once can discharge instances in all of
them. For example, InstSimplify's folds are called by `instcombine`, `early-cse`, `sccp`, `simplifycfg` and
`loop-instsimplify`. [`families.json`](../campaign/o1/families.json) gives each family its passes, what they share, the
shape of proof it needs and the tasks blocking it. Every pass is in exactly one family, and `check` fails otherwise.

| Family | Passes | Positions | Steps that changed IR | Bound | Later steps its promises block | Blocked by |
| --- | --- | --- | --- | --- | --- | --- |
| attribute-inference | 4 | 5 | 10 | 0 | 8 | SEM-07, PASS-01, LOOP-03 |
| peephole-int | 7 | 14 | 21 | 6 | 0 | INV-04, SEM-01, SEM-03, SEM-04, AUTO-01, AUTO-03, PASS-03 |
| loops | 13 | 15 | 18 | 0 | 0 | SEM-07, PASS-01, LOOP-01 |
| cfg | 3 | 10 | 10 | 0 | 0 | SEM-01, SEM-07, PASS-01, PASS-04 |
| inlining-ipo | 5 | 5 | 10 | 8 | 0 | SEM-06, SEM-07, LOOP-03, PASS-05 |
| redundancy-constprop | 4 | 5 | 10 | 10 | 0 | SEM-01, SEM-06, PASS-01, PASS-04 |
| annotation-noop | 13 | 14 | 0 | 0 | 0 | SEM-08, INV-09 |
| memory-promotion | 6 | 10 | 0 | 0 | 0 | SEM-02, SEM-06, PASS-01, PASS-04 |
| dead-code | 5 | 6 | 0 | 0 | 0 | SEM-01, SEM-07, PASS-04, LOOP-03 |
| analysis-management | 5 | 5 | 0 | 0 | 0 | PASS-01, PASS-05 |
| coroutines | 5 | 5 | 0 | 0 | 0 | SEM-09 |
| libcalls | 3 | 3 | 0 | 0 | 0 | SEM-06, SEM-07, INV-05 |
| vectorization | 2 | 2 | 0 | 0 | 0 | SEM-05, SEM-06, LOOP-02 |
| fp-narrowing | 1 | 1 | 0 | 0 | 0 | SEM-05 |

"Bound" counts translation validation of single steps, and nothing more. The 8 bound `globalopt` steps only add
`local_unnamed_addr`, and the 10 bound in redundancy-constprop are `early-cse`, `sccp` and `ipsccp` steps. None of it
is a proof about any of these passes.

## How evidence is made, and what counts

```console
nix develop
lake build && cmake -S . -B build -G Ninja && ninja -C build
campaign/o1/o1.py pin --check         # this machine's opt, source and pipeline are the pinned ones
campaign/o1/o1.py capture             # every input in campaign/o1/corpus/
campaign/o1/o1.py bind --workers 3    # under the machine's heavy-job lock
campaign/o1/o1.py ledger
campaign/o1/o1.py check               # fails on stale evidence; campaign/o1/test_o1.py is ctest's o1_campaign
```

**Capture.** For each input, the pinned invocation runs twice, and the output has to be the same both times. A third
run adds `-debug-pass-manager -print-changed -print-module-scope`, and its output has to be the same as the first.
Its trace has to start at the source IR and end at the `O1` output. Each pass that changed the module becomes a step,
matched to its position in the printed pipeline, with the whole module before and after it. Each step's IR is kept in
`evidence/CASE/steps/`.

**Replay.** Each step runs alone, as `opt` with the step's own spec in its unit's adaptor, such as
`function(instcombine<max-iterations=1;no-verify-fixpoint>)`, and then in its full adaptor context. The output has to
be the captured IR byte for byte. 26 steps, all in the loop inputs, differ only in `; preds =` comments. LLVM writes
those from use-list order, which a text round trip doesn't keep. They stay unbound, under their own reason, and
`-preserve-ll-uselistorder` would need a change to the pinned invocation to fix them.

**Bind.** Each step that's left goes to [`tools/binding.py`](../tools/binding.py) unchanged: `record` writes a bundle,
and `verify` replays it from scratch and gives the verdict. The campaign writes the certificate: an attempt at
`Src.f = Tgt.f`, with the source never stopping the model, for a function that's one block on both sides. The whole
`default<O1>` run of each input is sent the same way, as one claim. A bundle counts only if its input and target are
the captured IR, by SHA-256, so a step bound to anything else is `bound_unlinked`. A run's chain to its output is
complete only if every step is bound and linked.

**What never counts.** Anything but `bound` counts as no evidence: `refused`, `unsupported`, `unknown` from a time or
memory limit, `error`, or a status the tool doesn't give. Neither does an unlinked bundle, or a step that wasn't
attempted. Nor does a cached verdict: `bind` doesn't use `tools/binding.py`'s cache, so every verdict is a full replay,
and a bound one has to end with its `unchanged` check, or it's `bound_unreplayed`.

**Stale evidence.** Each verdict records a fingerprint of the tracked files it rests on: `tools/binding.py`,
`tools/binding_check.lean`, `tests/check_axioms.lean`, IRLean's sources, the emitter, and the Lean, LLVM and Nix pins.
A bound verdict made under other sources is `bound_stale`, and counts as no evidence. The ledger names the sources its
counts hold for, as `evidence_sources`, and `check` fails when they aren't the current ones. Then `bind` and `ledger`
bring the evidence up to date, or count it stale. Before any verify, `bind` runs `lake build` and `ninja` under the
lock, so the library and `ir-lean` it checks with are built from the sources its verdicts are labeled with.

ctest runs `check` with `--allow-stale`. It still checks that the files agree with each other. On every run it reports
the counts under the current sources, with any stale evidence as `bound_stale`, and on GitHub Actions it writes them
to the job summary, where a passing test's output would otherwise be hidden. Only the machine that
recorded the bundles can bind them again. Without that flag, another lane's change to the model, the emitter or the
checker would fail every pull request until this campaign re-binds. A pull request that changes the campaign's
evidence or reports is opened only after the strict `check` passes, and says so.

A bound step is translation validation of one run, and only in IRLean's semantics, under
everything [binding](llvm-proof-binding.md#what-a-bound-verdict-rests-on) trusts. No `sorry`, axiom or weakened
claim is involved: the claim type is built by the checker, and `axioms` allows the standard three and nothing else.

## The pilot

Ten hand-written inputs in [`corpus/`](../campaign/o1/corpus/), each one function with `noundef` integer arguments
and no memory, chosen to exercise the families the binding tool can judge today. Two are loops O1 can't remove.

| Input | Steps | Bound | Chain to the `O1` output | Whole run |
| --- | --- | --- | --- | --- |
| add_mul_pow2 | 5 | 4 | broken at step 5 of 5, function-attrs: trusted_promise | unsupported, trusted_promise |
| const_branch | 6 | 4 | broken at step 1 of 6, simplifycfg: no_certificate_template | unsupported, trusted_promise |
| cse_xor | 6 | 5 | broken at step 6 of 6, function-attrs: trusted_promise | unsupported, trusted_promise |
| dead_values | 5 | 3 | broken at step 4 of 5, instcombine: certificate_compile_failed | unsupported, trusted_promise |
| diamond_phi | 5 | 1 | broken at step 1 of 5, simplifycfg: no_certificate_template | unsupported, trusted_promise |
| loop_collatz | 19 | 0 | broken at step 1 of 19, globalopt: no_certificate_template | refused, certificate_compile_failed |
| loop_invariant | 22 | 0 | broken at step 1 of 22, globalopt: no_certificate_template | refused, certificate_compile_failed |
| reassoc_consts | 3 | 2 | broken at step 3 of 3, function-attrs: trusted_promise | unsupported, trusted_promise |
| shift_mask | 4 | 2 | broken at step 3 of 4, instcombine: certificate_compile_failed | unsupported, trusted_promise |
| sub_add_cancel | 4 | 3 | broken at step 4 of 4, function-attrs: trusted_promise | unsupported, trusted_promise |

Of 79 steps, 24 are bound and 4 are refused because Lean rejects the certificate, which says the proof is missing,
never that the rewrite is wrong. The other 51 weren't attempted, each for a reason the tool would give or a
missing proof:

- 43 have more than one block on a side, which the certificate template doesn't handle. That's the refinement tactic,
  AUTO-01.
- 26 replay differently only in comments, as above.
- 8 have `willreturn` or `mustprogress` in the target.

A step can have more than one of these reasons. All 100 positions ran on some input, and 21 of them changed IR.

### The next family

**Attribute inference gates everything after it.** On every loop-free input, `function-attrs` at position 16.1.4 adds
`mustprogress` and `willreturn`. IRLean trusts those rather than checking them, so `tools/binding.py` can't bind any
later step, or the whole run. That's 8 of the 10 whole runs `unsupported`. Until breaking a promise is undefined
behavior in the model ([SEM-07](llvm-verification-tasks.md#sem-07-promises-as-ub)), no end-to-end `O1` claim on such a
function can be checked. That work belongs to the semantics lanes, so here it's blocked, not started.

`tools/binding.py` looks for the promise anywhere in the module, so a declaration of an intrinsic such as
`llvm.abs.i32`, which carries `willreturn` itself, blocks a step whose function makes no promise at all. Whether that's
too strict is the binding owner's call.

The family to work on next, among those that aren't gated, is **peephole-int**. It has the most positions, 14, and
the most changed steps, 21. Its 4 refused certificates are `select`, `range` and `Option` goals `bv_decide` can't
take after `simp`. A lemma per rewrite, checked for every width, would discharge instances across `instcombine`,
`instsimplify`, `reassociate` and the InstSimplify folds other families call. That needs the rewrite inventory
(INV-04) and the all-width work (AUTO-03) from their lanes. The campaign's part is to supply observed instances,
linked to exact IR, for them to discharge.

## What it costs, and running it on smaller machines

Every run is measured by [`measure.py`](../campaign/o1/measure.py), and the records are in
[`measurements/`](../campaign/o1/measurements/), each with its command, worker count, limits and memory before and
after. Each record keeps two peaks. The peak process is exact, from `wait4()`, with macOS's bytes and Linux's KiB both
turned into MiB. The peak tree is the sampled sum over the process group and its descendants.

Measured on y: an M4 Max with 16 cores and 64 GB, under normal memory pressure, with no swap. The evidence now
committed was verified on `main` at `a26abb3` with #48 at `f6fc339` merged. The low-memory sweep and the single-run
rows are from the first pilot, on `4cd91e5`.

| Run | Workers | Wall | Peak process | Peak tree |
| --- | --- | --- | --- | --- |
| `lake build` of `IRLean`, from clean | Lake's own | 5.8 s | 749 MiB | 1409 MiB |
| `ninja -j4` of `ir-lean`, from clean | 4 | 3.9 s | 518 MiB | 497 MiB |
| `capture` of all 10 inputs, with every replay | 1 | 10 s | 34 MiB, for one `opt` | |
| One `tools/binding.py verify` that binds | 1 | 10.3 to 11.1 s | 1523 MiB | 1836 MiB |
| One `verify` that stops at `trusted_promise`, before Lean | 1 | 6.3 s | 447 MiB | 440 MiB |
| `bind` of all 38 bundles, each replayed in full, with `lake build` and `ninja` first | 3 | 181 s | 1668 MiB | 5695 MiB |

Verifying with 3 at once took 13.0 s each at the median, against 10.8 s alone. Before this, on `4cd91e5`, the same
`bind` took 173 s and peaked at 5671 MiB.

Most of a verify's memory is three processes:

- `lean`, compiling the generated modules and the certificate against `IRLean`, peaks at 1.38 GiB of RSS. Part of
  that is the mapped `.olean` files, which Lean's `-M` doesn't count.
- `leanchecker` replaying them peaks at 0.96 to 1.2 GiB.
- `tools/binding.py` itself peaks at about 455 MiB. Its `sha256_file` and `tree_hash` read each file whole, including
  the 177 MB `libleanshared.dylib`, to hash 2.8 GiB of toolchain on every verify. Streaming the hash would remove most
  of that, and of the system time. That's the binding owner's.

The low-memory sweep, in [`lowmem-arm64-darwin.jsonl`](../campaign/o1/measurements/lowmem-arm64-darwin.jsonl), shows
where Lean's `-M` stops a step:

| `--memory` (Lean `-M`) | Verdict | Wall | Peak process | Peak tree |
| --- | --- | --- | --- | --- |
| 3000 | bound | 10.6 s | 1487 MiB | 1834 MiB |
| 1500 | bound | 11.0 s | 1487 MiB | 1832 MiB |
| 1000 | unknown, resource_limit, in the certificate | 8.3 s | 1488 MiB | 1777 MiB |
| 700 | unknown, resource_limit, in the certificate | 8.6 s | 1495 MiB | 1791 MiB |
| 500 | unknown, resource_limit, in the generated module | 6.6 s | 659 MiB | 1010 MiB |

So for this workload one verify needed `-M 1500`, and its tree peaked at about 1.9 GiB of sampled RSS. A limit too
low comes back `unknown` and never as evidence. These figures are specific to this corpus: ten small functions,
one-block certificates, and this toolchain. They're sampled, so a spike shorter than 0.25 s can be missed. The only
concurrency tested is 3 workers on 64 GB, which peaked at 5.7 GiB in all. How many workers fit on a 32 GB or smaller
machine hasn't been measured. Start there with one worker, under a `--max-tree-rss-mb` cap, and measure before adding
more.

To reproduce the sweep on another machine:

```console
campaign/o1/measure.py run --heavy --label lowmem --max-tree-rss-mb 6000 --out FILE.jsonl -- \
    tools/binding.py verify campaign/o1/evidence/add_mul_pow2/bundles/s03/manifest.json --memory 1500
```

### Limits on a Mac

macOS has no cgroups and doesn't enforce `RLIMIT_AS`, so `systemd-run` scopes, which `tools/binding.py` uses on Linux,
aren't there.

- **Memory:** Lean's `-M` caps each Lean process. When the sampled tree passes `--max-tree-rss-mb`, `measure.py`
  also kills the process and every descendant. That includes those in sessions of their own, as `tools/binding.py`
  starts each step, and a timeout does the same. The cap can overshoot by what's allocated in one 0.25 s interval.
- **Starting:** A job doesn't start unless memory pressure is normal and at least `min_available_mb` is free, as
  `vm_stat` counts it. `config.json` sets 24000 MB, with 16000 MB as the whole campaign's cap and 3 workers.
- **Heavy jobs:** These take an `flock(2)` lock at `~/Library/Caches/ir-lean/heavy-job.lock`, or
  `$XDG_CACHE_HOME/ir-lean/heavy-job.lock` elsewhere. Every checkout on the machine shares it, so two campaigns don't
  build or prove at once. Who holds it is written beside it.

`tests/verify_negative.py`'s resource limits don't hold on macOS. They're the negative-tests lane's to fix:

- At line 315 it divides `ru_maxrss` by 1024 unconditionally, so its "MB" is KiB, 1024 times too high.
- Its free-memory guard, at lines 631 to 638, reads only `/proc/meminfo`, so it's skipped silently.

## Who owns what

This campaign owns `campaign/o1/` and this page. It uses `tools/binding.py`, the inventory and the task list as they
are, and changes none of them. Each of these belongs to another lane, and here it's blocked rather than worked around:

| Needed for | Owned by |
| --- | --- |
| `IRLean.Refines` is on `main` since #46, with transitivity, and `tools/binding.py` binds `ir_instance_refinement` claims. The campaign still certifies equality only. Using refinement for steps that only refine, and chaining bound steps of one run, are its next uses. A chain would still be one run on one input, not O1 | SEM-01, refinement core |
| Promises as UB, so a target with `willreturn` can be bound | SEM-07 |
| `undef`, `freeze` and poison, for rewrites that introduce them | SEM-02, SEM-03 |
| Memory refinement, for `sroa`, `mem2reg` and `memcpyopt` | SEM-06 |
| A refinement tactic for multi-block functions, and lemmas for every width | AUTO-01, AUTO-03 |
| Per-instance scoring of LLVM's own tests, its cache and its reports | PASS-02, the replayable scorer |
| A verifier for all-input, code-binding and composition claims | BIND-03 |
| Binding to LLVM's C++ | BIND-01 to BIND-06 |

## Limitations

- Every bound step is one run of one function in IRLean's semantics, as
  [binding](llvm-proof-binding.md#what-a-bound-verdict-rests-on) describes. None of it shows anything about other
  inputs, about the C++, about native code, or about the pipeline as a whole.
- The corpus is ten small functions without memory, so most of the pipeline runs on them without changing anything.
  That 100 positions ran says only that they were reached.
- A trace's matching of passes to positions is in order, by class name, with loop and CGSCC positions allowed to run
  again. A run with several functions or SCCs would interleave positions, so the pilot keeps to one function per
  input.
- Bundles hash this Mac's toolchain, so they verify only where the toolchain hashes the same. Another machine needs
  its own pin, and its own bundles from the same steps.
