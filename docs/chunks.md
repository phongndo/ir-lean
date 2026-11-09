# Chunks and gates

How `ir-lean` proves LLVM's optimizations, the main program since 2026-11-09: the pinned LLVM's 1,162 registered pass
names in nine chunks, the five gates each chunk goes through, how each gate's percentage is measured, and where each
chunk stands. The [roadmap](roadmap.md#six-decisions-of-2026-11-09-after-69) has the decision and its reasons, and the
[platform track](roadmap.md#the-platform-track) the chunks pull from. The [task list](llvm-verification-tasks.md)
defines what done means, and holds the inventory and the tasks. For what any theorem means, see [trust](trust.md).

Facts here were checked on 2026-11-09 on top of `dbfd710`, against the inventory of LLVM 23.1.3 in
[`tests/llvm_scope/inventory.json`](../tests/llvm_scope/inventory.json).

## The headline

**0 of the 1,162 passes are done.** A pass is done when
[BIND-03](llvm-verification-tasks.md#bind-03-an-independent-verifier), the independent verifier, accepts its
all-input, code-binding and composition claims for every context it runs in. Since 2026-11-09 it's
[`tools/verify_claims.py`](verify-claims.md), and it refuses every claim whose coverage it can't decide yet: all-input
until it reads INV-04's lists of rewrites, which exist for chunk 1, code-binding until BIND-02 gives a pass's complete
closure, and composition until PASS-05. So
`tests/llvm_scope.py summary` counts `verified_done` as 0.

Under that, each chunk's percentage at each gate:

| # | Chunk | G0 Coverage | G1 Instances | G2 All inputs | G3 Bound | G4 Composed |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | Peepholes | Not measured. InstCombine alone: 38.4% | Not measured | Not measured | Not measured | 0 of 4 |
| 2 | Scalar, no memory | Not measured | Not measured | Not measured | Not measured | 0 of 63 |
| 3 | Memory | Not measured | Not measured | Not measured | Not measured | 0 of 41 |
| 4 | Loops | Not measured | Not measured | Not measured | Not measured | 0 of 37 |
| 5 | Interprocedural | Not measured | Not measured | Not measured | Not measured | 0 of 82 |
| 6 | Vectorization | Not measured | Not measured | Not measured | Not measured | 0 of 10 |
| 7 | Pipelines | Not measured | Not measured | Not measured | Not measured | 0 of 20 |
| 8 | Codegen | Not measured | Not measured | Not measured | Not measured | 0 of 673 |
| 9 | The rest | Not measured | Not measured | Not measured | Not measured | 0 of 232 |

[Chunk 1](#1-peepholes) has the one number measured, and what it rests on.

## The gates

| Gate | Means | A chunk's percentage | What it is in the task list's terms |
| --- | --- | --- | --- |
| G0 Coverage | The model can express the chunk's own regression tests | Of the pairs the chunk's regression tests give, the share whose two sides both translate | Nothing toward done. It says which pairs G1 can try |
| G1 Instances | Its test transformations are certified | Of the same pairs, the share certified | [`translation-validation`](llvm-verification-tasks.md#translation-validation-isnt-proof-for-all-inputs), which never counts toward done |
| G2 All inputs | Every rewrite is proved for every input, and stored as lemmas | Of the chunk's rewrites, as INV-04 lists them, the share proved for every input and stored | `all-input`, or `analysis-soundness` for an analysis |
| G3 Bound | Tied to its C++, by BIND's rule | Of the functions in the chunk's passes' code, the share bound | `code-binding` |
| G4 Composed | Correct in its pipelines. Then it counts as done | Of the chunk's passes, the share BIND-03 counts done | `composition`, and the verifier accepting all three dimensions |

### How each is measured

- **G0.** A pair is one function from one of a pass's own regression tests at the pin, before and after `opt` runs
  that pass on it. The function the pass changes is cut into a module of its own with `llvm-extract`, and the pass runs
  again on that alone, so the pair is a run a certificate can bind. Functions the pass leaves unchanged aren't pairs.
  The share is the pairs where `ir-lean --report` refuses neither side, over every pair. A function with memory or
  pointers translates, and counts here, but `IRLean.Refines` can't state its claim until F4, so it can't count at G1
  until then. S1's harness, `bench/instcombine/stage1.py`, makes InstCombine's pairs this way. It isn't on `main` yet.
- **G1.** The same pairs as G0, so a chunk's G1 is never above its G0. The share is the pairs whose verdict is
  `certified`: `tools/binding.py verify` said `bound` about the pair's `ir_instance_refinement` claim, as
  [binding](llvm-proof-binding.md) defines it. A pair Lean proves and nothing binds doesn't count. S1's metric, the
  share of InstCombine's own test transformations certified, is this gate for InstCombine.
- **G2.** The units are [INV-04](llvm-verification-tasks.md#inv-04-rewrite-level-inventory)'s: a pass's rewrites, each
  with a stable ID and a source location, and for an analysis each kind of fact it reports. INV-04's scope names
  InstCombine's and InstSimplify's rewrites and codegen's patterns. For the other passes, its units are written down
  when their chunk reaches G2, and until then G2 isn't measured for them. A unit counts when it's proved for every
  permitted input, at every width as [AUTO-03](llvm-verification-tasks.md#auto-03-from-instances-to-every-width) asks,
  over the inputs [INV-05](llvm-verification-tasks.md#inv-05-permitted-inputs-and-options) sets, checked by the
  kernel with only the standard axioms, and its lemmas are in the [lemma store](lemma-store.md) meeting the first three
  rules of the [bar](roadmap.md#the-flywheel), as `tools/store/store.py check` checks. A rewrite proved only at some
  widths, or only on G1's pairs, doesn't count.
- **G3.** The units are the functions in the closure
  [BIND-02](llvm-verification-tasks.md#bind-02-implementation-closure) finds for the chunk's passes, at the pinned
  hashes: each a C++ function as the pinned build compiles it, after inlining, as
  [binding a proof to LLVM's C++](binding-approach.md#two-theorems-per-unit) defines a unit. One counts when it has both
  theorems, that its model is right for every input and that its compiled code computes the model, with no call cut,
  as [a `code-binding` claim's evidence](binding-approach.md#what-a-code-binding-claims-evidence-is) requires. Until
  BIND-02 finds a chunk's closure, its G3 isn't measured.
- **G4.** The units are the chunk's passes in [`tests/llvm_scope/chunks.json`](../tests/llvm_scope/chunks.json). One
  counts when BIND-03 counts it done, which is `verified_done` in `tests/llvm_scope.py summary`, by chunk. The headline
  is the sum over the chunks.

A chunk's percentage at a gate pools its passes: every pass's counted units over every pass's units, not an average of
the passes' percentages. Where only some of a chunk's passes are measured, the chunk isn't, and each measured pass's
number is given beside it, as for InstCombine now.

Some gates don't fit some kinds of pass as stated: G0 and G1 for an analysis, which changes no IR, for chunk 7's
pipeline names, and for machine passes, whose tests aren't IR in and IR out. For those, the chunk's G0 work writes down
what a pair is before anything is measured, and until then the cell says not measured.

## The chunks

Every one of the 1,162 registered names is in exactly one chunk, analyses included.
[`tests/llvm_scope/chunks.json`](../tests/llvm_scope/chunks.json) has each chunk's list, and the [test](#the-test)
checks the counts in this table against it and the inventory:

| # | Chunk | Passes | Analyses among them | In `default<O2>` | In `llc`'s pipelines |
| --- | --- | --- | --- | --- | --- |
| 1 | Peepholes | 4 | 0 | 4 | 1 |
| 2 | Scalar, no memory | 63 | 25 | 16 | 30 |
| 3 | Memory | 41 | 13 | 17 | 14 |
| 4 | Loops | 37 | 6 | 14 | 12 |
| 5 | Interprocedural | 82 | 13 | 24 | 5 |
| 6 | Vectorization | 10 | 0 | 4 | 2 |
| 7 | Pipelines | 20 | 6 | 2 | 2 |
| 8 | Codegen | 673 | 66 | 0 | 455 |
| 9 | The rest | 232 | 13 | 6 | 19 |
| | All | 1,162 | 142 | 87 | 540 |

"In `default<O2>`" counts the passes and required analyses `opt` prints for that pipeline, and "In `llc`'s pipelines"
the passes `llc` runs for any of its 48 target names at any level, on the inventory's two probe modules, as the
[task list](llvm-verification-tasks.md#the-measured-scope) measures them.

What each chunk needs from the [platform track](roadmap.md#the-platform-track), as decided:

| # | Chunk | The passes the decision names | Needs from the platform |
| --- | --- | --- | --- |
| 1 | Peepholes | InstSimplify, InstCombine, AggressiveInstCombine, Reassociate | INV-04, `freeze` (done), every-width proofs, floating point and external calls for coverage. Its smallest pass is the first try at BIND-06 |
| 2 | Scalar, no memory | SCCP, CorrelatedValuePropagation, ADCE and BDCE, SimplifyCFG, JumpThreading, DivRemPairs, ConstraintElimination | Sound dominators, known bits and lazy value info (PASS-01) |
| 3 | Memory | SROA, mem2reg, EarlyCSE, GVN and NewGVN, DSE, MemCpyOpt | Memory in `Refines` (SEM-06), sound alias analysis and MemorySSA |
| 4 | Loops | loop-simplify, LCSSA, rotate, LICM, IndVarSimplify, unroll, deletion, LSR | Sound scalar evolution. SEM-07 (done) |
| 5 | Interprocedural | Inliner, function-attrs, GlobalOpt, IPSCCP, ArgPromotion, DeadArgElim, devirtualization, ThinLTO | Composition, open modules |
| 6 | Vectorization | LoopVectorize and VPlan, SLP, the load-store vectorizer | Floating point, memory, chunk 4 |
| 7 | Pipelines | Composition across `O0` to `O3` and the LTO pipelines | Chunks 1 to 5 for `O1`'s passes, then `O2` and `O3` |
| 8 | Codegen | Selection, legalization, machine passes, then one target at a time: X86, AArch64 and RISC-V first, then AMDGPU and the rest | A machine-level semantics for each target |
| 9 | The rest | The 129 printers, verifiers and debug aids, and the 36 instrumentation passes | A ruling on what "proved" means for each kind (INV-09) |

A transform's proof can rest on analyses another chunk holds: InstCombine reads dominators, assumptions and target
library information, which are chunk 2's, and alias analysis, which is chunk 3's. A rewrite proved assuming an
analysis's facts counts at G2. The pass's G4 also needs those analyses' own G2, since composition is with the analyses a
pass reads.

### 1. Peepholes

`instsimplify`, `instcombine`, `aggressive-instcombine` and `reassociate`, all four in `default<O2>`. It goes first:
the peepholes build the lemmas the next chunks use.

| Gate | Needs from the platform |
| --- | --- |
| G0 | Coverage the emitter lacks: floating point, SEM-05, external calls and globals, and the long tail of refusals, SEM-08 |
| G1 | `freeze` is in the model since [#72](https://github.com/phongndo/ir-lean/pull/72). `tools/binding.py` binds a pair only when its function uses no memory or pointers and every argument of its source is `noundef`: a caller can pass `undef` to any other argument, and the model keeps `undef` out. So F4 for pairs with memory, and nothing yet decided for pairs whose arguments lack `noundef` |
| G2 | INV-04's list of rewrites, every-width proofs (AUTO-03), and the tactics, AUTO-01 to 03. The lemma store, E1, is done. Lemma mining at scale, E3, is this gate's burn-down |
| G3 | BIND-02's closure, then binding gates B1 to B4 as [#74](https://github.com/phongndo/ir-lean/pull/74) sets them: BIND-04 for reading IR, the emitter taking the matcher layer whole, `simplifyAddInst` bound, then code that changes IR. The pass whose closure BIND-02 finds smallest is the first try at BIND-06, gate B5 |
| G4 | BIND-03, composition (PASS-05), and the G2 of the analyses its passes read, in chunks 2 and 3 |

Where it stands:

| Pass | G0 | G1 | G2 | G3 | G4 |
| --- | --- | --- | --- | --- | --- |
| `instcombine` | 38.4%: 12,002 of 31,240 pairs translate | Not measured | Not measured | Not measured | Not done |
| `instsimplify` | Not measured | Not measured | Not measured | Not measured | Not done |
| `aggressive-instcombine` | Not measured | Not measured | Not measured | Not measured | Not done |
| `reassociate` | Not measured | Not measured | Not measured | Not measured | Not done |

InstCombine's G0 is from S1's run before F3 landed, as recorded with the decision of 2026-11-09. That run's summary
isn't on `main` yet, and nor is S1's harness. S1 is finishing, with G1 for InstCombine. Then G0 and G1 are measured
across chunk 1's other three passes.

What exists and doesn't count yet:

- **33 rewrites proved for every width,** from InstSimplify and InstCombine, in
  [#48](https://github.com/phongndo/ir-lean/pull/48) ([generic rewrites](generic-rewrites.md)), with their lemmas in
  the store. They were chosen by hand, so they aren't a share of G2 until INV-04's list exists to count them against.
- **Gate B0:** the [prototype](binding-approach.md#the-prototype) proves the compiled `llvm::isKnownNegation` computes
  #47's model of it, with 6 calls out of the module cut. A function with a cut doesn't count at G3.

### 2. Scalar, no memory

The decision's eight, the other scalar and control-flow transforms that read and write no memory, and the analyses
transforms read most: dominators and post-dominators, assumptions, lazy value info, demanded bits, cycles and regions,
branch probabilities and block frequencies, and target and library information. Known bits isn't a registered pass.
It's ValueTracking, which passes in most chunks call, and PASS-01 proves it sound with this chunk's analyses.

Some of these analyses only steer heuristics: block frequencies, profile summaries and optimization remarks. What G2
means for one of them, that every pass reading it is right whatever it answers, is for PASS-01 to write down.

### 3. Memory

The decision's seven, the other transforms of memory and pointers, such as `gvn-hoist`, `gvn-sink`, `mldst-motion`,
`reg2mem`, `expand-memcmp`, `mergeicmps`, lowering atomics, inferring alignment and address spaces, splitting GEP
offsets, and GC statepoints, and alias analysis, MemDep and MemorySSA. A pair with memory can't count at G1 until F4
gives `IRLean.Refines` an instance for memory.

### 4. Loops

The decision's eight, the other loop transforms, from `loop-idiom` and `loop-distribute` to `loop-interchange` and
`irce`, and loop info, scalar evolution, IV users, loop access info, dependence analysis and the DDG. SEM-07 is done,
in [#62](https://github.com/phongndo/ir-lean/pull/62), so deleting a loop under `mustprogress` can be certified.

### 5. Interprocedural

The decision's passes, under their registered names `inline`, `function-attrs`, `globalopt`, `ipsccp`, `argpromotion`,
`deadargelim`, `wholeprogramdevirt` and, for ThinLTO, `function-import` and the module summaries, and the rest of
`llvm/lib/Transforms/IPO`, coroutines, ObjC ARC, HIP's standard parallelism, other module-level transforms, and the
call graph and summary analyses. A call out of a module is refused today, so this chunk needs open modules first.

### 6. Vectorization

`loop-vectorize`, which plans with VPlan, `slp-vectorizer` and `load-store-vectorizer`, with `vector-combine`, the
sandbox vectorizer, `loop-idiom-vectorize`, lowering matrix intrinsics, the two scalarizers and `inject-tli-mappings`.

### 7. Pipelines

The 20 names that build or steer pipelines rather than change IR themselves: `default`, `thinlto-pre-link`, `thinlto`,
`lto-pre-link`, `lto`, `fatlto-pre-link` and `function-simplification`, and the pass manager's own, such as
`invalidate<all>`, its proxies and its guards. Its work is composition through each of the 20 `opt` pipelines that
build at the pin.

At the pin, `default<O1>` also runs three of chunk 6's passes, `loop-vectorize`, `vector-combine` and
`inject-tli-mappings`, and six of chunk 9's, `verify`, `annotation-remarks`, `ee-instrument`, `alloc-token`,
`memprof-remove-attributes` and `transform-warning`. So `O1`'s composition needs those too, beyond chunks 1 to 5.

### 8. Codegen

673 names: the 489 in a target's directory that aren't chunk 9's, the 24 `asm-printer` passes among them, the 18
codegen implementations an option picks that belong to no target, such as `regalloc=greedy`, and 166 more that belong
to no target. Of those, 154 are `llvm/lib/CodeGen`'s, which holds the target-independent machine passes, selection and
legalization, and the IR passes `llc` runs before selection, and 4 are machine passes the new pass manager names
without a class. The other 8 are DirectX's six analyses in `llvm/lib/Analysis` and its `dxil-upgrade`, and
`static-data-profile-info`, which only codegen's static data splitting reads. By target, X86 has 49, AArch64 43,
RISC-V 36 and AMDGPU 107. Each target needs its own machine-level semantics, CG-01, before its G0.

### 9. The rest

232 names: the 129 the inventory files as printers, verifiers and debug aids, the 36 it files as instrumentation, and
67 its category heuristic files as transforms or analyses that print, count, test, crash on purpose, rename, carry only
debug information, or instrument a program with checks, probes or hooks. Each of the 67 has its reason in
`chunks.json`, under `beyond_category`, and the test refuses one without a reason.

The heuristic also files a few names as printers or instrumentation whose code changes the program:
`?DEBUG_TYPE@llvm/lib/Target/X86/X86FlagsCopyLowering.cpp`, X86's flags copy lowering, registered under a name the
inventory couldn't resolve, `amdgpu-printf-runtime-binding` and `bpf-mi-simplify-patchable`. The decision puts every
name of those two categories here, so they stay, and INV-09's ruling for each kind is where they get settled.

## How passes were assigned

The file is the record, and these are the rules it was written by, first match first:

1. A name the inventory files as a printer, verifier or debug aid, or as instrumentation, and the 67 listed in
   `beyond_category`, are chunk 9's.
2. An `asm-printer`, a name in a target's directory, an option's codegen implementation, `llvm/lib/CodeGen`'s names,
   the machine passes the new pass manager names without a class, and what only codegen or one target uses, DirectX's
   analyses, `dxil-upgrade` and `static-data-profile-info`, are chunk 8's.
3. `llvm/lib/Transforms/IPO`, `Coroutines`, `ObjCARC` and `HipStdPar` are chunk 5's, and `llvm/lib/Transforms/Vectorize`
   is chunk 6's.
4. The rest go where the decision names them, and otherwise by what their proofs need: memory or pointers, chunk 3; a
   loop or scalar evolution, chunk 4; a module or the call graph, chunk 5; vectors, chunk 6; building or steering a
   pipeline, chunk 7; otherwise chunk 2. Analyses go with the passes whose proofs need them sound first.

A rule is a way to write the file, not a test. Moving a pass is a change to the file, with its reason in the pull
request. When the pin moves ([INV-08](llvm-verification-tasks.md#inv-08-moving-the-pin)), each new name fails the test
until it's put in a chunk.

## The test

`tests/chunks_test.py`, the `chunks` test in CTest, reads `chunks.json` and INV-01's inventory, and fails if:

- a pass is in no chunk, in two, or twice in one, or a chunk names a pass the inventory doesn't have;
- the chunks aren't the nine above, in order, with these names;
- a pass the decision names is in another chunk;
- a name the inventory files as a printer, verifier, debug aid or instrumentation is outside chunk 9, or chunk 9 holds
  another without a reason;
- an `asm-printer` or an option's codegen implementation is outside chunk 8;
- the [table of counts](#the-chunks) here differs from the files.

Cases built to break each rule show it refuses them. It needs only the standard library and `tests/llvm_scope.py`, and
takes well under a second.
