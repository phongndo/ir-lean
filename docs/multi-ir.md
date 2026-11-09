# Multi-IR

Whether `ir-lean` should cover MLIR and GCC's GIMPLE as well as LLVM IR, and if so, how. This is a research
note and a proposal. It changes nothing `ir-lean` claims: [status](status.md) and [trust](trust.md) still say
what's true. Its prototype, in [`prototypes/multi-ir`](../prototypes/multi-ir), is outside the library, the
build and CI.

Checked on 2026-11-07 at commit `6293d34`, with clang and MLIR 23.1.3, GCC 16.2.0 and Lean 4.35.0. LLVM and MLIR
sources are cited at tag `llvmorg-23.1.3`, and GCC's documentation as served on that date. Claims marked
*inferred* are this note's reading, not a source's statement.

## Recommendation

- **Stay an LLVM IR tool.** The emitter, `Val` and its poison, `UB`, `ModelStop` and all of `Mem` stay
  LLVM-specific. None of them should be generalized now.
- **Take MLIR in as a producer of LLVM IR.** Lower to the LLVM dialect, export with
  `mlir-translate --mlir-to-llvmir`, and translate that `.ll` as today. The theorem is about the exported IR,
  just as today's are about clang's output, and no MLIR semantics is needed. **Never go the other way.** Importing
  LLVM IR into MLIR loses facts that change its meaning ([below](#mlir-loses-facts-on-the-way-in)).
- **Don't write a GIMPLE reader yet.** It would need its own semantics, a GCC plugin rebuilt for each GCC release
  with a GPL-compatible license, and answers that GCC itself hasn't documented. That's a gated spike, not a
  roadmap phase. See [the plan](#proof-of-concept-plan).
- **Reuse is specs, the shape of an outcome, and the block driver.** Specs such as `pop`, CRC and Adler-32 are
  already independent of the IR. The only kernel change a second IR would justify is making `run` and its helpers
  generic over the reasons for stopping. Make it only when a second reader exists.

## What's LLVM-specific today

| Part | What it is | Specific to LLVM? | Reusable by another IR |
| --- | --- | --- | --- |
| `src/Emitter.cpp`, about 2,100 lines | Reads an `llvm::Module`, data layout, attributes and metadata, and prints Lean. Its refusal lists are LangRef's | Entirely | No. Another IR needs its own reader |
| `Outcome`, `Stop` (`IRLean/Basic.lean`) | Returns, stops or never finishes. A stop is undefined, or the model refusing to choose | The shape isn't. The reason lists `UB` and `ModelStop` are, and they're closed types | The shape, if it takes the reasons as a parameter. The [prototype](#the-prototype) does exactly that |
| `Next`, `run`, `jump`, `ret`, monotonicity lemmas | Blocks as data, and a driver that loops over `step` | Only through `Outcome`'s fixed `Stop` | Yes, after the same change. GIMPLE's CFG fits unchanged |
| `Val w = Option (BitVec w)`, `IRLean/Int.lean` | Integers where `none` is poison, and LangRef's operations | Poison is LLVM's. MLIR's `arith` and LLVM dialect share it | MLIR, mostly. **Not GIMPLE**, which has no poison |
| `Mem`: `Ptr`, `Alloc`, `Byte` | Block, offset and byte memory | The shape is generic | Plausibly. smtgcc models GIMPLE memory the same way ([Walfridsson](https://kristerw.github.io/2023/07/17/memory-representation/)) |
| `Mem`: `Tag`, `Effects`, `Call` | `readonly`, `captures`, `memory(...)` and `initializes` checked on each access | Entirely: these are LLVM attributes | No |
| GEP offsets from the data layout | Printed by the emitter | Entirely | No |
| Specs (`pop`, `CrcSpec`, RFC 1950 and 1952) | Pure Lean | No | **Yes, today** |
| Test harnesses | Native differential, Alive2 oracles, mutation, axiom checks | The oracles are LLVM's. The patterns aren't | The patterns |

## The three IRs, side by side

| | LLVM IR | MLIR (`arith`, `cf`, `llvm`, `memref`) | GIMPLE |
| --- | --- | --- | --- |
| Integer values | Poison is a value | `arith` ops "propagate poison values", and `ub.poison` is "deferred undefined behavior" ([ArithOps](https://mlir.llvm.org/docs/Dialects/ArithOps/), [UBOps](https://mlir.llvm.org/docs/Dialects/UBOps/)) | No poison concept. Its UB isn't documented ([PR106811](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106811), still open) |
| Signed overflow | Wraps, or poison with `nsw` | Same as LLVM, with `overflow<nsw>` | Undefined at the operation for `TYPE_OVERFLOW_UNDEFINED` types: signed, without `-fwrapv` or `-ftrapv` (`gcc/tree.h`) |
| Division by zero | Immediate UB | "is undefined behavior" for `divsi`, `divui` and the rest | "erroneous or undefined behavior" ([`-fisolate-erroneous-paths-dereference`](https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html)). A division by a variable is never speculated (`tree-eh.cc`) |
| Shift by at least the width | Poison | Poison | "the result is undefined" ([`tree.def`](https://gcc.gnu.org/onlinedocs/gccint/Unary-and-Binary-Expressions.html)). A maintainer calls it unclear whether that's UB ([PR106884](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106884)) |
| Branch on an unknown value | Poison is UB | `cf.cond_br` doesn't say | Branching on an "indefinite" value is UB in smtgcc's model ([Walfridsson, 2026](https://kristerw.github.io/2026/04/10/uninitialized-memory/)) |
| Uninitialized | `undef`, which ir-lean refuses, and poison from memory | No `undef` outside `llvm.mlir.undef` | A default definition `_N(D)`, where "the compiler may assume any initial value" (`tree-ssa-ccp.cc`). *Inferred:* like `undef` |
| Pointer-sized integers | Fixed by the data layout | `index` has a "platform-specific bit width", 64 by default ([DataLayout](https://mlir.llvm.org/docs/DataLayout/)) | Fixed by the target |
| Memory | Bytes, provenance, attribute promises | `memref` is strided and indexed, and lowers to a descriptor struct | `MEM_REF` with a type for alias analysis. `-fstrict-aliasing` is on at `-O2` |
| ABI | Lowered by clang before the IR exists | Lowered by the LLVM dialect conversion | *Inferred:* at RTL expansion (`calls.cc`), so GIMPLE calls keep source types |
| Serialized form | Bitcode loads "any bitcode since version 3.0". Text has "no specific promises" ([policy](https://llvm.org/docs/DeveloperPolicy.html#ir-backwards-compatibility)) | Bytecode is stable only "assuming immutable dialects" ([format](https://mlir.llvm.org/docs/BytecodeFormat/)), and no upstream dialect promises stability | Debug dumps only. LTO bytecode doesn't work across GCC versions ([`-flto`](https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html)) |
| How a tool reads it | The LLVM C++ API, as now | `mlir-translate` or the MLIR C++ API | A GCC plugin, which must declare `plugin_is_GPL_compatible` ([Plugin API](https://gcc.gnu.org/onlinedocs/gccint/Plugin-API.html)) and is checked against one GCC build. Or the `-gimple` dump, an unstable debug format |
| Releases | Two majors a year | With LLVM | One major a year ([releases](https://gcc.gnu.org/releases.html)) |

Each row means a separate semantics. **Neither model can stand in for the other's IR,** in either direction:

- **LLVM's ops on GIMPLE give less UB than GIMPLE has.** That's the dangerous direction for safety. The
  prototype shows a hoisted signed addition that's undefined in GIMPLE and only poison in LLVM.
- **GIMPLE's ops on LLVM give more UB than LLVM has.** That's wrong for the source side of a refinement
  ([trust](trust.md#known-gaps-in-the-model) has the polarity rule).

## Experiments

### MLIR loses facts on the way in

`prototypes/multi-ir/mlir_roundtrip.sh` takes 15 C files: the 4 in `tests/real` and the 11 of zlib's core
library. It compiles each at the proofs' flags, with no value names since MLIR doesn't keep them, and translates
it twice: as is, and after `mlir-translate --import-llvm` then `--mlir-to-llvmir`. It then compares the Lean.

| Result, of 127 functions | Count |
| --- | --- |
| Translated from the original, and the Lean after the round trip is identical | 39 |
| Translated both times, but the Lean differs | 38 |
| Translated from the original, refused after the round trip | 23 |
| Refused both times: per-file compilation leaves calls to other files external | 27 |
| Files MLIR failed to import | 0 |

In the 38 that differ, every difference is a fact lost on the way in, and the Lean gained nothing. Wrapping
flags, `range`, `dereferenceable` and `inbounds` survived.

| Lost | In the original `.ll` | After | Where |
| --- | --- | --- | --- |
| `icmp samesign`: poison if the signs differ | 70 | 0 | `LLVM_ICmpOp` has no such flag, at 23.1.3 or on `main` (`mlir/include/mlir/Dialect/LLVMIR/LLVMOps.td`) |
| `captures(address)` and `captures(address_is_null)` | 49 | 0 | Only `captures(none)` is imported: "TODO: Import captures(none) as a nocapture unit attribute until the LLVM dialect switches to the captures representation" (`ModuleImport.cpp`) |
| `initializes(...)` | 4 | 0 | Not imported |
| `noundef` and `nonnull` on intrinsic arguments | 435 | 328 | Intrinsic ops such as `llvm.intr.lifetime.start` don't carry argument attributes |

The 23 refusals come from the export copying each callee's `memory(...)` onto its call sites. The emitter refuses
call-site promises, so that costs coverage but not soundness.

**What this means.** Each lost fact removes poison or UB, so the round-tripped program refines the original.
A safety or correctness theorem about it isn't one about the original. The [LLVM dialect's
documentation](https://mlir.llvm.org/docs/Dialects/LLVM/) says "any divergence is considered a bug", and the
[import docs](https://mlir.llvm.org/docs/TargetLLVMIR/) call it "an experimental flow" for "a substantially
limited subset of LLVM IR". Export has no such problem for `ir-lean`, since the exported `.ll` is the program
LLVM compiles.

### The prototype

`example.c` has two functions. `popcount` is the loop the existing proof covers. `pick(c, a, b)` returns
`c ? a + b : 0`.

- **LLVM side:** clang's real output, through the emitter.
- **GIMPLE side:** transcribed by hand from GCC 16.2's `-fdump-tree-optimized-gimple`, kept as
  `example.gimple`. `check.sh` checks that GCC still prints exactly that.
- **`MultiIR.lean`:** a GIMPLE semantics of about 50 lines, and seven theorems, all proved.

| Theorem | What it shows |
| --- | --- |
| `gimple_popcount_correct` | GCC's `popcount` returns `pop x` for every input, against the same spec as `tests/proofs/Popcount.lean`. Same proof structure, different tactic text |
| `llvm_pick` | Clang hoisted `a + b` into a `select`, and dropped `nsw` doing it, so it wraps |
| `llvm_hoisted_nsw_discards_poison` | Keeping `nsw` would also have been valid in LLVM, since `select` discards the poison |
| `gimple_hoisted_signed_adds_ub` | In GIMPLE, the same hoist with a signed addition makes `pick 0 INT_MAX 1` undefined where GCC's returns 0. So it isn't a refinement |
| `gimple_hoisted_unsigned_refines` | Hoisting by unsigned arithmetic, which is what GCC does (`rewrite_to_defined_unconditional` in `gimple-fold.cc`), is a refinement |
| `clang_does_what_gcc_does` | Wherever GCC's `pick` is defined, clang's returns the same |
| `gcc_undefined_where_clang_wraps` | The converse fails: on `1, INT_MAX, 1` GCC's is undefined and clang's returns `INT_MIN` |

The axioms are the standard three. `gimple_popcount_correct` also uses `bv_decide`'s, through `pop_step`, as
`Popcount.lean` does. Checking takes about 2 seconds, under 1 GB.

Three things turned up along the way:

- **GCC kept `pick`'s branch at `-O2`.** It if-converts scalar code later, in RTL.
- **GCC's `popcount` exits with `x_4(D)` where clang has 0,** on the edge where `x_4` is 0. The two are equal
  there, but the IR is different, so a proof script can't be shared verbatim between them.
- **The hoisting rewrite didn't show up.** Trying it with a vectorizable loop at `-O3` on this Mac produced
  nothing, so that claim rests on GCC's source and maintainers
  ([PR106811](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106811)), not on a run.

## Refinement obligations

Each relation needs [trust](trust.md)'s polarity: a source model with no more UB than its IR, and a target
model with no less.

| Relation | What it is | Obligation if a claim crosses it |
| --- | --- | --- |
| MLIR lowered and exported to LLVM IR | A lowering | None for a theorem about the `.ll`. A claim about the MLIR program needs a model of each dialect used, and a per-run `Refines` certificate as in [Phase 4](roadmap.md#phase-4-certified-translation-validation-and-superoptimization). Not proposed |
| LLVM IR imported into MLIR and back | Should be the identity | Not met at 23.1.3. Don't use it |
| GCC's GIMPLE and clang's LLVM IR for the same C | Siblings: neither lowers to the other | None between them. Either both meet one spec, or one refines the other wherever it's defined, as `clang_does_what_gcc_does` does |
| GIMPLE before and after a GCC pass | A lowering | smtgcc's job, not this project's |

There's one open semantic question for any MLIR model. `arith` doesn't say what a poison divisor does: its
default says poison, and its lowering to LLVM says UB. A model would have to choose UB for the lowering to be a
refinement. That choice is *inferred*, and no source settles it.

## Versions

- **One version per IR, recorded.** Every theorem is about one producer at one version. The
  [L1 manifest](design.md#targets-and-machine-independence) should record the IR and its producer as well as
  the triple and data layout.
- **MLIR's LLVM dialect lags LLVM.** At 23.1.3 it can't express `samesign` or most of `captures`, though clang
  23.1.3 emits both. So a producer going through MLIR can't emit them either.
- **GIMPLE has no format to pin.** A reader is pinned to one GCC release, and `check.sh`'s comparison against
  `example.gimple` is the kind of drift check it would need.

## Interoperability

- **Specs carry across unchanged.** The prototype proves GCC's `popcount` against the `pop` that
  `tests/proofs/Popcount.lean` proves clang's against, copied since that file imports generated code. A spec
  library, as [Phase 2](roadmap.md#phase-2-reusable-contracts-and-frame-reasoning) plans, would let both import one.
- **Theorem statements differ by IR.** Clang's is `popcount (some x) = Outcome.ok (some (pop x))`, and GCC's has
  no `some`, since there's no poison. A per-IR wrapper that states "implements this spec" can come later, once
  there are two of them.
- **Proof scripts don't carry across.** Block names, PHI edges and simp sets differ. What carries is the proof's
  structure, and the spec's lemmas.
- **Cross-compiler theorems are possible,** but only "wherever one is defined, the other agrees". They say
  nothing about the C.

## Testing

| What | LLVM IR, today | MLIR through export | GIMPLE, if a reader is built |
| --- | --- | --- | --- |
| Operation semantics | `tests/opcheck.py` against Alive2 and LLVM's folder | Nothing new: it's LLVM IR | GCC's folder, and [smtgcc](https://github.com/kristerw/smtgcc) as an independent model |
| Whole functions | `tests/differential.py`, `tests/zlib.sh` against native code | The same, on exported code | The zlib harness against GCC's native code, and against clang's model on the same 117 results |
| The reader | `tests/emitter.sh`, mutation | `mlir_roundtrip.sh` as a fidelity check, if import is ever used | Generated Lean must equal the hand transcription in `MultiIR.lean` before anything else |
| Version drift | Pinned shell | Pinned shell, with matching MLIR | A pinned dump, compared each run as `check.sh` does |

## Proof-of-concept plan

Each step is opened only by the one before it. Each has a way to stop.

| | Step | Success | Stop if |
| --- | --- | --- | --- |
| **MIR-0** | This note and its prototype | Done: 7 theorems proved, with the round-trip numbers above | — |
| **MIR-1** | One MLIR program through export: an `arith` and `scf` function, lowered with upstream passes, exported, translated and proved against a spec | A theorem about the exported IR, and the emitter's refusals on MLIR's output listed | The emitter refuses most of what MLIR's lowering produces, such as descriptor structs. Then publish the list. **Depends on** accepting call-site `memory(...)` that matches the callee's, which is LLVM feature work, not multi-IR work |
| **MIR-2** | A GIMPLE reader spike: integers, PHIs, branches, returns. Either a plugin, as [gcc2cryptoline](https://github.com/fmlab-iis/gcc2cryptoline) and smtgcc are, or a parser for the `-gimple` dump | Its output for `example.c` matches `MultiIR.lean` up to names, then GCC's `adler32_z` is proved against the same RFC 1950 spec as clang's | The integer subset needs over about 1,500 lines, or smtgcc and GCC disagree on a case the proof needs |
| **MIR-3** | Generic stop reasons: `run`, `andThen`, `jump`, `ret` and the monotonicity lemmas over a reason type, with `Outcome α := Result Stop α` | Emitted LLVM Lean byte-identical, every proof unchanged, check time within noise | Any LLVM proof needs changing |
| **MIR-4** | Clang and GCC differential: both models on the zlib harness | Every disagreement explained, as a model bug, a compiler difference or UB in the source | — |

MIR-2 is where the cost is. A plugin is the robust reader, but it must be GPL-compatible. This repository is under
Apache-2.0 since 2026-11-08 ([Phase 5](roadmap.md#phase-5-public-api-adoption-and-publication)), which the FSF
[lists](https://www.gnu.org/licenses/license-list.html#apache2) as compatible with GPLv3, GCC's license, though not
with GPLv2. The GCC Runtime Library
Exception's "Eligible Compilation Process" is about tools that change what GCC compiles, and a read-only export
doesn't ([FAQ](https://www.gnu.org/licenses/gcc-exception-3.1-faq.html)). That's a reading, not legal advice. A
dump parser avoids the license question, but adds a trusted parser of a format GCC calls a debug dump.

## Tradeoffs

- **One core IR for everything** would mean one lowest-common-denominator semantics. That's exactly where
  polarity goes wrong. Per-IR semantics keep each faithful. They cost about 40 duplicated lines in the
  prototype: the driver, its step lemmas, and `ok`, `andThen`, `jump` and `ret` again.
- **MLIR through export** costs nothing, but the theorem is about lowered code. Tensors, `memref` descriptors and
  `index` widths are already decided by then. Native MLIR semantics would be a second emitter. The closest work
  is [Lean-MLIR](https://github.com/opencompl/lean-mlir), with the same `PoisonOr (BitVec w)` integers. On its
  `main`, `udiv?` in `LeanMLIR/LeanMLIR/Dialects/LLVM/Semantics.lean` says "Division by zero is undefined
  behavior", but returns poison. So sharing semantics would mean reconciling UB first, as the
  [roadmap](roadmap.md#phase-4-certified-translation-validation-and-superoptimization) already plans for Phase 4.
- **GIMPLE** adds a second compiler's view of the same C. That's useful as differential evidence and as a check
  on the specs. But it's a second semantics with no reference document, maintained against a yearly C++ API.
  [libgccjit](https://gcc.gnu.org/onlinedocs/jit/) is stable, but it only builds code. It can't read what GCC
  made of C.

## Limits

- GCC ran for `arm64-apple-darwin`, while the proofs pin `x86_64-linux-gnu`. *Inferred:* neither function's
  GIMPLE depends on the target, since `int` is 32 bits on both.
- The GIMPLE transcription is checked by no tool, only against the dump by eye. The dump itself is checked.
- The round trip covers 15 files compiled one at a time, not linked, at one LLVM version.
- No MLIR-native semantics was tried.
- smtgcc's supported GCC versions aren't stated. It appears to follow trunk.
- None of this is legal advice.

## Reproduce

Inside `nix develop`, after `lake build IRLean` and building `build/ir-lean`:

```console
nix build --no-link --print-out-paths github:NixOS/nixpkgs/1d060086d60cb76a40cf37109f979d88a5bd6396#gcc github:NixOS/nixpkgs/1d060086d60cb76a40cf37109f979d88a5bd6396#llvmPackages_latest.mlir
GCC=<gcc-wrapper-16.2.0>/bin/gcc prototypes/multi-ir/check.sh build/ir-lean
prototypes/multi-ir/mlir_roundtrip.sh build/ir-lean build/multi-ir <mlir-23.1.3>/bin tests/real/*.c
```

For zlib, extract `$ZLIB_SRC`, add `-I` for it to `PROOF_CFLAGS`, and pass its 11 core files as `tests/zlib.sh`
lists them.
