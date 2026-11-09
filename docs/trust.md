# Trust

What a theorem from `ir-lean` means, and what it rests on. Read this before citing a result.

Facts here were checked at commit `a86cfd2` on 2026-11-06, with clang 23.1.3, Lean 4.35.0 and zlib 1.3.2,
unless they say otherwise.

## What a theorem covers

| Scope | What it would say | Today |
| --- | --- | --- |
| **Modeled IR** | The function, as this LLVM IR from `-O2 -fno-strict-aliasing`, behaves this way in `IRLean`'s semantics | **This is what's proved** |
| **LLVM IR** | The same in LLVM's real semantics | Holds if the model is faithful. LLVM's semantics are prose, so this can't be a theorem |
| **Native code** | The machine code the backend produced behaves this way | Not claimed. There's no machine-code correspondence |
| **Source** | The C, C++ or Rust program behaves this way | Not claimed. It needs a proof about the front end's lowering |

A theorem about `-O2` IR and a theorem about the source differ in both directions. A front end and the
optimizer can use source-level undefined behavior to delete a check or an access before the IR exists,
so clean IR doesn't mean a clean source program. And the proof says nothing about anything that didn't
reach the IR.

**Memory-safe** means no `badAccess`, `misaligned`, `poisonPointer` or similar stop in the model, for
every input meeting the theorem's preconditions. It doesn't say the function terminates or returns the
right answer. Those are separate theorems. Under a [promise to progress](#promises-to-progress), a run that never
finishes is itself undefined, so a theorem that rules out undefined behavior there rules it out too.
[Memory safety](memory.md) has the one proved so far, which says more: the function returns, and changes only the
bytes it names.

**A promise is part of what's checked.** When the optimizer's attributes say something about a function, the
model checks it on each access, or at the end of a run, or stops, or the emitter refuses it. So a theorem saying
`= Outcome.ok` also says the function kept those promises on that run. Since 2026-11-08 that includes
`mustprogress`, `willreturn` and `llvm.loop.mustprogress`: see [promises to progress](#promises-to-progress).

**Refinement is not safety.** "`tgt` refines `src`" says `tgt` only does what `src` allowed. If `src`
hits undefined behavior on an input, any `tgt` refines it on that input, so a refinement certificate
alone shows nothing about whether either program is safe.

## Trust boundaries

| Layer | Status today | What could go wrong | What checks it | How to shrink it |
| --- | --- | --- | --- | --- |
| Front end (clang, later `rustc`) | Outside every theorem | Source meaning isn't what the IR says | Nothing, and we claim nothing | Stays outside |
| LLVM optimizer | Not trusted for what it did, since the proof covers its output, or for promises it left behind, which the model checks or the emitter refuses | The model reading a promise differently from LangRef | Tests of each promise, native code, and a one-off mutation run | An independent check of the promise rules, as Alive2 is for GEPs |
| LLVM's IR parser | Trusted | Reads IR differently from the tool that wrote it, or upgrades older IR | Native-code comparison | Pin versions, and record them |
| Emitter, about 2,100 lines of C++ | Trusted, unverified | Prints Lean that means something else | Differential tests, `tests/emitter.sh`, 13 C-level mutations, and one-off mutation of the GEP and promise rules | Full semantic and emitter mutation, then a check inside Lean ([in design](design.md#ir-and-lean-both-ways)) |
| `IRLean`, about 1,650 lines | Trusted, incomplete | Doesn't match LLVM | Constant folder, Alive2 for integer operations and GEPs, native code | [Phase 0](roadmap.md#phase-0-semantic-fidelity-and-trust-infrastructure) |
| Lean kernel | Trusted | A kernel bug | Lean's own process | Nothing planned |
| `bv_decide` | Trusted | Proofs using it also trust Lean's compiled code through the axiom it adds for each call | [`tests/check_axioms.lean`](../tests/check_axioms.lean), which reads a proof and its imports as data, allows only these and the standard three, reruns each in a file with none of the proof's code, refuses `implemented_by` and `extern`, and counts them per proof. `leanchecker` then replays the proof through the kernel | Nothing planned |
| Spec and theorem statement | Read by a person | The theorem proves the wrong thing | Review, and known test vectors | Publish statements separately from proofs |
| Backend, linker, loader, hardware | Outside every theorem | Everything below IR | Native-code comparison, as evidence | Not planned. A research question for after [Phase 5](roadmap.md#phase-5-public-api-adoption-and-publication) |

## Known gaps in the model

Each has a direction. Having **less UB than LLVM** is the dangerous one for safety: a proof can succeed
in the model on a run LLVM calls undefined.

| Gap | Direction | What happens next |
| --- | --- | --- |
| Under a promise to progress, two runs that never finish stop the model, since LangRef doesn't settle them: one waiting on a call to a function marked `mustprogress`, and not `willreturn`, that itself waits on a call that never returns, and any run of a function in a cycle of calls where something promises to progress, unless it's marked `willreturn`. See [promises to progress](#promises-to-progress) | No answer. Fine for safety proofs, and a refinement can't count them as UB, so deleting infinite recursion can't be certified | Classify a cycle exactly, if a refinement needs it |
| `llvm.loop.mustprogress` on some of a loop's latches and not others, or anywhere off a latch in a function with irreducible control flow, and a cycle through promised loops that leaves each of them, are refused. LLVM's `Loop::getLoopID` ignores the first two | Refused, so sound. None appears in zlib | Model them if real code needs it |
| `tbaa`, `tbaa.struct`, `alias.scope`, `noalias` metadata, `llvm.access.group` and `llvm.experimental.noalias.scope.decl` are refused. LangRef makes accesses that alias undefined if their `tbaa` tags say they don't, which would take a tag on every byte to check, and the Alive2 files checked don't mention it. Proofs compile with `-fno-strict-aliasing`, so it isn't in the IR | Refused, so sound. But a proof isn't about a default `-O2` build | Model it, which is what covering default builds needs |
| `noalias` on an argument, `dereferenceable_or_null`, two `initializes` arguments on one function, and promises at a call site, apart from `dereferenceable` and what's known of the C library, are refused | Refused, so sound. Expected to block most Rust | Model them when [Phase 3](roadmap.md#phase-3-c-and-rust-demonstrations) needs them |
| Linkage other than `external`, `internal` and `private` is refused, and so is a definition another module could replace when it's loaded, such as one under the `SemanticInterposition` module flag that isn't `dso_local`. The exceptions are `linkonce_odr` and `weak_odr` definitions, which translate as this translation's copy, and calls to them are refused, directly, through a pointer or an alias, or from themselves: the linker may keep another copy, which the one-definition rule doesn't make behave the same where the source is undefined | Refused, so sound. A theorem about an `_odr` function is about this copy, and assumes nothing of the one-definition rule. Callers of C++ inline functions that aren't inlined stay out | Decide for [Phase 3](roadmap.md#phase-3-c-and-rust-demonstrations) whether a caller's theorem may assume its module's copy is the one kept |
| The address in `captures`, `memory(none)` accesses, `noalias` results and `returned` stop the model, since LangRef defines them by what's observable or doesn't say what happens. See [below](#what-the-model-does-at-its-edges) | No answer. Fine for safety proofs, and a refinement can't count them as UB | Stays, unless LangRef settles them |
| `inbounds` on a freed allocation is poison, since the model has forgotten its size, where LLVM only says any access is undefined | More UB. Fine for safety proofs | Keep it, unless a proof needs the pointer afterward |
| A stack object is gone once its function returns, so a load through a pointer to it is undefined. LangRef calls it dead, and a load from a dead stack object poison | More UB. Fine for safety proofs, wrong for the source side of a refinement | Keep it, unless a refinement needs it |
| `undef` constants are refused, and reading uninitialized memory gives poison, where LLVM gives `undef` | More UB. Fine for safety proofs, wrong for the source side of a refinement | Decide how to represent `undef` |
| `Mem.base` is unconstrained: addresses can be zero, overlap, wrap, or ignore an allocation's alignment | Theorems are stronger than needed, so proofs carry hypotheses like `hnn`, `crcAlign`, `Readable.fits` and `Tables.crcFits` | State well-formed layouts once, as lemmas. `Mem.Object` does this for one object ([memory](memory.md)), and a whole layout is still to do |
| Provenance is an allocation and the tags of promises it came through. `inttoptr` is refused, reading a stored pointer as an integer stops, and `ptrtoint` gives an address with no notion of exposure | Conservative, and it refuses real code | Document it. Extend only when a demonstration needs it |
| Stack and `alloca` never fail, and recursion depth is unbounded | A "safe" function can still overflow a real stack | Document it as a native-level caveat |
| An `alloca` whose size in bytes doesn't fit in 64 bits would wrap to a smaller one. A constant one is refused, and a computed one is poison, which `alloca` takes as undefined. LangRef doesn't say what such an `alloca` does | More UB, for a computed size. Fine for safety proofs | Keep it, unless a refinement needs it |
| Floating point, atomics, volatile, exceptions, variadics, most external calls, and anything but 64-bit little-endian memory are refused | Refused, so sound | Keep refusing until a phase needs one |

### Closed

| Gap | How | Where |
| --- | --- | --- |
| Multi-index `inbounds` only checked where it ended up | Checks each step | [#15](https://github.com/phongndo/ir-lean/pull/15) |
| `inbounds` didn't check its base, `nusw` didn't reach the address, and `nuw` checked the offset into the allocation | All three follow LangRef, on the address | [#15](https://github.com/phongndo/ir-lean/pull/15) |
| Flagged constant `getelementptr` dropped its flags | Refused unless every step plainly stays inside its global | [#15](https://github.com/phongndo/ir-lean/pull/15) |
| Function attributes and linkage were never read | Reviewed lists, refusing anything else, also for the C library's declarations | [#16](https://github.com/phongndo/ir-lean/pull/16) |
| Model stops shared a type with undefined behavior | `Stop` is `undefined` or `model` | [#14](https://github.com/phongndo/ir-lean/pull/14) |
| `readonly`, `writeonly`, `readnone`, `nofree`, `returned`, `initializes`, `memory(...)` and provenance in `captures` were ignored | Checked on each access, through tags on pointers and frames for calls | [#19](https://github.com/phongndo/ir-lean/pull/19) |
| `norecurse` and `nofree` on a function were ignored | Refused if the call graph says they could be false | [#19](https://github.com/phongndo/ir-lean/pull/19) |
| `switch` bound its selector as `sel`, which a value of that name read in a case got instead: clang's IR for `int pick(int sel, int op)` proved `pick(5, 2) = 6` | Emitted code binds only names the emitter can't produce for a value, such as `sel'` | `pick` in [`tests/emitter.sh`](../tests/emitter.sh) |
| `tests/check_axioms.lean` imported the module it checked, running its code, and reran a `bv_decide` axiom there, so `implemented_by` could make a false one pass | It reads the module and its imports as data, as `tools/verify_check.lean` does, requires a `bv_decide` axiom's formula and certificate to be built from constructors and literals, reruns it with only the toolchain's code, and refuses `implemented_by` and `extern` in every module but Lean's own | `must_reject` in [`tests/proofs.sh`](../tests/proofs.sh) |
| A declaration added with `debug.skipKernelTC` passed with no axioms | `tests/proofs.sh` and `tests/llvm.py` run `leanchecker` on each proof and support module | `must_reject` in [`tests/proofs.sh`](../tests/proofs.sh) |
| `dereferenceable(n)` on a function's or a call's result was never checked | Checked where the function returns, and again where the call does | `Runs` in [`tests/emitter.sh`](../tests/emitter.sh) |
| The emitter didn't run LLVM's verifier, so `llvm.lifetime.start` on a constant global let a store to it succeed | It runs `verifyModule` after parsing, and refuses what fails | [`tests/emitter.sh`](../tests/emitter.sh) |
| `tests/llvm.py` only checked that a statement mentioned the generated module, and passed when the emitter left a function out | Each function has to be translated, and its theorem has to name it, as ir-lean generated it. A constant named like the generated module's has to come from it | [`tests/llvm.py`](../tests/llvm.py), and `must_reject` in [`tests/proofs.sh`](../tests/proofs.sh) for the zlib proofs |
| `allocsize` and `allockind` were allowed anywhere, and never checked | Refused, apart from on the C library functions `Mem` defines | [`tests/emitter.sh`](../tests/emitter.sh) |
| A call outside the module that never returns stopped the model before its arguments were checked | Its arguments are checked first, against the call's attributes and the declaration's, so a poison `noundef` argument is undefined | `Runs` in [`tests/emitter.sh`](../tests/emitter.sh) |
| A constant `alloca` size that overflowed wrapped, and so did a computed one | See [above](#known-gaps-in-the-model) | [`tests/emitter.sh`](../tests/emitter.sh) |
| A definition another module could replace at load time was accepted | Refused, through `isInterposable()` | [`tests/emitter.sh`](../tests/emitter.sh) |
| A mutant counted as breaking its proof when the proof only ran out of heartbeats, recursion depth, memory or stack. Two did: `crc32 skips a word`, whose proof also fails further on with an error of its own, and `__udivmoddi4`'s `wrong shift count`, whose proof never did | A limit says the proof might check with more, so a mutant needs an error that isn't one, and one with none fails as unknown. The `__udivmoddi4` mutant now shifts one less, which `bv_decide` refutes. Alive2 timeouts were already unknown, and are now read from its summary, since `alive-tv` exits 0 on one | `limit_is_unknown` in [`tests/proofs.sh`](../tests/proofs.sh), [`tests/llvm.py`](../tests/llvm.py) and [`tests/superopt.py`](../tests/superopt.py) |
| A `mustprogress` or `willreturn` function, or an `llvm.loop.mustprogress` loop, that never finished was `none`, where LLVM calls it undefined: less UB than LLVM, so a theorem allowing `none` had a hole there, no refinement could delete such a loop, and `tools/binding.py` refused any target with one | Undefined, as `UB.noProgress` or `UB.noReturn`, unless the run waits on a call LangRef allows never to return. See [promises to progress](#promises-to-progress) | SEM-07. [`tests/emitter.sh`](../tests/emitter.sh), [`tests/refine.sh`](../tests/refine.sh), `promise_checked` in [`tests/binding.py`](../tests/binding.py) |

For safety proofs, more UB than LLVM is conservative and less is unsound. For refinement it splits by
side: the source must have no more UB than LLVM, and the target no less. So a single conservative
semantics can't serve both, which is why [Phase 4](roadmap.md#phase-4-certified-translation-validation-and-superoptimization) depends on
separating these first.

## Promises to progress

LangRef, at the pinned LLVM 23.1.3, says three things about runs that don't end:

- `mustprogress` on a function: it "is required to return, unwind, or interact with the environment in an observable
  way", or the behavior is undefined. But "If a `mustprogress` function calls a function not marked `mustprogress`,
  and that function never returns, the program is well-defined even if there isn't any other observable progress."
  And "`willreturn` implies `mustprogress`."
- `willreturn`: "If an invocation of an annotated function does not return control back to a point in the call stack,
  the behavior is undefined."
- `llvm.loop.mustprogress` on a loop: it "is required to terminate, unwind, or interact with the environment in an
  observable way", which "corresponds to the `mustprogress` function attribute".

Nothing in the model is observable from outside apart from a run's result: there's no I/O, `volatile`, atomics or
synchronization, and the only calls outside a module are the C library's, which return, and ones that never return,
which stop the model. So under a promise, a run that never finishes breaks it, unless it's waiting on a call LangRef
allows never to return.

`run`'s least fixed point gives `none` for a loop that spins and for a call that never returns alike, so
[`IRLean/Promise.lean`](../IRLean/Promise.lean) tells them apart with a second driver. `stay p step b` runs blocks while
the next one is one `p` holds of, and is `none` exactly when that never ends. `runPromised p step b` runs blocks a
`stay` at a time: a `stay` that never ends is `UB.noProgress`, a block that never finishes is a call that never
returned, and stays `none`, and so does a run that keeps coming back to blocks `p` doesn't hold of. The emitter gives
each function one of these:

| The function | A run that never finishes is |
| --- | --- |
| Marked `willreturn` | `UB.noReturn`, whatever the reason |
| Marked `mustprogress` | `runPromised` with `p` true of every block: `UB.noProgress`, unless it waits on a call that never returns |
| With loops marked `llvm.loop.mustprogress` | `runPromised` with `p` true of those loops' blocks, as LLVM's `LoopInfo` finds them |
| Neither | `none`, as before |

That form is `promised (run f.step b) fun _ => runPromised f.promise f.step b`. A run that finishes is `run`'s result,
so a proof that a function returns is a proof about `run`, as before, and `promised_run` proves the whole is
`runPromised f.promise f.step b`. `runPromised_of_run_none` proves a run that never finishes is `UB.noProgress` or
`none` under it, and nothing else.

Staying among the blocks of every promised loop is staying in one of them only if every cycle through those blocks
lies inside one promised loop. In reducible control flow that always holds, and the emitter refuses a function where
it doesn't. Loop metadata is read where LangRef puts it and `Loop::getLoopID` reads it, on a loop's latches.
Passes leave copies elsewhere, on a split exit edge or a rotated loop's header, as `clang -O2` does in zlib's
`fill_window`, `deflate_stored` and `inflate`, and there they describe no loop and are ignored. Where LangRef doesn't
say what the metadata means, the function is refused: on some of a loop's latches and not others, and off a latch in a
function with irreducible control flow, whose cycles aren't loops.

Two runs LangRef doesn't settle stop the model:

- **`progressUnsettled`.** Under a promise, a call to a function marked `mustprogress`, and not `willreturn`, that never
  returns. That function's own promise is kept only because something it calls never returns, which LangRef allows.
  Whether the caller's promise still holds isn't said: its exception names a callee "not marked `mustprogress`", and
  then says "the program is well-defined".
- **`recursionUnsettled`.** A function in a cycle of calls where a function, or a loop in one, promises to progress.
  Inside the cycle the members' runs are one least fixed point, so infinite recursion, a promised loop that spins and
  a call that never returns are all `none`, and judging that by a run's own result isn't monotone, so it can't go
  inside. A member marked `willreturn` is `UB.noReturn` instead, which is right whatever the reason.

`noReturnCall`, a call outside the module that never returns, stays a stop under `willreturn` too: the callee could be
`longjmp`, and LangRef doesn't say whether jumping to a caller comes back "at a point in the existing call stack".

For refinement this is exact on both sides where it gives an answer. A source that breaks a promise is undefined, so
deleting a loop under `mustprogress` refines, which `tests/binding.py` binds on a real `loop-deletion` run. A target
that adds a promise is undefined where the source spins, which a source that never finishes doesn't allow, so it
doesn't refine. `promiseAdded` and `loopDeletedWithoutPromise` in [`tests/refine`](../tests/refine/RefineCases.lean)
prove both, and `wrong_promise_added` in [`tests/verification_negative`](../tests/verification_negative/cases) fails
the proof the model allowed before.

## Open soundness issues

None known. An audit on 2026-11-07 at `6293d34` found ten, and each is [closed](#closed) with the test that pins it. None
changed a theorem proved so far. Two mutants turned out to have counted only by running a proof out of resources, which
the same table has.

## Gaps in how we check

- The promise rules rest on a reading of LangRef, their tests, an independent review and a one-off mutation
  run. Integer operations and GEPs have Alive2 behind them, and these don't yet. Alive2 unrolls loops a fixed number
  of times, so it can't check what a run that never finishes means under `mustprogress` either.
- Alive2 runs with `--disable-undef-input`, so it doesn't exercise `undef`. It's built from a pinned commit on
  the shell's LLVM, 23.1.3, which has to move when LLVM does.
- For a literal index, `tests/gepcheck.py` gives Alive2 the same value through a variable, because Alive2
  doesn't apply LangRef's multiplication rules to a literal. That looks like an Alive2 bug, and it isn't
  reported upstream yet.
- `tests/gepcheck.py` tries specific offsets on a global, and doesn't cover all offsets. Stack and heap pointers
  rely on `ub.ll`, `gep.ll` and native code.
- `tests/proofs.sh` pins x86-64 Linux, but `tests/zlib.sh` compiles for the host, so on any other host the
  differential evidence isn't about the IR the proofs are about. The flake lists three systems, while CI runs
  only on x86-64 Linux.
- `llvmPackages_latest` moves with each flake update, and Lean comes through `elan` from outside Nix.
- Mutation in CI covers the C being proved. Mutation of the GEP and promise rules was a one-off, with no script
  in the repo, and the rest of the semantics and the emitter haven't been mutated.
- A mutant counts when its proof stops with an error that isn't a resource limit. That shows the proof depends on the
  code. It doesn't show the mutant does something wrong: most stop because a tactic finds code of a different shape, and
  only a few because `bv_decide` refutes something. The error that stopped each is in `tests/llvm.py`'s manifest.

## What the model does at its edges

Some things stop the model instead of choosing an answer, and the `ModelStop` type lists them: `freeze` of
poison, reading a stored pointer as an integer, calling through a pointer to something outside the module,
calling something outside the module that promises not to return, such as an abort, and the two runs under a
promise to progress that LangRef doesn't settle, [above](#promises-to-progress).
So do promises LangRef defines by what's observable, or doesn't say what happens if broken: looking at an address
`captures` left out, an access `memory(...)` lists as `none`, a `noalias` result that isn't new, a function
returning something other than its `returned` argument, and `llvm.assume` with a `nonnull` bundle on poison. A
proof that a function returns normally still holds in LLVM, but a proof that one of these happens says nothing
about LLVM, and neither is a claim of undefined behavior.

Reading uninitialized memory gives poison, where LLVM gives `undef`. Poison is stricter: a result that
isn't poison in the model doesn't depend on those bytes. This caught zlib's `slide_hash` reading
entries of `prev` that were never written, which a comment in its source says is harmless.

## Rules for every proof

- **Real input:** CI regenerates the Lean from the compiler's output, so nothing can be hand-edited.
- **Break it on purpose:** injecting a bug into the source must make the proof fail with an error of its own. Running out
  of time, memory, stack or recursion depth doesn't count, since the proof might check with more.
- **Clean axioms:** `tests/proofs.sh` checks every declaration in a proof's modules, reading them as data, and allows
  only the standard three and what `bv_decide` adds, which it recomputes. `leanchecker` replays each proof through the
  kernel, which catches a declaration added without it.
- **About the code:** each headline theorem has to name the function ir-lean generated, from the generated module.
- **Checked spec:** a person reads the theorem statement, and the spec passes known test vectors.
