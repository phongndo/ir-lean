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
right answer. Those are separate theorems, and code marked `mustprogress` needs the first of them: see
[Known gaps](#known-gaps-in-the-model).

**A promise is part of what's checked.** When the optimizer's attributes say something about a function, the
model checks it on each access, or stops, or the emitter refuses it. So a theorem saying `= Outcome.ok` also
says the function kept those promises on that run. The exceptions are `mustprogress` and `willreturn`, in the
gaps below.

**Refinement is not safety.** "`tgt` refines `src`" says `tgt` only does what `src` allowed. If `src`
hits undefined behavior on an input, any `tgt` refines it on that input, so a refinement certificate
alone shows nothing about whether either program is safe.

## Trust boundaries

| Layer | Status today | What could go wrong | What checks it | How to shrink it |
| --- | --- | --- | --- | --- |
| Front end (clang, later `rustc`) | Outside every theorem | Source meaning isn't what the IR says | Nothing, and we claim nothing | Stays outside |
| LLVM optimizer | Not trusted for what it did, since the proof covers its output, or for promises it left behind, which the model checks or the emitter refuses. Trusted for `mustprogress` and `willreturn` | One of those being false | Tests of each promise, native code, and a one-off mutation run | An independent check of the promise rules, as Alive2 is for GEPs |
| LLVM's IR parser | Trusted | Reads IR differently from the tool that wrote it, or upgrades older IR | Native-code comparison | Pin versions, and record them |
| Emitter, about 2,100 lines of C++ | Trusted, unverified | Prints Lean that means something else | Differential tests, `tests/emitter.sh`, 13 C-level mutations, and one-off mutation of the GEP and promise rules | Full semantic and emitter mutation, then a check inside Lean ([in design](design.md#ir-and-lean-both-ways)) |
| `IRLean`, about 1,650 lines | Trusted, incomplete | Doesn't match LLVM | Constant folder, Alive2 for integer operations and GEPs, native code | [Phase 0](roadmap.md#phase-0-semantic-fidelity-and-trust-infrastructure) |
| Lean kernel | Trusted | A kernel bug | Lean's own process | Nothing planned |
| `bv_decide` | Trusted | Proofs using it also trust Lean's compiled code through the axiom it adds for each call | `tests/proofs.sh`, which allows only these and the standard three, recomputes each, and counts them per proof | Nothing planned |
| Spec and theorem statement | Read by a person | The theorem proves the wrong thing | Review, and known test vectors | Publish statements separately from proofs |
| Backend, linker, loader, hardware | Outside every theorem | Everything below IR | Native-code comparison, as evidence | Not planned. A research question for after [Phase 5](roadmap.md#phase-5-public-api-adoption-and-publication) |

## Known gaps in the model

Each has a direction. Having **less UB than LLVM** is the dangerous one for safety: a proof can succeed
in the model on a run LLVM calls undefined.

| Gap | Direction | What happens next |
| --- | --- | --- |
| A `mustprogress` or `willreturn` function, or an `llvm.loop.mustprogress` loop, that spins is `none` in the model, where LLVM calls it undefined. `tests/emitter.sh` pins this with a proof | Less UB. A theorem saying `= Outcome.ok` isn't affected, since it rules out spinning. One that allows `none` is | [Phase 1](roadmap.md#phase-1-zlib-inflate-memory-safety) proves termination. It blocks [Phase 4](roadmap.md#phase-4-certified-translation-validation-and-superoptimization), and there's no exact answer yet |
| `tbaa`, `tbaa.struct`, `alias.scope`, `noalias` metadata, `llvm.access.group` and `llvm.experimental.noalias.scope.decl` are refused. LangRef makes accesses that alias undefined if their `tbaa` tags say they don't, which would take a tag on every byte to check, and the Alive2 files checked don't mention it. Proofs compile with `-fno-strict-aliasing`, so it isn't in the IR | Refused, so sound. But a proof isn't about a default `-O2` build | Model it, which is what covering default builds needs |
| `noalias` on an argument, `dereferenceable_or_null`, two `initializes` arguments on one function, and promises at a call site, apart from `dereferenceable` and what's known of the C library, are refused | Refused, so sound. Expected to block most Rust | Model them when [Phase 3](roadmap.md#phase-3-c-and-rust-demonstrations) needs them |
| Linkage other than `external`, `internal` and `private` is refused, apart from `linkonce_odr` and `weak_odr` definitions. Those translate as this translation's copy, and calls to them are refused, directly, through a pointer or an alias, or from themselves: the linker may keep another copy, which the one-definition rule doesn't make behave the same where the source is undefined | Refused, so sound. A theorem about an `_odr` function is about this copy, and assumes nothing of the one-definition rule. Callers of C++ inline functions that aren't inlined stay out | Decide for [Phase 3](roadmap.md#phase-3-c-and-rust-demonstrations) whether a caller's theorem may assume its module's copy is the one kept |
| The address in `captures`, `memory(none)` accesses, `noalias` results and `returned` stop the model, since LangRef defines them by what's observable or doesn't say what happens. See [below](#what-the-model-does-at-its-edges) | No answer. Fine for safety proofs, and a refinement can't count them as UB | Stays, unless LangRef settles them |
| `inbounds` on a freed allocation is poison, since the model has forgotten its size, where LLVM only says any access is undefined | More UB. Fine for safety proofs | Keep it, unless a proof needs the pointer afterward |
| `undef` constants are refused, and reading uninitialized memory gives poison, where LLVM gives `undef` | More UB. Fine for safety proofs, wrong for the source side of a refinement | Decide how to represent `undef` |
| `Mem.base` is unconstrained: addresses can be zero, overlap, wrap, or ignore an allocation's alignment | Theorems are stronger than needed, so proofs carry hypotheses like `hnn`, `crcAlign`, `Readable.fits` and `Tables.crcFits` | State well-formed layouts once, as lemmas |
| Provenance is an allocation and the tags of promises it came through. `inttoptr` is refused, reading a stored pointer as an integer stops, and `ptrtoint` gives an address with no notion of exposure | Conservative, and it refuses real code | Document it. Extend only when a demonstration needs it |
| Stack and `alloca` never fail, and recursion depth is unbounded | A "safe" function can still overflow a real stack | Document it as a native-level caveat |
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

For safety proofs, more UB than LLVM is conservative and less is unsound. For refinement it splits by
side: the source must have no more UB than LLVM, and the target no less. So a single conservative
semantics can't serve both, which is why [Phase 4](roadmap.md#phase-4-certified-translation-validation-and-superoptimization) depends on
separating these first.

## Gaps in how we check

- The promise rules rest on a reading of LangRef, their tests, an independent review and a one-off mutation
  run. Integer operations and GEPs have Alive2 behind them, and these don't yet.
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

## What the model does at its edges

Some things stop the model instead of choosing an answer, and the `ModelStop` type lists them: `freeze` of
poison, reading a stored pointer as an integer, calling through a pointer to something outside the module, and
calling something outside the module that promises not to return, such as an abort.
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
- **Break it on purpose:** injecting a bug into the source must make the proof fail.
- **Clean axioms:** `tests/proofs.sh` checks every declaration in a proof's module, and allows only the standard
  three and what `bv_decide` adds, which it recomputes.
- **Checked spec:** a person reads the theorem statement, and the spec passes known test vectors.
