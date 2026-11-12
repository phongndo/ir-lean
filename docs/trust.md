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

**A local rewrite certificate covers its slice.** So do [the q4_K theorems](llama.md#what-it-assumes). The q5_0
[bit-spreading proof](../tests/proofs/LlamaBitspread.lean) checks the exact pure integer helper in
[`llama_q5_bitspread.ll`](../tests/real/llama_q5_bitspread.ll). It proves that both helpers return the same
successful result for all integer inputs, including poison, and states every defined output byte for
defined inputs. Extracting that helper from a larger module and substituting its result remain trusted
steps. The certificate does not model the surrounding loads, floating-point arithmetic, whole inference,
or native lowering.

**A whole-function theorem covers its function.** Since 2026-11-10 [the cut lemma](refinement.md#the-cut-lemma) turns a
proof about a slice into a theorem that the function with the slice replaced refines the function with it, where the
model translates both. Then substituting isn't trusted: Lean checks that the function's block is the slice and then
the rest, and that the rest keeps refinement. It's used on five fixtures, two of them loops around the q5_0 slice,
one with memory, and one a function as clang compiled it, and not yet on a function of llama.cpp, so
[both rewrites](status.md#llamacpp) are still slice-proved.

Integer `bitcast` supports scalars and fixed integer vectors of equal total size, when one lane width
divides the other. It uses little-endian bit order; even pure big-endian functions are refused. Splitting
a poison lane poisons all its pieces. Joining poisons only the destination lane containing a poison
piece, so joining then splitting can spread poison. A float is its bits ([floating point](float.md)), so a `bitcast`
to or from a float of a format the model has is the same as an integer's. Pointer, scalable-vector and
nondividing-width casts remain refused. These rules are part of the trusted semantic model, tested by
the native vector comparisons, the explicit lane-order and poison cases in `tests/emitter.sh`, and
`tests/x86check.py`, against Alive2 in both directions and LLVM's constant folder, poison included.

## Trust boundaries

| Layer | Status today | What could go wrong | What checks it | How to shrink it |
| --- | --- | --- | --- | --- |
| Front end (clang, later `rustc`) | Outside every theorem | Source meaning isn't what the IR says | Nothing, and we claim nothing | Stays outside |
| LLVM optimizer | Not trusted for what it did, since the proof covers its output, or for promises it left behind, which the model checks or the emitter refuses | The model reading a promise differently from LangRef | Tests of each promise, native code, and a one-off mutation run | An independent check of the promise rules, as Alive2 is for GEPs |
| LLVM's IR parser | Trusted | Reads IR differently from the tool that wrote it, or upgrades older IR | Native-code comparison | Pin versions, and record them |
| Emitter, about 2,900 lines of C++ | Trusted, unverified | Prints Lean that means something else, or accepts what it should refuse | Differential tests, `tests/emitter.sh`, 13 C-level mutations, one-off mutation of the GEP and promise rules, and since 2026-11-09 [`tests/ir_features.py`](ir-features.md), which probes each item the pinned IR can contain and checks the emitter refuses what's classified refused, and that Lean accepts what it prints for the rest | Full semantic and emitter mutation, then a check inside Lean ([in design](design.md#ir-and-lean-both-ways)) |
| `IRLean`, about 4,100 lines | Trusted, incomplete | Doesn't match LLVM | Constant folder, Alive2 for integer operations, their vector forms and GEPs, native code, and scalable vectors against their fixed-width forms. Floating point's operations against the constant folder, the processor and Alive2, in [`tests/fpcheck.py`](../tests/fpcheck.py) | [Phase 0](roadmap.md#phase-0-semantic-fidelity-and-trust-infrastructure) |
| x86 intrinsics in `IRLean/X86.lean`, `IRLean/X86Bits.lean`, `IRLean/X86Arith.lean` and `IRLean/X86Crypto.lean`, 250 of them, [listed](x86-intrinsics.md#what-the-model-has) | Trusted, written from Intel's pseudo-code | Doesn't match the processor, or LLVM's reading of the intrinsic | `tests/x86native.py` against the processor, every one at every width and each immediate tried, saturation, wrapping and every byte of the AES S-boxes included, which needs AVX-512 VNNI, VAES, VPCLMULQDQ and GFNI. `tests/x86check.py` against Alive2 and InstCombine's folds, poison included, where they know the intrinsic, and `tests/vecopcheck.py` the same way for VPTERNLOG, PSHUFB and the shifts. Each has to refuse a wrong version of each definition. Neither Alive2 nor InstCombine computes 99 of them: VPDPBUSD, VPDPBUSDS, VPDPWSSD, VPDPWSSDS, PCLMULQDQ, the AES instructions, the masked down-converting moves, PTEST, CRC32, PHMINPOSUW and GFNI, whose values only the processor checks, on one model of processor | An independent check of those 99, and a second processor: Intel's, since z is AMD's Zen 5 |
| Lean kernel | Trusted | A kernel bug | Lean's own process | Nothing planned |
| `bv_decide` | Trusted | Proofs using it also trust Lean's compiled code through the axiom it adds for each call | [`tests/check_axioms.lean`](../tests/check_axioms.lean), which reads a proof and its imports as data, allows only these and the standard three, reruns each in a file with none of the proof's code, refuses `implemented_by` and `extern`, and counts them per proof. `leanchecker` then replays the proof through the kernel | Nothing planned |
| Python glue in `tools/` and `tests/` | Trusted for which file, theorem and finding a verdict is about. Not for whether one counts: only [`irlean.verdict`](#where-python-decides-a-verdict) grants that | Counting a crash, a limit, a failed compile or a missing file as success, as happened three times before it | [`tests/verdict_test.py`](../tests/verdict_test.py), over every combination of how the processes a verdict rests on end, and the past bugs | Keep it small, [Python](python.md) |
| Spec and theorem statement | Read by a person | The theorem proves the wrong thing | Review, and known test vectors | Publish statements separately from proofs |
| Backend, linker, loader, hardware | Outside every theorem | Everything below IR | Native-code comparison, as evidence | Not planned. A research question for after [Phase 5](roadmap.md#phase-5-public-api-adoption-and-publication) |

## Where Python decides a verdict

Lean's kernel checks proofs, but Python decides which file, which theorem and which verdict count. That went wrong
three times before 2026-11-09: a native check that crashed counted as catching a wrong rewrite, and a slice that failed to
compile counted as a refutation, both found in [#57](https://github.com/phongndo/ir-lean/pull/57), and the old scorer
counted cached results whose certificates were gone, found in [#51](https://github.com/phongndo/ir-lean/pull/51).

Since 2026-11-09 one function decides: `decide` in [`tools/irlean/verdict.py`](../tools/irlean/verdict.py). Every tool
and test that says something is proved, certified, refuted or caught asks it, and says so only if it grants it. It grants
one only on clean evidence: each process it rests on ended on its own, with the exit code that means success, and no limit
stopped it. Anything else is `unknown`, if a limit could explain it and more time or memory might decide it, or `error`.
Never success.

It's asked in two forms. A grant by name, from `GRANTS`, whose requirements are fixed there and not by its caller, as
[the verdicts design](verdicts.md) says; and the old form, one of the four claims below, whose caller picks the checks
it passes. Each tool keeps the old form until [its pull request](verdicts.md#the-migration) moves it onto its grants.
`IRLEAN_DENY_ALL=1` takes every grant away, in either form. A tool on its grants gives every status through
`status`, [the one adapter](verdicts.md#adapters), which gives a grant's word only for a granted decision of that
grant: `tools/verify.py` since stage A's third pull request.

| Claim | What it needs, besides every file it's about being there and every other check passing |
| --- | --- |
| Proved | A module that `lean` compiled, `leanchecker` replayed and the axiom audit, [`tests/check_axioms.lean`](../tests/check_axioms.lean) or the policy it applies, passed, each exiting 0. Or a record from `tools/verify.py` saying `proved`, from a process that exited 0 |
| Certified | The same, about at least one file, the evidence it's bound to. Or a verdict the same checker stored for exactly these files and tools. Or a record from `tools/binding.py` saying `bound`, or from `tools/verify.py` saying `proved`, each exiting 0 |
| Refuted | A module, as for proved, of a theorem that the claim is false. Or the kernel accepting such a theorem inside a Lean process, as [proof tests](proof-tests.md) do, or the model's compiled code finding the claim false at an input, as `tools/verify.py`'s witnesses do, each only if the process that answered then ended cleanly. Or a record saying `counterexample`, from a process that exited 2 |
| Caught | A check that has to fail on wrong code, ending on its own with the exit code that says it found something, and saying what it found, which isn't a resource limit: a Lean error of its own, a native check that exits 3, or Alive2's count of an incorrect transformation |

What counts as a limit, and so `unknown`, is what `limit_of` says: a time limit or memory cap its runner enforced, a
process killed by `SIGKILL`, which is how a cap or the OOM killer stops one, or that a shell reports as 137, `timeout`'s
124, Lean's memory exception, panic or stack guard, or a limit in the first error of a process that failed, since what
fails after a limit often fails because of it. Exit codes count only as exact integers, since in Python `False == 0`,
and a checker's record has to say the exit code its process ended with.

The caller still chooses the file, the theorem and the finding. What `decide` makes sure of is that nothing a verdict
rests on crashed, ran out of something or failed, and that nothing it needs is missing. These ask it:

| Where | Asks for |
| --- | --- |
| `tools/verify.py` | `verify.proved` and `verify.counterexample`, by name, through `status` |
| `tools/binding.py` | Certified, for a replay and for a cache hit |
| `tools/prooftest/prooftest.py` | Refuted, by the kernel or by `tools/verify.py` |
| `tools/store/store.py` | Proved, for each lemma the bar admits |
| `tools/rules/proved.py` | Proved, for each [rule](rules.md) whose theorem states its generated statement |
| `tools/rules/certify.py` | Certified, for a chain of rule applications Lean proves again |
| `tests/llvm.py` | Proved, for each target, and caught, for each injected bug |
| `tests/llama.py` | Proved, for each slice, refuted, for a wrong rewrite Lean shows differs, and caught, by a theorem stopping or the native check |
| `tests/superopt.py` | Proved, for `Rewrites.lean`, and caught, by Lean and by Alive2, for the wrong rewrite |
| `tests/passes.py` | Certified, for an instance `tools/binding.py` binds |
| `tests/verify_negative.py` | Certified, for a result the gate passes |
| `bench/instcombine/stage1.py` | Proved, for a pair `tools/verify.py` proves and the negative-verification gate passes, certified, for a bundle `tools/binding.py` binds, and refuted, for a witness `tools/verify.py` decides false |
| `tests/cpp_correspondence.py` | Proved, for the model, and caught, for each broken model |

One tool decides a verdict without asking it, on purpose: [`tools/verify_claims.py`](verify-claims.md), BIND-03's
verifier, which has to share no code with the scorer it checks. Its verdicts, `replayed` and `verified`, aren't the
scorer's words, and [`tests/verify_claims_test.py`](../tests/verify_claims_test.py) checks how it reaches each, and
that a limit is `unknown` there too. It denies by default with [a guard of its own](verify-claims.md#its-guard): only
`complete` gives `replayed`, when every check of a fixed list passed once over every module planned, and only
`verified` gives `verified`. `IRLEAN_DENY_ALL` holds there too, and the lint below allows those two functions alone.

`tools/binding.py` names `tools/irlean`'s files by hash in a bundle's toolchain, as it does itself, since they decide its
verdict too: that's `ir-lean.binding.manifest/2`. The shell tests, such as `tests/proofs.sh`, decide in shell, and
reading Alive2's own output is `tests/alive.py`'s; each has its own tests. `tests/verdict_test.py` checks `decide` over
more than 100,000 combinations of how each process ended, each file and each check, breaks each grant in every way
listed, one and two at a time, and checks each place above asks it. It also fails on any function in `tools/`, `tests/`
or `bench/` that gives a grant's word, or makes a `Decision`, outside `irlean.verdict`, and on a shell test that runs
Lean and grants itself, but those on lists that can only shrink, each with why.

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
| A global another module defines is an allocation the module doesn't create: it has an address, and `Mem.initial` leaves it out, so in a run from `initial` an access to it is `badAccess`. LLVM says it holds whatever the other module put there | More UB, from `initial` alone. Fine for safety proofs, which can say what memory holds there instead. Fine for a refinement, since 2026-11-10: a `Refines` claim is for every memory, the ones that hold the global among them | Settled for refinement: [calls](calls.md#external-globals) |
| `inbounds` on a freed allocation is poison, since the model has forgotten its size, where LLVM only says any access is undefined | More UB. Fine for safety proofs and for a refinement's target, wrong for its source | Keep it, unless a proof needs the pointer afterward. A claim about memory assumes its source doesn't do it: [refinement](refinement.md#memorys-gaps-each-with-its-side) |
| A stack object is gone once its function returns, so a load through a pointer to it is undefined. LangRef calls it dead, and a load from a dead stack object poison | More UB. Fine for safety proofs and for a refinement's target, wrong for its source | Not closed by F4's relation. A claim about memory assumes its source doesn't load through one: [refinement](refinement.md#memorys-gaps-each-with-its-side). Closing it is the rest of SEM-06 |
| `undef` constants are refused, and reading uninitialized memory gives poison, where LLVM gives `undef` | More UB. Fine for safety proofs, wrong for the source side of a refinement | Kept on purpose: on 2026-11-09 the maintainer [decided](roadmap.md#three-decisions-of-2026-11-09) `undef` stays out of the model, following LLVM's move to remove it. F4's relation, on 2026-11-10, settles the memory a run leaves: an uninitialized byte allows any byte but poison, which is right whether it's `undef` or poison. It doesn't settle a read: a source that reads one still gets poison, so a claim about memory assumes its source doesn't depend on one, or reads LLVM as its byte-type proposal has it: [refinement](refinement.md#memorys-gaps-each-with-its-side) |
| `freeze` of a vector, a pointer or a struct is refused. LangRef freezes a vector's lanes one by one, and gives a pointer with no provenance | Refused, so sound | Model them when real code needs it |
| `Mem.base` is unconstrained: addresses can be zero, overlap, wrap, or ignore an allocation's alignment | Theorems are stronger than needed, so proofs carry hypotheses like `hnn`, `crcAlign`, `Readable.fits` and `Tables.crcFits` | State well-formed layouts once, as lemmas. `Mem.Object` does this for one object ([memory](memory.md)), and a whole layout is still to do |
| Provenance is an allocation and the tags of promises it came through. `inttoptr` is refused, reading a stored pointer as an integer stops, and `ptrtoint` gives an address with no notion of exposure | Conservative, and it refuses real code | Document it. Extend only when a demonstration needs it |
| Stack and `alloca` never fail, and recursion depth is unbounded | A "safe" function can still overflow a real stack | Document it as a native-level caveat |
| An `alloca` whose size in bytes doesn't fit in 64 bits would wrap to a smaller one. A constant one is refused, and a computed one is poison, which `alloca` takes as undefined. LangRef doesn't say what such an `alloca` does | More UB, for a computed size. Fine for safety proofs | Keep it, unless a refinement needs it |
| `tail` and `musttail` calls also promise the callee doesn't touch the caller's allocas, `va_arg`s or `byval` arguments, as LangRef says, and the model doesn't check it. [IR features](ir-features.md#assumptions-it-names) lists this and the other items the emitter accepts without checking | Less UB than LLVM, in a function with memory: a callee reading the caller's stack after `tail` is undefined in LLVM and runs in the model. A function without memory has nothing to break. For a refinement it's wrong in a target, and fine in a source | Not checked yet: F4's relation doesn't. A claim about memory assumes its target makes no such call: [refinement](refinement.md#memorys-gaps-each-with-its-side) |
| Floating-point intrinsics other than `llvm.fabs`, `llvm.copysign`, `llvm.is.fpclass` and `llvm.fpto*i.sat`, atomics, volatile, exceptions, variadics, calls outside the module that touch memory the function can reach or pass a pointer, calls with effects under a promise to progress, and memory under a data layout whose pointers in address space 0 aren't 64 bits, all of them address, with null all zeros, or whose bytes aren't little-endian are refused, and so is a `bitcast` between integers or vectors in a big-endian module, even where nothing touches memory | Refused, so sound | Floating point: SEM-05's [slices](float.md#the-slices). The rest: keep refusing until a phase needs one. Calls that touch memory wait for F4: [calls](calls.md#calls-that-touch-memory) |
| Floating point outside LangRef's default environment is refused by name: `denormal_fpenv` other than `ieee`, `strictfp`, `"amdgpu-ieee"`, `!fpmath`, and the constrained intrinsics. So are `x86_fp80` and `ppc_fp128`, the fast-math flags `arcp`, `contract`, `afn` and `reassoc` wherever they mean something, and any flag on `phi`, on a call but to `llvm.fabs` and `llvm.copysign`, or on an operation that doesn't take it yet | Refused, so sound | Flags on `phi` and calls with SEM-05's intrinsics. The rest stay out, as [floating point](float.md#decisions) says why |
| LangRef lets a floating-point operation's NaN result take a payload from a target's "extra" set, which it says is empty on x86 and ARM. The model's set is empty, so floating point is refused for a target triple naming any other architecture, and for x86-32, where LangRef says LLVM may compute in `x86_fp80`. A module with no triple is taken as one of those | An assumption, for a module with no triple: one that runs on wasm or SPARC could give a NaN the model doesn't, which a target relying on it would hide | Keep it, and say it in each theorem about such a module, as [floating point](float.md#what-it-rests-on) lists |
| Floating-point arithmetic is circuits on bit vectors, symfpu's scheme, written for every format. Nothing proves them IEEE 754's arithmetic | Checked, not proved: they agree with Lean's `Float.Model` on every pair of five small formats, and with the constant folder, the processor and Alive2 where `tests/fpcheck.py` samples them, NaN results as LangRef allows them | A theorem equating them with `Float.Model` for every format |
| A call outside the module answers from the world, `IRLean.World`, which a theorem quantifies over, with the same world for source and target. One with effects goes in the run's trace, which both sides have to end with. Its callee may call back into the module, and whatever that does is part of its answer, as Alive2 assumes, so a caller's `norecurse` is refused, and so are `nosync`, `nofree` and a narrower `memory(...)` on one that makes a call with effects or that reads. A promise it breaks is undefined, `UB.outsideCall`: see [calls](calls.md#who-keeps-a-promise) | Exact where it answers: every way such a callee can behave is some world and some choice. Two calls without effects and with the same arguments may answer differently, as LangRef's `memory(none)` allows, where Alive2 gives them the same answer. A run is compared by every prefix of its trace, the source picking one run for all of them | Kept. Its arguments are compared exactly, so a target passing a value where the source passed poison doesn't refine, which LLVM allows |
| `nsz` is LangRef 23.1.3's: "the sign bit of 0.0 or -0.0 input operands can be non-deterministically flipped", a choice per operand, and on `uitofp`, `sitofp` and `select` a zero result's sign. InstSimplify reads it as reaching the result of `llvm.fabs` too: it folds `fabs nsz -0.0` to `-0.0`, which the model refutes, as Alive2 does ([floating point](float.md#fast-math-flags)) | Unsettled. Under InstSimplify's reading a target with `fabs nsz` may give `-0.0`, where the model says it can't, so a theorem about such a target holds under LangRef's text and not under that reading | Ask upstream which reading is meant |
| `llvm.x86.avx.vzeroupper` does nothing in the model. LLVM marks it as having a side effect, so its passes keep it. What it changes is the upper halves of YMM0 to YMM15, which hold no IR value across it: LLVM gives the instruction those registers as definitions, and `tests/x86native.py` checks values live across it | A rewrite that adds or drops one refines in the model. It changes no value, only what SSE code after it costs | Kept, unless it should be an effect in a run's trace, which is the maintainer's to decide |
| LangRef doesn't say what poison does to a target intrinsic. The model makes a result lane poison when a lane it's computed from is, as LLVM's constant folds of PMADDWD and PMADDUBSW do, and Alive2. For VPTERNLOG, PSHUFB, PSIGN and PBLENDVB it follows Alive2 where that's more poisonous than Intel's pseudo-code: a lane of VPTERNLOG is poison when that lane of any operand is, even one its truth table ignores, a byte of PSHUFB when the byte it picks is, even where bit 7 makes it 0, a lane of PSIGN when that lane of its first operand is, even where the second's is 0, and a byte of PBLENDVB when that byte of either operand is, even the one the mask doesn't pick. A shift by a poison count is poison in every lane. PCLMULQDQ reads one quadword of each operand in a block, and poison in the other doesn't reach the result, as InstCombine reads it. A masked move's mask is one number, and if it's poison every lane is, the ones the instruction zeroes too. For those, the AES instructions, VPDPBUSDS, VPDPWSSD, VPDPWSSDS, PTEST, CRC32, PHMINPOSUW and GFNI nothing but the model says: [x86 intrinsics](x86-intrinsics.md#what-the-model-has) has each rule. A proof that rests on that poison in a source wouldn't hold under the pseudo-code's reading | Unsettled. [The llama.cpp rewrite](llama.md) is proved equal to clang's IR under this choice. If poison spread to the whole result instead, [an argument, not checked](llama.md#what-it-assumes) says it would still refine it | Ask upstream, or prove refinement under both |

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
| A false [rule](rules.md), proved from `False` that a module outside the rules' library added with `debug.skipKernelTC`, was proved, and an application of it certified, on the standard axioms: `leanchecker` replayed only the rules' modules, and the certificate's | Both gates replay every module the proof imports that declares something and isn't Lean's own, `IRLean`'s and `Peephole`'s included, one `leanchecker` process each | `Peephole.Hack` in [`tests/rules_test.py`](../tests/rules_test.py) `--tier live` |
| The same rule was proved, and its application certified, when `Peephole.Hack` was swapped for one with `False` as an axiom after the checker and the audit read it and before the replay: each process found modules by name again, in directories anything still running could change. And a certificate's code, run as Lean compiled it, could rewrite the checkers the gate then ran, and leave a process running past the compile. Found by review on 2026-11-10 | Both gates' checks read one copy of the `IRLean`, `Peephole` and `Rules` libraries, with nothing else on `LEAN_PATH`, and hold it, the toolchain and the checkers until the last check ends. Certify mode copies the libraries before the certificate compiles, compiles it in a systemd scope, and errs if anything held changed. What `lake build` ran before `rules.py check` is still trusted: [rules](rules.md#gaps) | The swap, and a certificate rewriting the checkers, in [`tests/rules_test.py`](../tests/rules_test.py) `--tier live` |
| What the rules' gates held still wasn't all they read. `rules.py check` didn't hold the checker it generated, so one written over before Lean read it, saying every rule is proved, proved a rule with no theorem. Certify mode hashed the IR only when it recorded the verdict, so IR written over after `build/ir-lean` translated it was certified and the record named that IR. And `LEAN_SYSROOT`, from the caller, made the checker and `leanchecker` look for Lean's own modules somewhere other than the toolchain the gates held. Found by review on 2026-11-10 | `check` holds the checker and its configuration by hash and `lstat` from when it writes them. Certify mode holds the IR, the generated module and the certificate by their hashes when written, records those, and errs if any differs before the verdict. Every Lean process the gates start runs from the held toolchain by its path, with `LEAN_SYSROOT` naming it. Each held directory's own `lstat` is held too. What the gates promise, and against what, is [rules](rules.md#what-the-gates-promise) | The checker written over, the IR written over and `LEAN_SYSROOT` naming an empty directory, in [`tests/rules_test.py`](../tests/rules_test.py) `--tier live` |
| `dereferenceable(n)` on a function's or a call's result was never checked | Checked where the function returns, and again where the call does | `Runs` in [`tests/emitter.sh`](../tests/emitter.sh) |
| The emitter didn't run LLVM's verifier, so `llvm.lifetime.start` on a constant global let a store to it succeed | It runs `verifyModule` after parsing, and refuses what fails | [`tests/emitter.sh`](../tests/emitter.sh) |
| `tests/llvm.py` only checked that a statement mentioned the generated module, and passed when the emitter left a function out | Each function has to be translated, and its theorem has to name it, as ir-lean generated it. A constant named like the generated module's has to come from it | [`tests/llvm.py`](../tests/llvm.py), and `must_reject` in [`tests/proofs.sh`](../tests/proofs.sh) for the zlib proofs |
| `allocsize` and `allockind` were allowed anywhere, and never checked | Refused, apart from on the C library functions `Mem` defines | [`tests/emitter.sh`](../tests/emitter.sh) |
| A call outside the module that never returns stopped the model before its arguments were checked | Its arguments are checked first, against the call's attributes and the declaration's, so a poison `noundef` argument is undefined | `Runs` in [`tests/emitter.sh`](../tests/emitter.sh) |
| A constant `alloca` size that overflowed wrapped, and so did a computed one | See [above](#known-gaps-in-the-model) | [`tests/emitter.sh`](../tests/emitter.sh) |
| A definition another module could replace at load time was accepted | Refused, through `isInterposable()` | [`tests/emitter.sh`](../tests/emitter.sh) |
| A mutant counted as breaking its proof when the proof only ran out of heartbeats, recursion depth, memory or stack. Two did: `crc32 skips a word`, whose proof also fails further on with an error of its own, and `__udivmoddi4`'s `wrong shift count`, whose proof never did | A limit says the proof might check with more, so a mutant needs an error that isn't one, and one with none fails as unknown. The `__udivmoddi4` mutant now shifts one less, which `bv_decide` refutes. Alive2 timeouts were already unknown, and are now read from its summary, since `alive-tv` exits 0 on one | `limit_is_unknown` in [`tests/proofs.sh`](../tests/proofs.sh), [`tests/llvm.py`](../tests/llvm.py) and [`tests/superopt.py`](../tests/superopt.py) |
| A `mustprogress` or `willreturn` function, or an `llvm.loop.mustprogress` loop, that never finished was `none`, where LLVM calls it undefined: less UB than LLVM, so a theorem allowing `none` had a hole there, no refinement could delete such a loop, and `tools/binding.py` refused any target with one | Undefined, as `UB.noProgress` or `UB.noReturn`, unless the run waits on a call LangRef allows never to return. See [promises to progress](#promises-to-progress) | SEM-07. [`tests/emitter.sh`](../tests/emitter.sh), [`tests/refine.sh`](../tests/refine.sh), `promise_checked` in [`tests/binding.py`](../tests/binding.py) |
| A call whose calling convention isn't the callee's ran as an ordinary call. LangRef: "The calling convention of any pair of dynamic caller/callee must match, or the behavior of the program is undefined", so the model had less UB than LLVM | Refused, directly and through a pointer that could reach a function with another convention | SEM-08. [IR features](ir-features.md#what-it-found), `calling-convention-mismatch` in [`tests/ir_features`](../tests/ir_features/probes.ll) |
| The emitter reported the vector forms of 16 integer intrinsics, `noundef` on a struct, and `llvm.memcpy` and `llvm.memset` with a length narrower than 64 bits, as translated, and printed Lean that doesn't elaborate. Lean rejected it, so nothing was proved wrong | The vector forms and struct `noundef` are modeled lane by lane, in `IRLean/Lanes.lean`, the length is zero-extended, and `tests/ir_features.py` elaborates what the emitter prints for every probe it translates | SEM-08. [IR features](ir-features.md#what-it-found), `vecopcheck` |
| The emitter crashed on a vector-typed constant expression and on a `getelementptr` over a scalable type, so a module with either got no report at all | Both are refused, and `tests/ir_features.py` fails if the emitter crashes on a probe | [IR features](ir-features.md#what-it-found) |
| `freeze` of poison stopped the model, so a source that froze poison allowed nothing, inserting a `freeze` couldn't be certified, and two functions that both stopped there were equal though LLVM tells them apart | It's a value the run chooses, through `IRLean.Choice`, and `Refines` quantifies over each side's choices. See [above](#freeze-and-what-a-run-chooses) | F3. [`tests/freeze.sh`](../tests/freeze.sh), `tests/refine.sh`, the `freeze` runs in `tests/binding.py`, and the choices in [`tests/emitter.sh`](../tests/emitter.sh) |
| A proof that failed to compile could make `tools/verify.py` answer `counterexample` for a true statement. It took any error reading like `bv_decide`'s counterexample as a witness, and a tactic block in a value ran in the process deciding witnesses, which holds the run's nonce, so it could print a false answer of its own, or hide a real one. It could never make a run say `proved`. Found by an audit on 2026-11-10 | `tools/verify.py` takes a value from such an error only if it's a literal as `bv_decide` prints one, and `tools/verify_check.lean` refuses a witness or a pinned statement with a tactic block or `by_elab`. Either alone stops the forged answer. See [what a witness may be](verify.md#what-a-witness-may-be) | `proof_failed_forged_counterexample`, `counterexample_witness_runs_no_code` and `statement_runs_tactic` in [`tests/verify.py`](../tests/verify.py) |

For safety proofs, more UB than LLVM is conservative and less is unsound. For refinement it splits by
side: the source must have no more UB than LLVM, and the target no less. So a single conservative
semantics can't serve both, which is why [Phase 4](roadmap.md#phase-4-certified-translation-validation-and-superoptimization) depends on
separating these first. Since 2026-11-10 `IRLean.Refines` has an instance for functions with memory, and
[refinement](refinement.md#memorys-gaps-each-with-its-side) says which side each of memory's gaps is wrong for and
what a claim has to assume. The relation doesn't close them: nothing yet refuses a claim whose source reads
uninitialized memory.

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
synchronization, and the only calls outside a module are the C library's, which return, ones that never return,
which stop the model, calls without effects, which aren't observable, and calls with effects, which are refused under a
promise ([calls](calls.md#what-stays-out-and-what-a-theorem-assumes)). `llvm.sideeffect`, which LangRef says optimizers "must assume" is observable, is refused, and so
is anything that calls a function using it. So under a promise, a run that never finishes breaks it, unless it's waiting on a call LangRef
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
the same table has. An audit on 2026-11-10 found one more, a failed proof forging a counterexample in
`tools/verify.py`, which could never make a run say `proved`, and it's closed in the same table.

## Gaps in how we check

- The promise rules rest on a reading of LangRef, their tests, an independent review and a one-off mutation
  run. Integer operations, GEPs, `bitcast` between vectors and most of the model's x86 intrinsics have Alive2 behind
  them, and these don't yet. Nor do 99 of the x86 intrinsics, VPDPBUSD and PCLMULQDQ among them, which only the
  processor checks, on z's Zen 5 and no other, and which can't show poison. Alive2 unrolls
  loops a fixed number of times, so it can't check what a run that never finishes means under `mustprogress` either.
- `tests/x86native.py` and `tests/real/x86.ll` skip on a processor without AVX-512 VNNI, and the first without VAES,
  VPCLMULQDQ or GFNI. If CI's runners lack one, the processor check runs on z and not in CI: nobody has looked at
  which they have.
- Alive2 runs with `--disable-undef-input`, so it doesn't exercise `undef`. It's built from a pinned commit on
  the shell's LLVM, 23.1.3, which has to move when LLVM does.
- For a literal index, `tests/gepcheck.py` gives Alive2 the same value through a variable, because Alive2
  doesn't apply LangRef's multiplication rules to a literal. That looks like an Alive2 bug, and it isn't
  reported upstream yet.
- `tests/gepcheck.py` tries specific offsets on a global, and doesn't cover all offsets. Stack and heap pointers
  rely on `ub.ll`, `gep.ll` and native code.
- `tests/fpcheck.py` tries every operand of floating point's one-operand operations at `half` on the model and the
  processor, and every edge value against every other for two operands, with random values. The other formats are
  sampled, and two operands at `half` are 2^32 pairs, too many for the model. Alive2 sees a sample, and can't check
  `arcp`, `contract` and `afn` on `fcmp`, which it approximates, or `uitofp ninf`, which crashes it at the pin. The
  processor runs `fp128` and `i128` only where the backend and the host have a library for them, which x86-64 Linux
  does, and where AArch64 doesn't, as for `uitofp i128` to `bfloat`.
- Tests with memory run on [`ExecMem`](memory.md#executable-memory), not `Mem`. Each of its operations is proved to
  agree with `Mem`'s, and so are runs of blocks that agree, but each block's agreement is argued, not proved: the
  emitter prints the same Lean with only the name changed, which `exec_memory` checks, and blocks reach memory only
  through those operations. `model_memory` runs the memory-heavy inputs on `Mem` itself.
- `tests/proofs.sh` pins x86-64 Linux, but `tests/zlib.sh` compiles for the host, so on any other host the
  differential evidence isn't about the IR the proofs are about. The flake lists three systems, while CI runs
  only on x86-64 Linux.
- `llvmPackages_latest` moves with each flake update, and Lean comes through `elan` from outside Nix.
- [The classification](ir-features.md) probes each item once, or once for each shape of an overloaded intrinsic, in
  one place. It shows the emitter refuses or translates that probe, not every way the item can appear, and 133 items
  have no probe, each listed with why, all refused but `immarg` and the `metadata` type.
- The rules' gates, `rules.py check` and certify mode, hold what they read against anything else running as the user
  changing it, another build in the checkout or an editor, and against a crash or a limit: neither then says
  `proved` or `certified` about anything but the files checked. They don't hold against code running as the same user
  that rewrites files, directories, the tools or the toolchain on purpose while they run, such as a directory above
  the copies the checks read moved aside, replaced for the replay and put back. Nothing inside the same account can,
  as such code could rewrite the gate itself. Nothing untrusted runs in them today: every rule's proof is a reviewed
  lemma `lake build` compiles, and a certificate is Lean the tools write. A proof an agent proposes has to be compiled
  in a sandbox the operating system enforces before it reaches them, which isn't built, and is a requirement before a
  proposer's proofs are accepted. [Rules](rules.md#what-the-gates-promise) has the whole of it.
- Mutation in CI covers the C being proved. Mutation of the GEP and promise rules was a one-off, with no script
  in the repo, and the rest of the semantics and the emitter haven't been mutated.
- A mutant counts when its proof stops with an error that isn't a resource limit. That shows the proof depends on the
  code. It doesn't show the mutant does something wrong: most stop because a tactic finds code of a different shape, and
  only a few because `bv_decide` refutes something. The error that stopped each is in `tests/llvm.py`'s manifest.

## What the model does at its edges

Some things stop the model instead of choosing an answer, and the `ModelStop` type lists them: reading a stored
pointer as an integer, calling through a pointer to something outside the module,
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

Until F3, on 2026-11-09, `freeze` of poison stopped the model too. Now it's a value the run chooses, below.

## `freeze`, and what a run chooses

Since F3, on 2026-11-09, `freeze` of poison is an arbitrary value of its type, the same for every use of that
`freeze`, and chosen again each time it runs, as LangRef says. A function that has a `freeze`, or calls one that
does, returns `IRLean.Outcomes α`: an outcome for each `IRLean.Choice`, which fixes every choice of the run in
advance, and gives each `freeze` that runs a place of its own. [Refinement](refinement.md#runs-that-make-choices) has
the design, and why every way each `freeze` can choose is some `Choice`.

- **A theorem for every `Choice` is about every run LLVM allows.** `∀ c, f x c = Outcome.ok y` says each way `f` can
  choose returns `y`. A theorem about one `Choice` says what one run does, not what every run does.
- **A function without `freeze` is emitted as before,** and returns `Outcome α`, so no theorem about one changed.
- **`Refines` is for every way the target chooses, some way the source does,** with the source's choices after the
  target's, as the prototype in [`undef` and `freeze`](undef-freeze.md) settled. A source undefined for some way of
  choosing allows anything there.
- **Not covered:** `undef`, which stays out, and `freeze` of anything but an integer, which is refused, both in
  [known gaps](#known-gaps-in-the-model).

## Rules for every proof

- **Real input:** CI regenerates the Lean from the compiler's output, so nothing can be hand-edited.
- **Break it on purpose:** injecting a bug into the source must make the proof fail with an error of its own. Running out
  of time, memory, stack or recursion depth doesn't count, since the proof might check with more.
- **Clean axioms:** `tests/proofs.sh` checks every declaration in a proof's modules, reading them as data, and allows
  only the standard three and what `bv_decide` adds, which it recomputes. `leanchecker` replays each proof through the
  kernel, which catches a declaration added without it.
- **About the code:** each headline theorem has to name the function ir-lean generated, from the generated module.
- **Checked spec:** a person reads the theorem statement, and the spec passes known test vectors.
