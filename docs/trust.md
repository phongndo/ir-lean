# Trust

What a theorem from `llvm-lean` means, and what it rests on. Read this before citing a result.

Facts here were checked at commit `9bf49e1` on 2026-11-05, with clang 23.1.3, Lean 4.35.0 and zlib 1.3.2,
unless they say otherwise. The probes were run at `4377c07`, and the code they exercise hasn't changed since.

## What a theorem covers

| Scope | What it would say | Today |
| --- | --- | --- |
| **Modeled IR** | The function, as this LLVM IR, behaves this way in `LLVMLean`'s semantics | **This is what's proved** |
| **LLVM IR** | The same in LLVM's real semantics | Holds if the model is faithful and the promises below hold. LLVM's semantics are prose, so this can't be a theorem |
| **Native code** | The machine code the backend produced behaves this way | Not claimed. There's no machine-code correspondence |
| **Source** | The C, C++ or Rust program behaves this way | Not claimed. It needs a proof about the front end's lowering |

A theorem about `-O2` IR and a theorem about the source differ in both directions. A front end and the
optimizer can use source-level undefined behavior to delete a check or an access before the IR exists,
so clean IR doesn't mean a clean source program. And the proof says nothing about anything that didn't
reach the IR.

**Memory-safe** means no `badAccess`, `misaligned`, `poisonPointer` or similar stop in the model, for
every input meeting the theorem's preconditions. It doesn't say the function terminates or returns the
right answer. Those are separate theorems.

**Refinement is not safety.** "`tgt` refines `src`" says `tgt` only does what `src` allowed. If `src`
hits undefined behavior on an input, any `tgt` refines it on that input, so a refinement certificate
alone shows nothing about whether either program is safe.

## Trust boundaries

| Layer | Status today | What could go wrong | What checks it | How to shrink it |
| --- | --- | --- | --- | --- |
| Front end (clang, later `rustc`) | Outside every theorem | Source meaning isn't what the IR says | Nothing, and we claim nothing | Stays outside |
| LLVM optimizer | Not trusted for what it did, since the proof covers its output. Trusted for promises it left behind | An attribute or metadata that's false | Nothing yet | [Phase 0](roadmap.md#phase-0-semantic-fidelity-and-trust-infrastructure) inventory |
| LLVM's IR parser | Trusted | Reads IR differently from the tool that wrote it, or upgrades older IR | Native-code comparison | Pin versions, and record them |
| Emitter, about 1,750 lines of C++ | Trusted, unverified | Prints Lean that means something else | Differential tests, 13 C-level mutations | Semantic and emitter mutation, then a check inside Lean ([in design](design.md#ir-and-lean-both-ways)) |
| `LLVMLean`, about 1,100 lines | Trusted, incomplete | Doesn't match LLVM | Constant folder, Alive2, native code | [Phase 0](roadmap.md#phase-0-semantic-fidelity-and-trust-infrastructure) |
| Lean kernel | Trusted | A kernel bug | Lean's own process | Nothing planned |
| `bv_decide` | Trusted | Proofs using it also trust Lean's compiled code through its native axioms | `#print axioms` | Allow-list them, and count which proofs use them |
| Spec and theorem statement | Read by a person | The theorem proves the wrong thing | Review, and known test vectors | Publish statements separately from proofs |
| Backend, linker, loader, hardware | Outside every theorem | Everything below IR | Native-code comparison, as evidence | Not planned. A research question for after [Phase 5](roadmap.md#phase-5-public-api-adoption-and-publication) |

## Known gaps in the model

Each has a direction. Having **less UB than LLVM** is the dangerous one for safety: a proof can succeed
in the model on a run LLVM calls undefined.

| Gap | Direction | What [Phase 0](roadmap.md#phase-0-semantic-fidelity-and-trust-infrastructure) does |
| --- | --- | --- |
| Multi-index `getelementptr inbounds` checks where it ends up, not each step. Going out of bounds and back goes unnoticed | Less UB | Check each step, or refuse |
| `inbounds` doesn't check that the base pointer is in bounds, which [LangRef](https://llvm.org/docs/LangRef.html) requires for non-zero indices. `Mem.gep` looks only at the result | Less UB | Check it |
| Standalone `nusw` reaches the index arithmetic but not the addition to the address: `getelementptr nusw i8, ptr %p, i64 %i` becomes plain `Mem.gep m p i` | Less UB | Model the rule, or refuse |
| `nuw` checks overflow on the allocation-relative offset, while LangRef's rule is on the address | Differs | Model the address rule, under layout assumptions |
| Attributes `noalias`, `readonly`, `writeonly`, `readnone`, `nofree`, `returned`, `captures`, `initializes` and `dereferenceable_or_null` are promises the model ignores | A proof assumes they were true | Model, refuse, or list as an explicit assumption |
| Metadata `tbaa`, `tbaa.struct`, `alias.scope`, `noalias` and `llvm.access.group` are ignored as harmless, and some can matter to the optimizer | A proof assumes they were true | The same |
| Function attributes and linkage are never read. A probe with `mustprogress`, `willreturn`, `memory(none)`, `weak` and `linkonce_odr` translated with no complaint, unlike value attributes, which are refused by default | Unknown new attributes pass silently, and an interposable callee may not be what runs | Allow-list them, refusing by default |
| `mustprogress` loops are plain non-termination in the model, where LLVM calls some of them undefined | Less UB | Decide with the above |
| `undef` constants are refused, and reading uninitialized memory gives poison, where LLVM gives `undef` | More UB. Fine for safety proofs, wrong for the source side of a refinement | Decide how to represent `undef` |
| Model stops share a type with real UB: `freezePoison`, `readUninit`, `pointerBytes`, `unknownCallee` | More UB. Fine for safety proofs, unsound if refinement treats them as UB | Separate them in the type |
| `Mem.base` is unconstrained: addresses can be zero, overlap, wrap, or ignore an allocation's alignment | Theorems are stronger than needed, so proofs carry hypotheses like `hnn` and `crcAlign` | State well-formed layouts once, as lemmas |
| Provenance is block plus offset. `inttoptr` is refused, reading a stored pointer as an integer stops, and `ptrtoint` gives an address with no notion of exposure | Conservative, and it refuses real code | Document it. Extend only when a demonstration needs it |
| Stack and `alloca` never fail, and recursion depth is unbounded | A "safe" function can still overflow a real stack | Document it as a native-level caveat |
| Floating point, atomics, volatile, exceptions, variadics, most external calls, and anything but 64-bit little-endian memory are refused | Refused, so sound | Keep refusing until a phase needs one |

For safety proofs, more UB than LLVM is conservative and less is unsound. For refinement it splits by
side: the source must have no more UB than LLVM, and the target no less. So a single conservative
semantics can't serve both, which is why [Phase 4](roadmap.md#phase-4-certified-translation-validation-and-superoptimization) depends on
separating these first.

## Gaps in how we check

- `tests/proofs.sh` fails on `sorryAx` but doesn't restrict other axioms, so a proof that added its own
  `axiom` would pass. The rule below says otherwise, so the script needs to catch up.
- `tests/opcheck.py` prints a message and passes if `alive-tv` isn't on `PATH`. Variants Alive2 can't check
  are reported, but don't fail.
- Alive2 in the flake is built on LLVM 21.1.8, while clang and the emitter are on 23.1.3. It runs with
  `--disable-undef-input`, so it doesn't exercise `undef`.
- `tests/proofs.sh` pins x86-64 Linux, but `tests/zlib.sh` compiles for the host, so on any other host the
  differential evidence isn't about the IR the proofs are about. The flake lists three systems, while CI runs
  only on x86-64 Linux.
- `llvmPackages_latest` moves with each flake update, and Lean comes through `elan` from outside Nix.
- Mutation covers the C being proved, not the semantics or the emitter.

## What the model does at its edges

Some things stop the model instead of choosing an answer: `freeze` of poison, reading a stored pointer
as an integer, and calling through a pointer to something outside the module. A proof that a function
returns normally still holds in LLVM, but a proof that one of these happens says nothing about LLVM.

Reading uninitialized memory gives poison, where LLVM gives `undef`. Poison is stricter: a result that
isn't poison in the model doesn't depend on those bytes. This caught zlib's `slide_hash` reading
entries of `prev` that were never written, which a comment in its source says is harmless.

## Rules for every proof

- **Real input:** CI regenerates the Lean from the compiler's output, so nothing can be hand-edited.
- **Break it on purpose:** injecting a bug into the source must make the proof fail.
- **Clean axioms:** `#print axioms` shows no `sorry`, only `bv_decide`'s native axioms.
- **Checked spec:** a person reads the theorem statement, and the spec passes known test vectors.
