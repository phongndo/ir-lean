# LLVM semantic contracts

What LLVM's LangRef says an operation means, written down as obligations the model has to meet, and how far
`IRLean` meets them today. This is lane T1, semantic contracts, of the effort to prove LLVM's optimizations: a pass
can't be proved correct against semantics that don't match LLVM's, so every later proof rests on what this page says.

**No area here is done.** The first slice proves four contracts about integer poison and undefined behavior, for the
model's integer operations, at every width. Everything else on this page is an audit: what exists, what's refused,
what's stricter or laxer than LangRef, and what a proof would need first. For what any theorem means, read
[trust](trust.md) first.

## Pins

Facts here were checked on 2026-11-08. The LLVM revision is the inventory's lock, `llvmorg-23.1.3`: the tag peels to
`0d261d1ca552c95a8f007e061c787ac7132fbcbc`, and `llvm/docs/LangRef.md` at that commit, fetched from GitHub, has the same
sha256 as the dev shell's copy below. If the lock moves, the LangRef sections cited here have to be read again.

| What | Pin |
| --- | --- |
| Base commit | `18421bebd466ff1bacc6b61ee9372efe9f157c37`, branch `research/llvm-semantics-contracts-20261108` |
| LLVM | 23.1.3, commit `0d261d1ca552c95a8f007e061c787ac7132fbcbc`. The dev shell's `LLVM_PROJECT_SRC` is `/nix/store/kbrxzb0whhb430x13c8ni7wnnm0h42av-source` |
| LangRef | `llvm/docs/LangRef.md` at that commit, 30,337 lines, sha256 `d05da7672c07beb53a01d77361b2c1a96f4fbd46aa30893cc40542a8a7c1ab2b` |
| nixpkgs | `1d060086d60cb76a40cf37109f979d88a5bd6396`, from `flake.lock` |
| Lean | 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, from `lean-toolchain` through elan |
| Alive2 | `a68009c9e81575bdcc249d3cc534514a76112221`, from `nix/shell.nix`. Not used by this slice |
| Target | x86-64 Linux, 64-bit little-endian, address space 0, as everywhere in `IRLean` |

## What a contract is

A contract is one rule LangRef states for many operations, written once as a Lean predicate, and proved of each model
operation it covers. For a contract to count, all four of these hold:

1. **Stated once.** The predicate doesn't mention any one operation, and quotes the LangRef sentence it comes from.
2. **Proved of the model, at every width.** The theorem is about the definition emitted code calls, such as
   `IRLean.Val.sdiv`, for all `w`, not a copy of it, and rests on the standard three axioms only.
3. **Not true of everything.** A semantics LangRef rules out, written next to the test, is proved to fail it.
4. **Tied to the code.** Changing the model's own definition, the way a plausible edit would, stops the theorem with an
   error of its own, not a resource limit.

Each audit row below has one of these statuses.

| Status | Means |
| --- | --- |
| **Proved** | The model meets a contract here, at every width. That the contract is LangRef's rule is a reading of LangRef, not a theorem |
| **Tested** | Compared with LLVM's constant folder, Alive2 at small widths, or native code, but no contract |
| **Stricter** | The model has more poison or undefined behavior than LangRef. Sound for safety proofs. Wrong for the source side of a refinement |
| **Laxer** | The model has less. Wrong for safety proofs. Wrong for the target side of a refinement |
| **Model stop** | The model gives no answer, with `Stop.model`. A proof that a function returns still holds in LLVM. A proof that one of these happens says nothing |
| **Refused** | The emitter won't translate it, so no theorem is about it. Sound, and zero coverage |

For refinement, the direction decides soundness: the source must have no more undefined behavior or poison than LLVM,
and the target no less. [Trust](trust.md#known-gaps-in-the-model) has why one semantics can't serve both yet.

## The first slice: integer poison and undefined behavior

[`IRLean/Contract/Poison.lean`](../IRLean/Contract/Poison.lean), namespace `IRLean.Contract`. It imports `IRLean.Int`
only, changes no definition, and `IRLean.lean` doesn't import it, so nothing that builds today builds differently.

### The contracts

```lean
def IsUB (o : Outcome α) : Prop := ∃ r, o = Outcome.ub r

structure Strict₂ (f : Val w → Val u → Val v) : Prop where
  left : ∀ b, f none b = none
  right : ∀ a, f a none = none

def NoPoison₂ (f : Val w → Val u → Val v) : Prop := ∀ x y, ∃ r, f (some x) (some y) = some r

def OnlyPoisons₂ (f g : Val w → Val u → Val v) : Prop := ∀ a b x, f a b = some x → g a b = some x

structure OnlyPoisonsUB (f g : Val w → Val w → Outcome (Val w)) : Prop where
  ub : ∀ a b, IsUB (f a b) ↔ IsUB (g a b)
  value : ∀ a b x, f a b = Outcome.ok (some x) → g a b = Outcome.ok (some x)

structure PoisonUB (f : Val w → Val w → Outcome (Val w)) : Prop where
  left : ∀ b, IsUB (f none b) ↔ ∃ x, IsUB (f (some x) b)
  right : ∀ a, IsUB (f a none) ↔ ∃ y, IsUB (f a (some y))
  leftPoison : ∀ b, ¬ IsUB (f none b) → f none b = Outcome.ok none
  rightPoison : ∀ a, ¬ IsUB (f a none) → f a none = Outcome.ok none
```

`Strict₁`, `NoPoison₁` and `OnlyPoisons₁` are the same for one operand. `none` is poison, as everywhere in `IRLean`.

| Contract | LangRef rule | Where |
| --- | --- | --- |
| `Strict` | "Most instructions return '`poison`' when one of their arguments is '`poison`'." | Poison Values |
| `NoPoison` | Each instruction's Semantics section gives a value, and poison only through a flag, an argument such as `is_zero_poison`, or a shift amount at least the width. So without those, values give a value | Each instruction's Semantics |
| `OnlyPoisons`, `OnlyPoisonsUB` | Each poison-generating flag: "If the `nuw` keyword is present, the result value of the `add` is a poison value if unsigned overflow occurs", and the same wording for `nsw`, `exact`, `disjoint`, `samesign`, `nneg`, and the `is_int_min_poison` and `is_zero_poison` arguments | Each instruction's Semantics |
| `PoisonUB` | "immediate undefined behavior occurs if a poison value is used as an instruction operand that has any values that trigger undefined behavior", and the divisor is listed. The other direction, and the poison result, come from the first rule | Poison Values |

`PoisonUB` pins both directions: poison is undefined exactly where some value is. For `sdiv` and `srem` this means a
poison dividend divided by minus one is undefined, since the minimum is, and by anything else nonzero it's poison.
`Val.divOverflows` already did this. The theorem says the model meets `PoisonUB`. That `PoisonUB` is what LangRef
means is the reading in the table above, which a person has to check against LangRef's text: no theorem can, since
LangRef is prose.

### What's proved

102 theorems, all at every width `w`, resting on `propext`, `Classical.choice` and `Quot.sound` only.

| Theorem | Covers |
| --- | --- |
| `udiv_isUB_iff`, `urem_isUB_iff` | Undefined exactly for a zero divisor |
| `sdiv_isUB_iff`, `srem_isUB_iff` | Undefined exactly for a zero divisor, or the minimum divided by minus one. Uses Lean's `BitVec.sdivOverflow_eq` |
| `udiv_poisonUB`, `sdiv_poisonUB` (any `exact`), `urem_poisonUB`, `srem_poisonUB` | `PoisonUB` |
| `udiv_answers`, `sdiv_answers`, `urem_answers`, `srem_answers` | Division never stops the model and always finishes |
| `udiv_exact_onlyPoisons`, `sdiv_exact_onlyPoisons` | `exact` changes neither when division is undefined nor any value it gives |
| `*_strict`, 33 of them | `Strict` for `add`, `sub`, `mul`, `shl` with any `nuw`, `nsw`; `lshr`, `ashr` with any `exact`; `and`, `or` with any `disjoint`, `xor`; `icmp` with any predicate and `samesign`, which covers all ten; `umin`, `umax`, `smin`, `smax`; the four saturating operations; `ucmp`, `scmp`; `fshl`, `fshr` in each operand; `*.with.overflow`, both fields; `zext` with any `nneg`; `sext`; `trunc` with any `nuw`, `nsw`; `abs`, `ctlz`, `cttz` with either poison argument; `ctpop`, `bitreverse`, `bswap`; the `range` attribute |
| `*_noPoison`, 33 of them | `NoPoison` without flags: everything `*_strict` covers but the shifts and `range`, which LangRef lets give poison on values. Division gives a value wherever it isn't undefined |
| `*_onlyPoisons`, 13 of them | Dropping any subset of flags keeps any value: `add`, `sub`, `mul`, `shl` (`nuw`, `nsw`), `lshr`, `ashr` (`exact`), `or` (`disjoint`), `icmp` (`samesign`), `zext` (`nneg`), `trunc` (`nuw`, `nsw`), `abs`, `ctlz`, `cttz` (their poison arguments) |
| `select_poison`, `select_true`, `select_false` | LangRef's `select`: poison condition gives poison, and only the chosen arm matters |
| `freeze_some`, `freeze_none_stops`, `freeze_none_not_ub` | `freeze` of a value is that value. Of poison, the model stops, and that isn't undefined |

`OnlyPoisons` is what lets a pass drop a flag, which InstCombine does constantly, and with `Strict` it's the integer case
of the lemma a refinement proof needs to replace one operation with another inside a larger function. `NoPoison` is the
other direction: without flags, the model makes no poison of its own, which a refinement's source needs.

### Tests

[`tests/contracts.sh`](../tests/contracts.sh), in the dev shell. It runs one Lean process at a time, each capped at 2,000
MB with `lean -M` and 300 s with `timeout`, and writes only to a temporary directory: it compiles copies of the contracts
and the three model modules they import there, without Lake. It takes about 12 s.

| Check | Shows |
| --- | --- |
| `IRLean.Contract.Poison` builds | The contracts check, with warnings as errors |
| [`tests/contracts/ContractPoison.lean`](../tests/contracts/ContractPoison.lean) | 18 vectors: LangRef's own Poison Values examples, `sdiv` of `-2147483648` by `-1`, `exact` on `7 / 2`, `select` and `freeze`. And 7 semantics LangRef rules out, each proved to fail its contract: `and` with zero absorbing poison, `add` always acting as if it had `nuw`, `add nsw` saturating, `sdiv` never undefined on a poison dividend, `udiv` always undefined on one, `udiv` giving poison for a poison divisor, and `exact` trapping |
| Axioms, read as data | Both modules rest on the standard three, through the repo's [`tests/check_axioms.lean`](../tests/check_axioms.lean), unchanged. `leanchecker` replays both through the kernel |
| [`must_fail/LaxSdivProof.lean`](../tests/contracts/must_fail/LaxSdivProof.lean) | A proof that the lax `sdiv` meets `PoisonUB` fails, with an error that isn't a resource limit |
| [`must_fail/SorriedContract.lean`](../tests/contracts/must_fail/SorriedContract.lean) | A `sorry` compiles, and the axiom check refuses it |
| Five model mutants | Each edits a copy of the real `IRLean/Int.lean`, and has to stop the named theorem with an error of its own, which a resource limit in it isn't: a poison dividend never undefined stops `sdiv_poisonUB`, a poison divisor giving poison stops `udiv_poisonUB`, `add`'s flags giving 0 stops `add_onlyPoisons`, `add` ignoring whether it has `nuw` stops `add_noPoison`, and `and` with zero absorbing poison stops `and_strict` |

Run on 2026-11-08 at the base commit plus this slice: all 11 checks passed, in 12.2 s. A copy of the script naming the
wrong theorem for a mutant failed, as it should, and so did a run where the tests didn't compile, which reported each
check that depends on them instead of passing it.

## The audit

Each row is one of LangRef's rules, where the model has it, and its status. "Gap" is what a proof would need first.

### Integers, flags and poison

| Rule | Model | Status | Evidence | Gap |
| --- | --- | --- | --- | --- |
| Arithmetic, bitwise, shifts, comparisons and casts on values | `IRLean/Int.lean` | Tested | `tests/opcheck.py`: LLVM's constant folder at many widths, Alive2 at small ones | A contract for each operation's value, against a spec that isn't the code. Only poison and UB rules are proved |
| Poison propagation | Each operation | **Proved** | `*_strict` | Vectors, below |
| No poison of the model's own | Each operation | **Proved** | `*_noPoison` | Shifts: that poison comes exactly from an amount at least the width |
| Poison-generating flags | Each operation | **Proved** | `*_onlyPoisons`, `*_exact_onlyPoisons` | `nneg` on `uitofp`, flags on `getelementptr` (memory) |
| Shift by at least the width gives poison | `Val.shiftOk` | Tested | `opcheck` | A contract |
| Division by zero or poison, signed overflow | `Val.udiv` to `Val.srem` | **Proved** | `*_isUB_iff`, `*_poisonUB` | None for scalars |
| `select` | `IRLean.select` | **Proved** | `select_*` | `undef` condition, below |
| `br`, `switch`, `llvm.assume` on poison, `unreachable` | `IRLean/Basic.lean` | Matches by definition, one line each | The `undefined` test, `tests/real/ub.ll` | Stated as contracts, with `PoisonUB` for `switch` |
| `noundef` with `range`, `nonnull` or `align`: violation is undefined | Emitter applies the poison check, then `noundef` | Tested | `narrower` in `tests/emitter.sh`, `tests/real/promises.ll` | A contract about the emitter's order, which needs the emitter in Lean |
| `range` attribute, `[a, b)`, wrapping, `0, 0` empty | `Val.range` | Tested | `range_strict` only for poison | A contract that `Val.range` is LangRef's set. Vectors are refused |
| Vectors: each lane its own value | `IRLean/Vec.lean` | Tested | `vectors_pointers`, native code | Lane-wise versions of `Strict` and `OnlyPoisons`; `extractelement` and `insertelement` past the end give poison; poison mask entries |
| `*.with.overflow` | `Val.withOverflow` | Tested, poison proved | `withOverflow_strict`, `withOverflow_noPoison` | That each field is the right value. LangRef doesn't say what a poison operand gives, beyond the general rule |
| Non-byte-sized load or store, such as `i1` | Refused by `checkMemoryType` | Refused | `src/Emitter.cpp` | LangRef 23 truncates with `nuw` on load, and zero-extends on store |

### `undef` and `freeze`

| Rule | Model | Status | Gap |
| --- | --- | --- | --- |
| `undef` constants: each use may see a different value | Refused | Refused | A representation. See [dependencies](#what-refinement-depends-on) |
| `select` on an `undef` condition: each use picks either arm | `undef` never reaches it | Refused | Same |
| Uninitialized memory reads as `undef` | Reads as poison | **Stricter** | Same. Already in [trust](trust.md#known-gaps-in-the-model) |
| Shuffle of an `undef` lane is `undef` | `undef` never reaches it | Refused | Same |
| `freeze` of `undef` or poison: arbitrary, fixed, the same for every use | `ModelStop.freezePoison` | **Model stop**, proved | A nondeterministic `Outcome`. Without it, any source that freezes poison gets no refinement certificate, and passes that insert `freeze` can only be checked where the operand is never poison |
| Two `freeze`s of the same poison may differ; one `freeze` used twice may not | Both stop the model the same way | **Model stop**. Not distinguished | See the [boundary](#a-model-stop-is-not-a-result) below |
| `freeze` of a value is the value | `Val.freeze` | **Proved** | None |

### Floating point

Every floating-point type is refused, by `leanType`. There's no model, no contract and no test. Before any can exist, a
decision is needed on each of these, and none is made here:

- **IEEE 754 arithmetic.** Lean's core has no IEEE 754 binary formats. Options are a bit-level model proved against
  a reference such as Flocq, or one trusted and differentially tested.
- **NaN.** LangRef's "Behavior of Floating-Point NaN values" makes the payload of a NaN result nondeterministic, within
  rules. That needs the same nondeterministic `Outcome` as `freeze`.
- **Fast-math flags.** `nnan` and `ninf` are poison-generating, so `OnlyPoisons` fits them. `nsz`, `arcp`, `contract`,
  `afn` and `reassoc` allow a different value, not poison, so they need a semantics with sets of results.
- **Floating-point environment and denormals.** LangRef assumes the default environment outside constrained
  intrinsics, and `denormal-fp-math` changes results.
- **Targets.** `x86_fp80` and `ppc_fp128` are target formats.

Floating point is where most of the gap between "every optimization" and today's model is.

### A model stop is not a result

Replacing `%f = freeze i32 %x` used twice with two `freeze`s of `%x` is wrong in LLVM, since two `freeze`s of poison
may pick different values. In the model, both sides stop with `freezePoison` when `%x` is poison, and agree otherwise,
so a theorem that they're equal holds. The adversarial lane reports that equality certifies this rewrite. So:

- **Equality of model outcomes is not refinement.** Where either side can stop the model, `src = tgt` says only that
  they stop the same way, which says nothing about LLVM. A certificate has to treat a source stop as allowing nothing,
  as [`Refines`](refinement.md) does, or prove neither side stops.
- **The scalar contracts here don't fix this.** `freeze_none_stops` and `freeze_none_not_ub` say what the model does.
  They don't make it say anything about `freeze` that LangRef does. Coordinating which certificates may use equality is
  the binding lane's, and fixing it for real needs a nondeterministic `Outcome`, below.

### Memory, provenance and undefined behavior

[Memory](memory.md) and [trust](trust.md#known-gaps-in-the-model) have the model and its known gaps. In contract terms:

| Rule | Model | Status | Gap |
| --- | --- | --- | --- |
| Access out of bounds, freed, misaligned, through poison, null: undefined | `Mem.access` | Tested | `memory_errors`, native code. A contract per rule |
| `getelementptr` `inbounds`, `nusw`, `nuw` | `Mem.gep`, `Mem.gepSteps` | Tested | `tests/gepcheck.py` against Alive2, on specific offsets |
| Pointer provenance, derived from an allocation | `Ptr.block` and `Ptr.tags` | Tested | Provenance is the allocation, which is narrower than LangRef's. A contract for "based on" |
| `inttoptr` | Refused | Refused | A provenance model with exposure |
| `ptrtoint`, `ptrtoaddr`: the address | `Mem.toVal`, no exposure | Tested | Exposure, which `inttoptr` needs |
| Loading a pointer's bytes as an integer | `ModelStop.pointerBytes` | **Model stop** | LangRef 23's byte type and the `bitcast` rules |
| Byte type `bN` | Refused | Refused | A model of bytes with pointer and poison bits |
| Uninitialized memory | Poison | **Stricter** | `undef` |
| Dead stack object | Writes undefined, reads poison | **Stricter** | Already in trust |
| `inbounds` on a freed allocation | Poison | **Stricter** | Already in trust |
| `tbaa`, `alias.scope`, `noalias` metadata, `noalias` arguments | Refused | Refused | Type-based and scoped aliasing as undefined behavior |
| Atomics, volatile, address spaces other than 0, scalable vectors | Refused | Refused | Each is a model |
| Stack overflow, `alloca` failing | Never happens | **Laxer** | Native caveat only, since LangRef also calls insufficient stack undefined |

### Attributes

| Kind | Model | Status |
| --- | --- | --- |
| `noundef`, `range`, `nonnull`, `align`, `dereferenceable` on a function's parameters and returns | Checked | Tested. `dereferenceable` implies `noundef`, as LangRef 23 says, since an access through poison is undefined |
| `readonly`, `writeonly`, `readnone`, `nofree`, `initializes`, `captures`, `memory(...)` | Checked on each access, through tags | Tested, with one-off mutation. See trust |
| `returned`, `noalias` returns, address `captures` | Model stop | **Model stop** |
| `mustprogress`, `willreturn`, and `llvm.loop.mustprogress` | A spinning run is `none`, where LLVM is undefined | **Laxer**. A theorem of `= Outcome.ok` isn't affected |
| `nosync`, `nounwind` | Always hold: no threads, no exceptions | Holds in the model |
| Optimization hints such as `cold`, `minsize`, `noinline` | Ignored, as they mean nothing for one run | Holds |
| `sext`, `zext` on a parameter | Ignored, as they're about how a target passes it | Holds, for x86-64. Other targets need their ABI |
| Everything else, and promises at a call site apart from `dereferenceable` and the C library's | Refused | Refused |

### Metadata

`checkMetadata` in `src/Emitter.cpp` allows `llvm.loop`, `prof`, `unpredictable`, `nosanitize`, `noundef`,
`heapallocsite`, `srcloc`, `annotation` and `inline_history`, and refuses the rest. `!noundef` on a load is checked.
The rest of that list are hints with no meaning for one run, apart from `llvm.loop.mustprogress`, in the row above. So
`!range`, `!nonnull`, `!align`, `!dereferenceable`, `!invariant.load`, `!invariant.group`, `!tbaa` and the alias scopes
are all refused, which is sound, and blocks most `-O2` builds without `-fno-strict-aliasing`.

## What refinement depends on

[`Refines src tgt`](refinement.md) is defined for code without memory. It assumes the model has no more
undefined behavior than LLVM there. This slice settles part of that:

- **Settled, for scalars, given the reading of LangRef above.** Division meets `PoisonUB`, and is undefined exactly for
  the inputs `*_isUB_iff` names. The other integer operations are never undefined, since their type has no room for it. `Strict` says poison goes on, `NoPoison` that
  without flags none appears, and `OnlyPoisons` that flags only add it. So these operations have no undefined behavior
  or poison beyond LangRef's, apart from shifts and flagged operations, where whether poison comes from exactly the
  inputs LangRef names is tested by `opcheck`, not proved.
- **Not settled.** `br`, `switch`, `assume` and `noundef` match by reading, not by contract. Values match by testing,
  not by proof. Vector lanes aren't stated. Anything that can stop the model, `freeze` first, needs a certificate that
  doesn't count a stop on both sides as agreement.

These are the exact dependencies, each a decision this lane doesn't make silently:

1. **`undef`.** Needed for any refinement whose source reads uninitialized memory or has an `undef` constant, and for
   every refinement with memory. The model reads it as poison, which is stricter, so a source that LangRef defines could
   be certified against a wrong target. The options are a value with a set of possible bit patterns per use, or a
   per-bit `undef` like LangRef's examples. Both need `Outcome` to allow more than one result.
2. **Nondeterminism in `Outcome`.** `freeze`, NaN payloads and value-changing fast-math flags all need a run to have
   more than one allowed result. Today's `Outcome` is a single result, so these are model stops or refused. This is the
   largest change the model needs, and it changes the type every emitted function has.
3. **`mustprogress`.** The model is laxer here. Refinement is unaffected in the direction it needs, since a source that
   spins needs a target that spins, but a target that adds `mustprogress` can't be certified.
4. **Memory.** Every row marked Stricter in memory is wrong for a source. Refinement with memory needs those fixed
   first, or a separate source semantics.
5. **Floating point.** Nothing exists.

## What this slice trusts and doesn't claim

Trusted:

- The Lean 4.35.0 kernel and toolchain, `tests/check_axioms.lean` and `leanchecker`, as everywhere in the repo.
- That the contracts say what LangRef says. LangRef is prose. Each predicate quotes its sentence, and a person has to
  read both. The negative tests show each predicate rules something out, not that it rules out the right thing.
- Lean's `BitVec.sdivOverflow_eq`, which is a theorem in Lean's core, and so checked.

Not claimed:

- **Anything about the emitter.** The contracts are about `IRLean`'s definitions. That `sdiv exact` in the IR becomes
  `Val.sdiv a b true` is the emitter's job, which is trusted and unverified. This is a proof-to-code gap.
- **Anything about LLVM's C++.** Whether LLVM's constant folder, InstCombine or any pass follows these rules isn't
  touched. These contracts are what such a proof would be against.
- **Values.** Only where poison and undefined behavior go is proved, and for flags only that they never change a value,
  not that they make poison on exactly the inputs LangRef names. That `Val.add` adds is tested, not proved against
  an independent spec.
- **Coverage.** Proved: the poison and undefined-behavior rules of the 4 divisions, and the poison and flag rules of
  the scalar operations the 33 `*_strict`, 33 `*_noPoison` and 13 `*_onlyPoisons` theorems name. Not proved: vectors,
  memory, control flow, attributes, metadata. Unsupported: floating point, `undef`, atomics, the byte type, `inttoptr`, and every
  other target.

## Files this lane owns

| File | What |
| --- | --- |
| `docs/llvm-semantic-contracts.md` | This page |
| `IRLean/Contract/` | Contracts and their proofs. Not imported by `IRLean.lean` |
| `tests/contracts.sh`, `tests/contracts/` | Their tests, run by `ctest` as `contracts` |

It changes no existing file but `CMakeLists.txt`, which registers `tests/contracts.sh` as the `contracts` test, and
`docs/testing.md`, which lists it. Not `IRLean.lean`, `lakefile.toml`, the model, the emitter, `tests/check_axioms.lean`,
CI, `tests/lint.sh` or the scorer. `IRLean.lean` needn't import `IRLean.Contract`: the test compiles it by path.

## Next

In order, each a contract with the same four checks:

1. Lane-wise `Strict`, `NoPoison` and `OnlyPoisons` for `IRLean/Vec.lean`, with `extractelement`, `insertelement` and
   `shufflevector`'s poison rules.
2. `PoisonUB` for `br`, `switch`, `assume`, `noundef` and `Mem.access`'s pointer operand.
3. Exact poison: each flag poisons on exactly the inputs LangRef names, and each shift on exactly an amount at least the
   width. Then value contracts against a spec written from LangRef, not from the code, starting with `fshl`.
4. A proposal for nondeterministic `Outcome`, with `freeze` as its first user, which `undef`, NaN and fast-math need.
