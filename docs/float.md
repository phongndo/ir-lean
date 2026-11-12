# Floating point: the design

How `ir-lean` will model LLVM's floating point, SEM-05 in the [task list](llvm-verification-tasks.md#sem-05-floating-point).
This page is the design, decided on 2026-11-09. Its first three slices, the bit-level operations, the arithmetic and
conversions, and the fast-math flags, are in the model, and [the slices](#the-slices) say what each has done and what's
still refused. [Trust](trust.md) and [status](status.md)
say what's true now. For what any theorem means, read [trust](trust.md) first.

**Why now.** Floating point is the largest gap in stage 1's coverage. Of InstCombine's 31,240 changed pairs at
`dbfd710`, the emitter refuses 18,361, and 9,035 of those for floating point first, more than the next three reasons
together ([coverage](#coverage)).

## Decisions

| Question | Decision | Why, in a line |
| --- | --- | --- |
| What a float is | Its bits: `Val w`, the type an integer of the same width has. The format is a parameter of each operation | LLVM's floats are bit patterns: two NaNs with different payloads, and `0.0` and `-0.0`, are different values. `bitcast`, `select`, `phi`, vectors, `freeze` and `Refines` then need nothing new |
| The arithmetic | Circuits on bit vectors, one per operation, for every format, rounding once to nearest, ties to even, written without `let` | At a fixed format `bv_decide` bit-blasts them, and they're definitions, so facts for every format can be proved by hand. Without `let`, because `bv_decide` mishandles it ([measured](#no-let-in-a-circuit)) |
| What proofs cost | `bv_decide` decides a rewrite with one circuit, or two adders, at every format, `double` within 14 s. Two multipliers on two free operands it decides only at `bfloat`, so laws of multiplication need lemmas | [Measured](#what-bv_decide-costs) at `half`, `bfloat`, `float` and `double` |
| The reference | Lean's own `Float.Model`, in the toolchain's `Init`. Every circuit is checked against it | It's a second, independent definition, by Lean's developers, on `Nat` and `Int` |
| Formats | `half`, `bfloat`, `float`, `double`, `fp128`. `x86_fp80` and `ppc_fp128` refused | They're IEEE binary formats, or `bfloat`, which is laid out as one. The other two aren't, and 41 pairs are refused first for them |
| NaN results | A choice, through F3's `IRLean.Choice`: either sign, and the preferred NaN, or an input NaN quieted or unchanged | LangRef's rule, word for word. The target-specific extra payloads are taken as empty, as LangRef says of x86 and ARM, and a module for another architecture is refused |
| `nnan`, `ninf` | Poison, as LangRef says | Exact |
| `nsz` | A choice: each zero operand's sign may flip, and on `uitofp` and `sitofp` a zero result's sign | LangRef 23.1.3 says exactly that: of inputs, and of the result where the input is an integer |
| `arcp`, `contract`, `afn`, `reassoc`, `fast` | Refused by name | LangRef gives them "rewrite-based semantics" over several instructions, not a meaning per instruction. Alive2 can't prove anything with them either |
| Environment | The default one only: round to nearest, no traps, subnormals kept. `denormal_fpenv` other than `ieee`, `strictfp`, constrained intrinsics, rounding-mode arguments, `"amdgpu-ieee"` and `!fpmath` refused by name | LangRef calls running outside it "typically" undefined unless those attributes say otherwise, and they each need a model of their own |
| Where it lives | `IRLean/Float.lean`, which this lane owns. Shared files get small, local edits | The rule for running three semantics lanes at once |

The rest of this page says what each rests on, what it costs, and how it's checked.

## Pins

| What | Pin |
| --- | --- |
| Base commit | `dbfd710`, `main` after #74 |
| LangRef | `llvm/docs/LangRef.md` at `llvmorg-23.1.3`, sha256 `d05da7672c07beb53a01d77361b2c1a96f4fbd46aa30893cc40542a8a7c1ab2b`, the copy [semantic contracts](llvm-semantic-contracts.md#pins) pins. Sections "Floating-Point Environment", "Behavior of Floating-Point NaN values", "Floating-Point Semantics", "Fast-Math Flags", `denormal_fpenv`, `nofpclass`, `fcmp` and `llvm.is.fpclass` |
| Lean | 4.35.0, from `lean-toolchain`, whose `Init/Data/Float/Model` is the reference |
| Alive2 | `a68009c9e81575bdcc249d3cc534514a76112221`, built on LLVM 23.1.3, from `nix/shell.nix` |
| Host for the measurements | y: an Apple silicon Mac with 16 cores and 64 GB, macOS 26.6 |

## What LangRef says

- **The environment.** "The default LLVM floating-point environment assumes that traps are disabled and status flags
  are not observable. Therefore, floating-point math operations do not have side effects and may be speculated
  freely. Results assume the round-to-nearest rounding mode, and subnormals are assumed to be preserved." Running
  elsewhere "typically leads to undefined behavior", unless `strictfp`, `denormal_fpenv` or the constrained intrinsics
  say otherwise.
- **Results.** For `half`, `float`, `double` and `fp128`, an operation's value "matches that of the corresponding
  IEEE 754 operation executed in the default LLVM floating-point environment, except that the behavior of NaN results
  is instead as specified here". So a result that isn't a NaN is bit for bit IEEE 754's.
- **NaN results.** Where IEEE 754 gives a NaN, "the result has a non-deterministic sign; the quiet bit and payload are
  non-deterministically chosen from the following set of options": the quiet bit set and an all-zero payload, the
  "preferred NaN"; the quiet bit set and the payload of "any input operand that is a NaN"; the quiet bit and payload
  of such an operand unchanged; or the quiet bit set and a payload from "a target-specific set of 'extra' possible NaN
  payloads", which "is empty on x86 and ARM". Operations "are allowed to treat all NaNs as if they were quiet NaNs".
- **What isn't math.** "`bitcast` as well as the following operations are not 'floating-point math operations':
  `fneg`, `llvm.fabs`, and `llvm.copysign`. These operations act directly on the underlying bit representation and
  never change anything except possibly for the sign bit." And "if there is no floating-point operation being
  performed, NaN signs, quiet bits, and payloads are preserved".
- **Where LLVM breaks its own rule.** x86-32 without SSE2, and on some calling conventions with it, "may convert
  floating-point values to x86_fp80 and back", and older MIPS reads the quiet bit the other way.
- **Fast-math flags.** `nnan` and `ninf`: "If an argument is a nan, or the result would be a nan, it produces a poison
  value instead", and likewise for infinities. `nsz`: "the sign bit of 0.0 or -0.0 input operands can be
  non-deterministically flipped". `arcp`, `contract`, `afn` and `reassoc` "have rewrite-based semantics. These flags
  allow expressions, potentially containing multiple non-consecutive instructions, to be rewritten into alternative
  instructions", and only when every instruction in the expression has the flag. `fast` is all of them.
- **`denormal_fpenv`.** Absent, it's `ieee|ieee`. Under `preservesign` or `positivezero`, "denormal outputs may be
  flushed to zero", and inputs treated as zero. Under `dynamic` the mode is the environment's at run time.

## Representation

A float of `w` bits is a `Val w`, `Option (BitVec w)`, as an integer of `w` bits is: `none` is poison, and a value is its
bit pattern, the sign on top, then the biased exponent, then the trailing significand. `half` and `bfloat` are both
`Val 16`, `float` `Val 32`, `double` `Val 64`, `fp128` `Val 128`. The format is an argument of each operation, its
exponent and significand widths `e` and `m`, so `fadd` on `half` is `FP.fadd 5 10`, and on `bfloat` `FP.fadd 8 7`.

What that buys:

- **Refinement is already right.** `Refine (Val w)` says a value allows only itself, bit for bit, which is LLVM's
  refinement on floats: a target may not turn one NaN into another, or `-0.0` into `0.0`, where the source didn't
  allow it. Every nondeterministic result comes from a choice the operation makes, below, not from the relation.
- **The bit-level operations are free or nearly so.** `bitcast` between `i32` and `float` is the identity, as LangRef's
  "act directly on the underlying bit representation" says. `select`, `phi`, `extractelement`, `insertelement` and
  `shufflevector` on floats, and vectors of floats as `Vec n w`, need no change. `freeze` of a float is `Val.freeze`
  of its bits: "an arbitrary, but fixed, value of type", any bit pattern, signaling NaNs included.
- **Proof automation already reads it.** Every argument is still a value or poison of a bit vector.

What it costs: a float and an integer of the same width share a type, so the format lives only in the operations the
emitter prints. That's the emitter's to get right, and the tests below check what it prints against LLVM.

### The arithmetic

Each operation is a definition on bit vectors, for every `e` and `m`. A finite operand is a significand `M`, its implicit
bit included, and the biased exponent `t` of its last place, so its value is `M × 2 ^ (t - bias - m)`. An operation
computes its result exactly, or with a sticky bit, and rounds once:

- **One rounder.** `round s S t` rounds `(-1) ^ s × S × 2 ^ (t - bias - m)` to nearest, ties to even: it finds `S`'s top
  bit with `clz`, keeps `m + 1` bits, or fewer where the result is subnormal, rounds on the next bit and the rest, and
  adds the exponent and fraction as one integer, so a carry out of the fraction raises the exponent and the largest
  finite value rounds up to infinity.
- **`fmul`** multiplies the significands exactly, in `2m + 2` bits, and rounds.
- **`fadd`** shifts the significand with the lower last place right to meet the other, keeping three more places and
  folding what's shifted out into a sticky bit, then adds or subtracts. That's symfpu's, and SoftFloat's, scheme.
- **`fdiv`** normalizes both significands, divides with `m + 3` more places, and takes the remainder as the sticky bit.
- **`llvm.fma`**, since 2026-11-12, keeps the product's significand exact, in `2m + 2` bits, places whichever of it and
  the addend has the higher last place `3m + 5` places up, and meets it with the other, exactly where that's at most
  as many places lower, and otherwise shifted right with a sticky bit. A term that far below is less than the other's
  last place, so the sum rounds at least `2m + 4` places above the sticky bit, and `round` rounds it once. `5m + 9`
  bits hold it all. **`llvm.fmuladd`** is `fma`, or `fmul` and then `fadd`, as bit 7 of the run's choice says: LangRef
  lets it be "computed with or without fusion (rounding once or twice)". Every NaN the second gives, the first can too.
- **`fcmp`** compares sign and magnitude, with zeros of either sign equal and anything with a NaN unordered.

The circuits follow symfpu's, as fp.lean's do. The prototype is [`prototypes/float/FloatSpike.lean`](../prototypes/float/FloatSpike.lean):
`fadd`, `fsub`, `fmul`, `fdiv` and `fcmp`, 230 lines, which `IRLean/Float.lean`'s arithmetic starts from. It has no
`let`, for the reason [below](#no-let-in-a-circuit).

They agree with the reference, Lean's `Float.Model`, on every pair of values of five small formats, `E2M3`, `E3M2`,
`E4M3`, `E5M2` and `E3M4`, for all four operations and all sixteen `fcmp` predicates, with the NaN choice 0, which
gives `Float.Model`'s one NaN. Every path through the circuits, subnormal results, cancellation, rounding into infinity
and out of the subnormals, shows up in formats that small, since nothing in them depends on the widths but their
sizes. They agree with the processor, through Lean's `Float` and `Float32`, on 2,000 pairs each for `float` and
`double`, a third of them edge values. [`SpikeCheck.lean`](../prototypes/float/SpikeCheck.lean) runs both in 32 s.

### What exists, and what this reuses

| Work | What it has | What `ir-lean` takes |
| --- | --- | --- |
| Lean's `Float` and `Float32` | The processor's floats, opaque to the kernel | Nothing in the model, since the kernel can't evaluate them. The tests run them, as one oracle |
| Lean's `Float.Model`, `Init/Data/Float/Model` in 4.35.0 | A logical model of floats by Lean's developers: a `Format` of any widths, `UnpackedFloat` with `add`, `sub`, `mul`, `div`, `fma`, `sqrt` and `compare` on `Nat` and `Int`, `pack` and `unpack` on `BitVec (1 + e + m)`. One NaN, positive and quiet. Its docstring asks libraries to prove their operations equal to it | The reference: every circuit is tested against it, and a theorem equating them, for every format, is the way to generic facts about IEEE arithmetic. It isn't the model, since `bv_decide` can't read `Nat` arithmetic |
| Mathlib | `Mathlib/Data/FP/Basic.lean`, "Implementation of floating-point numbers (experimental)", deprecated on 2026-10-02 with no replacement, at `32a422c83a18` | Nothing. `ir-lean` doesn't depend on Mathlib |
| [fp.lean](https://github.com/opencompl/fp.lean), opencompl, Apache-2.0, at `bf6fa4c4e981` | Circuits from symfpu for every operation, on `PackedFloat e s`, that `bv_decide` bit-blasts, tested exhaustively against FloatX and symfpu at small formats, and `FpAgainstFloatModel`, proofs that they agree with `Float.Model`. On `nightly-2026-06-30`. One canonical NaN, as SMT-LIB has | The design of the circuits, and its proofs when they're done. Not a dependency: 20 files still have `sorry`, `Fp/PackUnpackNormalize.lean` declares `private axiom Canonical_all`, which `tests/check_axioms.lean` would refuse in anything that uses it, its toolchain isn't ours, and LLVM's NaN payloads would need a layer on top anyway |
| [VeIR](https://github.com/opencompl/veir), at `cb58df7bbf1a` | Parses float types and constants, and has `Veir/Data/FP`, a floating-point library of fp.lean's lineage. Its interpreter, `Veir/Interpreter`, has no case for `fadd` | Nothing yet. A comparison once it runs floating point |
| [Flocq](https://flocq.gitlabpages.inria.fr/) | Coq's library of IEEE 754: binary formats with NaN payloads, rounding proved correct, the basis of CompCert's floats | Nothing, since it's Coq. Its lemmas are what proofs by hand about the circuits would restate |
| Alive2, `ir/instr.cpp` and `ir/type.cpp` at the pin | Z3's floating-point theory. A NaN result chooses its sign and one of the preferred NaN, each input NaN quieted or not, and one unknown "target specific preferred QNaN" (`FloatType::fromFloat`). `nsz` flips each zero input, `nnan` and `ninf` give poison for an input or the result, and `arcp`, `contract`, `reassoc` and `afn` wrap the result in an uninterpreted function and report an approximation (`fm_poison`). `denormal_fpenv` flushes a subnormal input or output by a choice (`handle_subnormal`) | Its readings of LangRef, which this design shares but for one: Alive2 adds one unknown target payload where `ir-lean` takes the set as empty and refuses other architectures. And an oracle, below |
| symfpu, and SoftFloat | Bit-vector circuits for IEEE 754, used by cvc5 and Bitwuzla, and Berkeley's software floats | The algorithms: alignment with a sticky bit, one rounding, and the exponent and fraction added as one integer |

## NaN payloads, as a choice

A floating-point math operation, anything but `fneg`, `fabs`, `copysign`, `bitcast`, `select`, `phi` and the vector
operations that move lanes, makes a choice when it runs, through F3's [`IRLean.Choice`](refinement.md#runs-that-make-choices),
the same way `freeze` does. It's a chooser in its block, and reads its number with `c'.pick k`, so a function with one
returns `Outcomes`, as one with a `freeze` does. On a vector each lane chooses on its own: lane `i` of the `k`th chooser
reads `(c'.sub k).pick i`, as a call's choices do. Where IEEE 754 gives a NaN, the number picks:

| Bits of the choice | Pick |
| --- | --- |
| 0 | The sign |
| 1 | Unchanged, or quieted |
| 2 and 3 | Which: the preferred NaN, or operand 1, 2 or 3 |
| 4 and 5 | Under `nsz`, whether operand 1 or 2, where it's a zero, has its sign flipped, [below](#fast-math-flags). On `uitofp`, `sitofp` and `select`, bit 4 flips a zero result's sign instead. Bit 6 is kept for a third operand |

An operand that isn't a NaN gives the preferred NaN. So every choice is a result LangRef allows, and every result it
allows is some choice: the preferred NaN with either sign, and each NaN operand, quieted or as it was, with either sign.
Where IEEE 754 gives anything else, the choice is ignored, and the result is the same for every choice.

**Between formats,** `fptrunc` and `fpext` carry a NaN operand's payload as LangRef says: `fptrunc` drops the payload's
low bits that don't fit, and `fpext` copies it "to the high order bits of the resulting payload, and the remaining low
order bits are zero". Where dropping bits leaves an all-zero payload, the unchanged NaN would be an infinity, so only
the quieted one is allowed, as LangRef says too. Alive2's `FloatType::fromFloat` reads it the same way.

**`Refines` needs no change.** For every way the target chooses, some way the source chooses gives a result that allows
the target's, bit for bit. So `fadd %x, -0.0` to `%x` refines: where `%x` is a NaN, the source may return it unchanged
with its own sign. `fadd %x, %nan` to the preferred NaN refines, and to any other payload doesn't. Alive2 agrees on all
three at the pin.

**What a proof needs.** The source's choice has to be named, as a function of the inputs and the target's choices.
For the rewrite above it's "operand 1, unchanged, with `%x`'s sign". That's the `∃` in `Refine (Outcomes α)`, and the
spike's `fadd_negzero` is that statement, closed by `bv_decide` once the witness is given.

**The extra payloads.** The model takes LangRef's target-specific set as empty, which it says it is on x86 and ARM.
On another architecture it isn't: on SPARC it's the all-ones payload, and on wasm it can be every payload. A model with
too few NaN results makes a target look more defined than it is, so the emitter refuses floating-point operations in a
module whose target triple names any architecture but x86-64, AArch64 and ARM, or `unknown`. x86-32 is refused too,
since LangRef says LLVM breaks its own rules there. A module with no triple is taken as one of those, which is an
assumption, and [trust](trust.md) will list it. Of the 9,222 refused pairs whose reason names floating point, 6,880
have no triple, 875 are for x86-64 and 148 for AArch64 or ARM. Of the other 1,319, 1,101 are for AMDGPU, whose target
intrinsics and attributes are refused too, 92 for x86-32 and 67 for `unknown`.

## Fast-math flags

| Flag | In the model | Alive2 |
| --- | --- | --- |
| `nnan` | Poison if an operand is a NaN, or the result would be | The same |
| `ninf` | Poison if an operand is an infinity, or the result would be | The same |
| `nsz` | A choice: each operand that's a zero may have its sign flipped, before the operation. One more bit of the choice per operand. On `uitofp` and `sitofp`, whose operand is an integer with no sign, LangRef says instead "if the input value is 0, the sign bit of the result is non-deterministic": one bit of the choice, for the result | The same, `any_fp_zero` on each input. At the pin it asserts that `uitofp` and `sitofp` have no flags at all, and stops |
| `arcp`, `contract`, `afn`, `reassoc`, and `fast` | Refused by name, on the source and target alike | An uninterpreted function and an approximation, so it never says a rewrite with one is correct |

The four refused flags give permission to rewrite an expression, LangRef says, and they hold only where every
instruction in it has the flag. That's a relation between two programs, not something one instruction does, so no
choice per instruction can say it. A source with such a flag could be translated without it, since that only takes
behaviors away from the source, but the emitter doesn't know which side it's translating, so the flags are refused on
both. Of the 9,222 refused pairs whose reason names floating point, 1,191 have one of them on either side.

`fcmp`, `select`, `phi` and calls returning floats take flags too. On `fcmp` only `nnan`, `ninf` and `reassoc` have
an effect, LangRef says. On `select`, "they are only applied to the result, not both arms", so `nnan` and `ninf` make
the result poison where the selected value is a NaN or an infinity, whatever the other arm is, and `nsz` lets a zero
result's sign flip. Alive2 reads it the same way. `phi` and calls keep their flags refused.

Which operations `nsz` changes:

- **The arithmetic, `fptrunc` and `fpext`:** each zero operand's sign, by bits 4 and 5 of the choice the operation
  already makes for a NaN.
- **`fneg` and `llvm.copysign`:** a zero operand's sign, so `fneg` of a zero, and `copysign` with a zero second
  operand, may give either zero. Each becomes a chooser, but only with `nsz`.
- **`llvm.fabs`:** nothing, since it clears the sign whatever the operand's was. It doesn't choose.
- **`uitofp`, `sitofp` and `select`:** a zero result's sign, by bit 4. Each becomes a chooser with `nsz`.

**Where LLVM reads `nsz` differently.** InstSimplify folds `fabs nsz x` to `x` where `x` is never a NaN and never below
zero (`simplifyUnaryIntrinsic`, in `InstructionSimplify.cpp` at the pin), so `fabs nsz -0.0` becomes `-0.0`. That
reads `nsz` as reaching the result's sign. LangRef 23.1.3's text lets it flip only an operand's, and `fabs` of either
zero is `0.0`, so the model refutes the fold, and Alive2 does too. It shows only where the constant folder leaves the
`fabs`, as it does for `fp128`. `tests/float` has it as a wrong rewrite, and `tests/fpcheck.py` counts the folds apart.

## The environment

The model is the default environment: round to nearest, ties to even, no traps, flags nobody reads, and subnormals kept.
Everything that leaves it is refused by name, so a refusal says why:

| What | Refused as | Pairs refused first for it at `dbfd710` |
| --- | --- | --- |
| `denormal_fpenv` other than `ieee` or `ieee\|ieee`, for any type | `function attribute denormal_fpenv(...)` | 171. Another 27 are refused for `denormal_fpenv(ieee)`, the default, which slice 1 accepts |
| `strictfp`, and `llvm.experimental.constrained.*` | `function attribute strictfp`, and the intrinsic | 37, and those under other reasons |
| `llvm.fptrunc.round` and the other intrinsics that take a rounding mode, `llvm.get.rounding`, `llvm.set.rounding` and the environment's | the intrinsic | Under intrinsics |
| `"amdgpu-ieee"` | `function attribute "amdgpu-ieee"=...` | 58 |
| `!fpmath` | `metadata !fpmath`, as today | Under metadata |

Alive2 models the flushing modes as a choice per input and output. `ir-lean` could too, with the same mechanism as
NaNs, if the 171 pairs turn out to matter.

## Formats

| Type | Exponent bits `e` | Significand bits `m` | In the model |
| --- | --- | --- | --- |
| `half` | 5 | 10 | Yes |
| `bfloat` | 8 | 7 | Yes. LangRef's "Floating-Point Semantics" names only the IEEE formats. LLVM's `APFloat` treats `bfloat` as an IEEE-style format with these widths, and the constant folder is its oracle, since few processors do `bfloat` arithmetic |
| `float` | 8 | 23 | Yes |
| `double` | 11 | 52 | Yes |
| `fp128` | 15 | 112 | Yes. Only the constant folder checks it |
| `x86_fp80` | 15 | 64, with an explicit integer bit | Refused. Its unnormals and pseudo-denormals need a model of their own |
| `ppc_fp128` | Two `double`s | | Refused. It isn't a binary format |

## What `bv_decide` costs

[`prototypes/float/spike.py`](../prototypes/float/spike.py) states nine theorems about the prototype at each format, and
proves each in a Lean process of its own, with `bv_decide`'s SAT solver given 300 s, and the process capped at 8 GB and
420 s by `tools/measure.py`, which records its wall time and the peak memory of its process, sampled every 0.25 s. The
theorems are of the shapes refinements take:

- `fadd_comm`, `fmul_comm`: two whole circuits on two free operands, and the NaN choice.
- `fadd_negzero`, `fmul_one`, `fdiv_one`: one circuit, a constant operand and a named NaN choice: `x + -0.0`, `x × 1.0`
  and `x / 1.0` are `x`, bit for bit, NaNs included.
- `fdiv_two`: two different circuits on one free operand: `x / 2.0` is `x × 0.5`.
- `fcmp_swap`, `fcmp_oeq_self`: every predicate with its operands swapped, and `oeq x, x` is "not a NaN".
- `fadd_sub_wrong`: `(a + b) - b = a` for operands that aren't NaN or an infinite `b`, which is false, so `bv_decide`
  has to refute it, never prove it.

On y, on 2026-11-09, at `dbfd710`, three formats at a time. Each cell is the verdict, the wall time of the whole Lean
process, startup included, and its peak memory. The records are in
[`spike-results.jsonl`](../prototypes/float/spike-results.jsonl).

| Theorem | `half` | `bfloat` | `float` | `double` |
| --- | --- | --- | --- | --- |
| `fadd_comm` | 2.6 s, 758 MiB | 1.9 s, 690 MiB | 4.9 s, 935 MiB | 13.8 s, 1582 MiB |
| `fmul_comm` | **limit**, 318.6 s, 726 MiB | 16.6 s, 1647 MiB | **limit**, 318.9 s, 821 MiB | **limit**, 318.9 s, 1100 MiB |
| `fadd_negzero` | 0.3 s, 568 MiB | 0.4 s, 568 MiB | 0.6 s, 581 MiB | 0.9 s, 638 MiB |
| `fmul_one` | 0.3 s, 567 MiB | 0.4 s, 568 MiB | 0.5 s, 581 MiB | 0.8 s, 608 MiB |
| `fdiv_one` | 0.4 s, 570 MiB | 0.4 s, 570 MiB | 0.6 s, 590 MiB | 1.9 s, 794 MiB |
| `fdiv_two` | 0.5 s, 579 MiB | 0.6 s, 583 MiB | 1.3 s, 692 MiB | 4.5 s, 1190 MiB |
| `fcmp_swap` | 0.2 s, 557 MiB | 0.3 s, 557 MiB | 0.3 s, 557 MiB | 0.2 s, 557 MiB |
| `fcmp_oeq_self` | 0.2 s, 553 MiB | 0.2 s, 553 MiB | 0.2 s, 554 MiB | 0.2 s, 553 MiB |
| `fadd_sub_wrong` | refuted, 0.3 s, 563 MiB | refuted, 0.3 s, 562 MiB | refuted, 0.4 s, 589 MiB | refuted, 0.5 s, 603 MiB |

A limit is the SAT solver stopping at 300 s, and `bv_decide` saying "If solving your problem relies inherently on using
associativity or commutativity, consider enabling the `acNf` config option". With `acNf`, `fmul_comm` at `half` still
stops at 300 s. Every refutation is `bv_decide`'s counterexample, never a limit.

What it decides:

- **One circuit, at every format, by `bv_decide`.** A rewrite whose source and target differ in one operation, with
  constants for the rest, `x + -0.0`, `x × 1.0`, `x / 1.0`, takes under 2 s at `double`. Two different circuits on one
  free operand, `x / 2.0` against `x × 0.5`, under 5 s. A comparison, under 0.3 s.
- **Two adders on two free operands, at every format.** `fadd`'s commutativity takes 14 s and 1.6 GiB at `double`.
- **Two multipliers on two free operands, only where the significands are small.** At `bfloat`, with 8-bit
  significands, `fmul_comm` takes 17 s. At `half`, `float` and `double` it doesn't finish in 300 s. Algebraic laws of
  multiplication, commutativity and anything built on it, need lemmas: proved once, by hand, for every format, from
  the circuit's own symmetry, and stored. The multiplier is the obstacle, as it is for integers.
- **Not measured yet.** `fp128`, two dividers on free operands, `frem`, whose exact remainder needs `2 ^ e + m + 1`
  bits, 43 at `half` and 2,101 at `double`, and `fma`. Each slice measures what it adds, in the same way, before it
  claims a format is decided.
- **A wrong rewrite is refuted fast,** under 0.6 s at every format, with the input that shows it.

### No `let` in a circuit

A circuit `bv_decide` reads has to be written without `let` or `have`: each value an operation computes is a definition
of its own, of the operation's inputs, marked `@[bv_normalize]`, as fp.lean writes its circuits. This was measured, and
decided the prototype's style, and it's the rule for `IRLean/Float.lean`'s arithmetic:

- **`bv_decide` mishandles binders.** Given definitions to unfold whose bodies bind values with `let`, `bv_decide`'s
  normalizer in Lean 4.35.0 leaves terms that don't type, such as `BitVec.ult` applied to two `Bool`s, or a `bif` whose
  condition is `(15 : Nat)`, abstracts them as unsupported, and reports a counterexample it calls "potentially
  spurious". `have` does the same. Not reported upstream yet.
- **Unfolding first doesn't scale.** `simp only` with the definitions substitutes the `let`s and avoids the bug, but
  for `fadd_negzero` it alone takes 9.7 s at `half` and more than 300 s at `float`, where it was stopped, before
  `bv_decide` starts. A first sweep that unfolded this way ran out of time on every goal at `float` and `double`.
- **Without binders, the same goal takes 0.4 s at `half` and 0.6 s at `float`,** `fmul_one` included, in the same
  process, on y. The circuits are the same functions, and agree with `Float.Model` and the processor as before.

## Checking it

Each operation, as it lands, is checked against four references, in the style of [`tests/opcheck.py`](../tests/opcheck.py),
in a new test, `fpcheck`:

| Reference | How | Where it's exhaustive |
| --- | --- | --- |
| Lean's `Float.Model` | The circuits themselves, against `UnpackedFloat`'s operations, compiled and run | Every pair at small formats, for every operation `Float.Model` has |
| LLVM's constant folder, `APFloat` | The emitted Lean for each operation, run on constants, against `opt -passes=instsimplify` folding the same instruction on them. A NaN result has to be one LangRef allows of the fold's inputs | Every value at `half` for operations of one operand. Sampled for two, and for `float`, `double`, `bfloat` and `fp128` |
| Native code | The same, against the processor, through clang | The same. `half` is native on AArch64, and on x86-64 computed in `float`, which is exact for `+`, `-`, `×`, `/` and `sqrt` |
| Alive2 | For sampled constants, the instruction against the model's result, as a table, in both directions where the result isn't a NaN. Where it is, in one: the instruction as the source and the table as the target, which says the model's NaN is one the instruction may give, since it may give several | Sampled, at every format Alive2 reads |

Two operands at `half` are 2^32 pairs, about 4.3 billion: too many to run the model on in a test, so they're sampled,
with every edge value against every other.

**Rewrites.** Each slice certifies a set of InstCombine's floating-point folds, from its own tests, and refuses wrong
ones, from Alive2's tests of unsound floating-point transformations and LLVM's floating-point miscompilation issues.

## Coverage

Stage 1's breakdown of the emitter's refusals, from `bench/instcombine/stage1.py pairs` on the branch
`feat/stage1-benchmark`, with this branch's emitter at `dbfd710`: 31,240 changed pairs, 12,002 candidates, 18,361
refused by the emitter and 795 refused for memory. By first reason, the emitter refuses 9,035 for floating point,
2,936 for calls outside the module, 1,815 for target intrinsics and 977 for scalable vectors.

The emitter names one reason, the first it meets. Reading the source and target of the 9,222 refused pairs whose
reason names floating point:

| What the pair needs beyond floating point's types | Pairs |
| --- | --- |
| Memory, a call outside the module, or scalable vectors | 2,382 |
| Nothing else: `fneg`, `fabs`, `copysign`, `fcmp`, `bitcast`, `select`, `phi`, `is.fpclass` | 2,225 |
| An intrinsic other than those | 1,944 |
| A rewrite-based fast-math flag | 1,191 |
| Arithmetic | 899 |
| Conversions | 581 |

The commonest operations among them: vectors of floats in 2,743, `fcmp` in 2,318, `fmul` 833, `fneg` 794, `fabs` 748,
`fadd` 696, `fsub` 604, `fdiv` 481, `bitcast` 475, `fpext` 380 and `is.fpclass` 364. Of intrinsics, `minnum` 231,
`maxnum` 223, `ldexp` 207, `maximum` 199, `minimum` 194, `fma` 159, `maximumnum` and `minimumnum` 153 each, `sqrt` and
`pow` 147 each, and `frexp` 136. Flags: `nnan` in 1,014, `nsz` 783, `fast` 733, `ninf` 715, `reassoc` 314, `arcp` 113,
`afn` 101 and `contract` 82.

[`prototypes/float/coverage.py`](../prototypes/float/coverage.py) runs the emitter again on pairs `stage1.py pairs` saved,
with stage 1's own classifier, so every slice is measured on the same pairs:

```sh
git worktree add ../stage1 origin/feat/stage1-benchmark
(cd ../stage1 && mkdir -p build && cp ../ir-lean/build/ir-lean build/)   # the emitter at dbfd710
nix develop -c ../stage1/bench/instcombine/stage1.py --work build/s1 pairs --jobs 12   # about 6 minutes on y
nix develop -c prototypes/float/coverage.py --stage1 ../stage1 --work build/s1 --tool build/ir-lean
```

Each slice's pull request reports how many refused pairs it makes translatable, how many move to another refusal, and
that command.

## The slices

Each is a pull request of its own, merged when CI is green and review approves, with its operations checked as above,
every existing proof still passing, its coverage reported, and [trust](trust.md)'s rows and SEM-05's status current.

1. **Bit-level operations:** the types and constants, `fneg`, `fabs`, `copysign`, `bitcast` between integers and floats,
   `select`, `phi` and `freeze` of floats, `fcmp`, `llvm.is.fpclass` and `nofpclass`, with `nnan` and `ninf` where they
   apply, and the refusals above by name. No operation in it makes a choice.
   **In the model** since 2026-11-09, checked by `tests/fpcheck.py` against the constant folder, the processor and
   Alive2, and by `tests/float.sh` on 18 rewrites, with `nofpclass` lane by lane on vectors, scalable ones
   included, and the lane-moving vector intrinsics on vectors of floats. On the same pairs, it
   makes 1,572 of those the emitter refused at `091275e` translatable, and moves 82 to a refusal for memory. Until a
   fix on 2026-11-09, a fixed-length splat of a float, which LLVM 23 holds as a `ConstantFP` of vector type, printed
   as one lane where a vector goes, which Lean rejects, and in a global's initializer gave only lane 0 its bytes, the
   rest zeros, which made the model read a value LLVM doesn't. 168 of those pairs printed a splat.
2. **Arithmetic and conversions:** `fadd`, `fsub`, `fmul`, `fdiv` and `frem`, `fptrunc` and `fpext`, `fptoui` and
   `fptosi`, poison out of range, `uitofp` and `sitofp`, with `nneg`, and the `*.sat` conversions. Each is a chooser.
   **In the model** since 2026-11-09, written without `let` as the circuits [above](#no-let-in-a-circuit). Checked by
   `tests/fpcheck.py` against the constant folder, the processor and Alive2, with every one of the model's sixteen
   choices of a NaN checked against LangRef's set where IEEE 754 gives one, and by `tests/float.sh` on 14 more
   rewrites, among them `fadd x, -0.0` to `x` and `fadd x, y` to `fadd y, x`, whose proofs name the source's choice.
   On the same pairs, it makes 1,175 of those the emitter refused at `45a55e7` translatable, and moves 29 to a refusal
   for memory.
3. **Fast-math flags:** `nsz` as a choice, as [above](#fast-math-flags), and `nnan`, `ninf` and `nsz` on `select`,
   scalar and vector, applied to the selected value.
   **In the model** since 2026-11-09. Checked by `tests/fpcheck.py`: each operation with `nsz`, under every choice,
   gives exactly what the operation without it gives on its operands with their zeros' signs flipped every way, or its
   result with either sign where that's a zero, and against the constant folder, the processor and Alive2 one way. By
   `tests/float.sh` on 8 more rewrites, among them `fadd nsz x, 0.0` to `x` and `fsub nsz 0.0, x` to `fneg x`, whose
   proofs name the flip, and InstSimplify's `fabs nsz -0.0` to `-0.0`, refuted. `phi` and calls with flags stay
   refused. On the same pairs, against the emitter at `2879b18`, it makes 210 of those the emitter refused
   translatable, 133 refused first for `nsz`, 60 for `nnan` and 17 for `ninf`, and moves 6 to a refusal for memory.
4. **Intrinsics,** by how often InstCombine's tests use them: `fma` and `fmuladd`; `minnum`, `maxnum`, `minimum`,
   `maximum`, `minimumnum` and `maximumnum`; `sqrt` and the rounding family; `ldexp` and `frexp`; then the rest.
   **`fma` and `fmuladd` are in the model** since 2026-11-12, scalar and lane by lane, without fast-math flags, which
   stay refused on them. `tests/fpcheck.py` checks `fma` at every format against the constant folder, the processor
   and Alive2, on edges against edges, random triples, and triples whose addend nearly cancels the product, with
   every NaN choice. x86-64's backend at the pin computes a `bfloat` or `half` `fma` in `float` and rounds twice, so
   where the processor differs there, it's counted apart, only once exact arithmetic shows the model's result is the
   exact one rounded once and the processor's the same rounded through `float`: one case in that run. `fmuladd` is
   `fma` or `fmul` and `fadd` by definition, each checked.
5. **Vectors of floats,** lane by lane, as each operation lands.

What stays out: the four rewrite-based flags, the environments above, `x86_fp80` and `ppc_fp128`, the functions `afn`
approximates (`sin`, `pow` and the rest, which LangRef leaves to the library). Scalable vectors of floats are in, since
the long-tail lane's scalable vectors, [#95](https://github.com/phongndo/ir-lean/pull/95), landed first, and slice 1
wired them up: what applies to a vector of floats applies to a scalable one, lane by lane.

## What it rests on

Once a slice lands, its theorems rest on everything in [trust](trust.md), and on these, which [trust](trust.md) will
list as they become true:

| Assumption | Why it's reasonable | What would break it |
| --- | --- | --- |
| The circuits are IEEE 754's arithmetic | They agree with `Float.Model` on every pair of five small formats, and with the processor, the constant folder and Alive2 where sampled | A bug that shows only at a large format. A theorem equating them with `Float.Model` for every format would close it |
| `Float.Model` is IEEE 754's arithmetic | Lean's developers wrote it as the logical model of `Float` | A bug in it. The processor and the constant folder are checked independently, so both would have to agree with it |
| LangRef's extra NaN payloads are none | LangRef says so of x86 and ARM, and other architectures are refused | A module with no triple that runs on wasm or SPARC |
| The emitter prints each type's format | Tests compare what it prints with LLVM's results | A format confused with another of the same width, `half` with `bfloat`, which `fpcheck` runs both of |
