# `undef` and `freeze`: an experimental semantics

**A prototype. It changes nothing in the model.** [`IRLean/Experimental/UndefFreeze.lean`](../IRLean/Experimental/UndefFreeze.lean)
is a small semantics for LLVM's `undef` and `freeze`, with its tests. `IRLean.lean` doesn't import it, and the emitter
never targets it. No certificate, scorer, status row or `IRLean.Refines` claim rests on it. The model still refuses
`undef` and stops at `freeze` of poison, as [semantic contracts](llvm-semantic-contracts.md#undef-and-freeze) says.

It's here to settle, on a small fragment, what a semantics with `undef` and `freeze` has to say before the model can
have one:

- Each use of a value without `freeze` may see something different, and that includes values computed from `undef`.
- `freeze` chooses once, and every use of it sees that choice. Two `freeze`s choose apart.
- Poison is stronger than `undef`.
- Refinement nests its quantifiers in one order, and moving any of them certifies wrong rewrites.

For what any theorem in this repo means, read [trust](trust.md) first.

## Pins

| What | Pin |
| --- | --- |
| Base commit | `4cd91e5689b0aedc11bae7f01f183fbd1ffbdb93`, `main` after #45 |
| LangRef | `llvm/docs/LangRef.md` at `llvmorg-23.1.3`, sha256 `d05da7672c07beb53a01d77361b2c1a96f4fbd46aa30893cc40542a8a7c1ab2b`, the copy [semantic contracts](llvm-semantic-contracts.md#pins) pins. Sections "Undefined Values", "Poison Values", "Well-Defined Values" and "`freeze`" |
| Lean | 4.35.0, from `lean-toolchain` |
| Alive2 | `a68009c9e81575bdcc249d3cc534514a76112221`, built on LLVM 23.1.3, from `nix/shell.nix` |

## What LangRef says

- `undef`: "the user of the value may receive an unspecified bit-pattern". It's per use, and per register: "an `undef`
  'variable' can arbitrarily change its value over its 'live range'", so `%C = xor %B, %B` with `%B = undef` is `undef`.
  "In fact, `%A` and `%C` need to have the same semantics or the core LLVM 'replace all uses with' concept would not
  hold."
- `%A = add %X, undef` may become `%A = undef`. So a value computed from `undef` is drawn again at each use too.
  Otherwise `sub %A, %A` would be 0 before that rewrite and anything after it.
- "To ensure all uses of a given register observe the same value (even if `undef`), the freeze instruction can be
  used."
- `freeze` of `undef` or poison "returns an arbitrary, but fixed, value". "All uses of a value returned by the same
  `freeze` instruction are guaranteed to always observe the same value, while different `freeze` instructions may
  yield different values."
- Poison: "It is correct to replace a poison value with an undef value or any value of the type."

## The semantics

Two kinds of choice, made at different times.

| Choice | When | Type | Example |
| --- | --- | --- | --- |
| What a use of a value sees | At each use: each operand of each instruction | `UVal w := Val w → Prop`, the set a use draws from | `undef` is every value. Poison is `{none}`. A value `x` is `{some x}`. `add %w, %w` with `%w = undef` is every value, odd ones too |
| What `freeze` gives | Once, when it runs | `Run α := α → Prop`, one result per way the computation's `freeze`s choose | `freeze undef` gives `{c}` for some `c`. Each use of it sees `c` |

An instruction is the model's own operation on `Val`, `IRLean.Val.add` and the rest, flags included, applied to each
draw of its operands, by `lift₁`, `lift₂` and `lift₃`. A register bound without `freeze` is that set, so each use draws
again. `freeze a` chooses one value a use of `a` could see, or any value if a use could see poison, and binds the set
of just that value. Sequencing is the set monad's.

On single values this is the model: `lift₂ f (of a) (of b) = of (f a b)`, and `freeze (of (some x)) = pure (of (some
x))`. Where the model stops, at `freeze` of poison, this chooses among every value. `model_freeze` says both.

A set that holds poison is as weak as poison. LangRef's `%poison = add nsw i1 %k, undef`, commented as poison, is the
set `{-1, poison}` when `%k` is true and `{0, -1}` when it's false. So the comment is exact only for a true `%k`, and
the example's `freeze` branches either way for both.

## Refinement, and the order of its quantifiers

`Refines src tgt` holds when, for every input, every target run is matched like this:

```text
∀ input,                     -- an Arg: any nonempty set, so undef, poison, values and partly undef ones
∀ T, tgt input T →           -- every way the target's freezes choose
∃ S, src input S ∧           -- some way the source's freezes choose, once for the run
∀ b, T b →                   -- whatever a use of the target's result sees
∃ a, S a ∧ ValLe a b         -- a use of the source's result could see something it refines
```

`ValLe` is the model's order on `Val`: poison allows anything, and a value only itself. It's the same as the one
`IRLean.Refines` uses for `Val`.

Inputs range over every nonempty set, which is more than LLVM can pass, so a proof covers every input LLVM has. Each
counterexample uses only `undef`, poison or a value, which LLVM can pass.

It's a preorder: `Refines.refl` and `Refines.trans`. Every instruction, `select`, `freeze`, `pure` and sequencing
respect it: `lift₂_mono`, `select_mono`, `freeze_mono` and `bind_mono`. So replacing part of a computation with a
refinement refines the whole. A target with no result would refine anything. Nothing here has none:
`freeze_total`, `pure_total` and `bind_total`.

Each of these shortcuts certifies a wrong rewrite that `Refines` rejects, in
[`UndefFreezeTests.lean`](../tests/undef_freeze/UndefFreezeTests.lean):

| Shortcut | Wrong rewrite it certifies | Theorem |
| --- | --- | --- |
| Equality of the model's outcomes. Both sides stop at `freeze` of poison | `freeze_duplicated` | `shortcut_model_equality_accepts_freeze_duplicated` |
| One target run, rather than every one, as running it once would see | `ret 0` to `ret (freeze undef)` | `shortcut_some_run_accepts` |
| The source's run chosen after a use of the target's result is seen, as comparing one use of each would | `freeze undef` to `undef` | `shortcut_per_use_accepts`, and `shortcut_per_use_not_compositional`: inside `sub %r, %r` it rejects |
| A register keeps one value for all its uses, without `freeze` | `ret 0` to `%a = add %x, undef; sub %a, %a` | `shortcut_pin_accepts`, and `per_use_follows_langref`: LangRef's own safe rewrite rules it out |

## What's checked

`tests/undef_freeze.sh` runs as the `undef_freeze` test. It runs one process at a time, each Lean process capped at
2 GB and 300 s, and writes only to a temporary directory. It takes about 17 s of CPU and 1.5 GB at most.

| Check | What it shows |
| --- | --- |
| The prototype and its tests build with warnings as errors | The definitions, 32 theorems about them, and 49 tests |
| `tests/check_axioms.lean` and `leanchecker` on both | They rest on the standard axioms and `bv_decide`'s, which the checker reruns, and replay in the kernel |
| LangRef's examples | 18 from "Undefined Values": each one LangRef calls safe is a refinement, and each one it calls unsafe isn't, with a counterexample. `select %X, %Y, undef` to `%Y` is safe when `%Y` can't be poison, and wrong for a poison `%Y`. And all of the `freeze` example: `add %w, %w` is `undef` and can be odd, `add %x, %x` is even in every run, two `freeze`s compared can be true or false, and `freeze` of `add nsw i1 %k, undef` branches either way |
| Rewrites with a known verdict | The `freeze` cases of [negative verification](llvm-negative-verification.md), under their names. `freeze_added_unmodeled`, which the model can't certify, is right here. `freeze_removed` and `freeze_duplicated` are wrong, with counterexamples in LLVM's terms. Also `mul %x, 2` to `add %x, %x`, wrong for `undef`, from "Taming Undefined Behavior in LLVM" (PLDI 2017), section 3, and poison against `undef` both ways |
| Two false claims must fail | Proofs that `freeze_duplicated` and `mul %x, 2` to `add %x, %x` are right each stop with an error that isn't a resource limit |
| A sorried claim must be refused | The axiom check refuses it |
| Five mutants of the prototype | Each makes a copy into a semantics LangRef rules out, and a theorem false under it has to stop with an error of its own: `undef` including poison stops `undef_to_poison_wrong`, `undef` as 0 stops `langref_freeze_y_odd`, `freeze` of poison giving no result, as the model's stop does, stops `freeze_total`, `freeze` drawn at each use stops `freeze_of_none`, and a value allowing poison stops `ValLe.trans` |
| Alive2 agrees, 31 of 31 | `tests/undef_freeze_alive.py` runs `alive-tv`, with `undef` inputs allowed, on each rewrite in `tests/undef_freeze/alive2/` that's LLVM IR, at `i8` or `i1`. It checks Alive2's verdict against the case's, and that the theorem of the same name proves that verdict. A timeout or anything but a proof or a counterexample fails. `zero_to_sub_self_per_use_wrong` is the case that tells per-use registers from fixed ones, and Alive2 finds `%a = 3` with `sub %a, %a = -1` |

## What it trusts and doesn't claim

Trusted:

- The Lean kernel, `tests/check_axioms.lean` and `leanchecker`, as everywhere here.
- That the semantics says what LangRef says. LangRef is prose, so a person has to read both. The vectors check its own
  examples, and the mutants show the tests notice the plausible misreadings named above. Neither shows there's no other
  reading.
- Alive2, only for the cross-check. Its agreement on 31 small rewrites is evidence that the two read LangRef the same
  way here. It isn't a proof that they agree everywhere.

Not claimed:

- **Anything about the model, the emitter, certificates or LLVM's C++.** Nothing uses this yet.
- **Equivalence with LLVM or Alive2 in general.** Values are whole-value sets drawn per use. LangRef also speaks of
  `undef` bits. A set can say anything a per-bit description can, such as `and undef, 0xF0`, and more, such as
  `add (and undef, 1), (and undef, 1)`, which is `{0, 1, 2}`. That this is LLVM's meaning past these examples is a
  reading, not a theorem.

## What it doesn't cover

These are unsupported, not modeled as something else:

- **Undefined behavior.** No operation here can be undefined. Division by `undef`, branching on `undef` or poison, and
  `switch` aren't here. LangRef makes `sdiv %X, undef` undefined, since `undef` could be 0. The UB-free subset is `add`,
  `sub`, `mul`, `and`, `or`, `xor`, `icmp eq`, `slt` and `sge`, and `select`, with the model's flags. `lift₁` and
  `lift₂` take any of the model's operations on `Val` that can't be undefined.
- **Control flow and loops.** It covers straight-line code only. Whether a `freeze` executed twice in a loop chooses
  again isn't tested.
- **Model stops and divergence.** `Run` gives values only. The model's `Outcome` has undefined behavior, stops and
  runs that never end, and combining the two is the next step, below.
- **Vectors, memory, pointers and the byte type.** LangRef freezes vectors element-wise and bytes per bit, and
  uninitialized memory isn't modeled. `freeze` of a pointer gives a non-dereferenceable one.
- **Floating point.** Nothing, as in the model.

## What using it in the model would need

Not started. Each step is a decision for the lanes that own the model, refinement and certificates:

1. A nondeterministic `Outcome`, such as `Run (Outcome (UVal w))`, where a source with undefined behavior on some draw
   allows anything. When an operand of `udiv` is drawn has to be fixed first.
2. Emitted code over `UVal` and `Run`, with `undef` constants as `UVal.undef`, and `freeze` as a bind. That changes the
   type of every emitted function, and every proof and certificate. The deterministic model could stay as the fast
   path for code with neither, since this is the model on single values.
3. A refinement claim for certificates that uses this `Refines`, alongside `IRLean.Refines`, with
   [binding](llvm-proof-binding.md) and the scorer told which one a certificate states.

## Files

| File | What |
| --- | --- |
| `docs/undef-freeze.md` | This page |
| `IRLean/Experimental/UndefFreeze.lean` | The semantics, refinement, and its preorder, congruence and model lemmas. Not imported by `IRLean.lean` |
| `tests/undef_freeze/UndefFreezeTests.lean` | LangRef's examples, rewrites with known verdicts, and the shortcuts |
| `tests/undef_freeze/must_fail/` | Two false claims and a sorried one |
| `tests/undef_freeze/alive2/` | The rewrites as LLVM IR, each with its verdict |
| `tests/undef_freeze.sh`, `tests/undef_freeze_alive.py` | The test, run by `ctest` as `undef_freeze` |

It changes no existing file but `CMakeLists.txt`, which registers the test, and `docs/testing.md`, which lists it.
