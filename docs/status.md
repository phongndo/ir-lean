# Status

What is true of `ir-lean` today. For what comes next, see the [roadmap](roadmap.md).

Claims are kept apart by kind on purpose. Don't promote one to another in a talk or a paper.

Facts here were checked at commit `a86cfd2` on 2026-11-06, with clang 23.1.3, Lean 4.35.0 and zlib 1.3.2,
unless they say otherwise. `zlib_slow` last passed locally on `a86cfd2`'s model, emitter and proofs. The one-off
probes were last run at `4377c07`, before the allow-lists.

## Proved

Checked by Lean, in CI, against Lean freshly generated from clang's `-O2 -fno-strict-aliasing` output. Each
theorem says the function returns the right answer, with no undefined behavior or poison in the model and no
promise from its attributes broken, for every input meeting its hypotheses.

| Proof | Source | Against | Proof lines | Check time | Hypotheses a reader should notice |
| --- | --- | --- | --- | --- | --- |
| [`Popcount.lean`](../tests/proofs/Popcount.lean) | A small example | Counting bits | 66 | About 1 second | None |
| [`Adler32.lean`](../tests/proofs/Adler32.lean) | zlib's `adler32_z` | RFC 1950 | 651 | About 4 seconds | `Readable` buffer, non-null address, reduced starting sums |
| [`Crc32.lean`](../tests/proofs/Crc32.lean), with [`CrcSpec.lean`](../tests/proofs/CrcSpec.lean) and [`CrcTables.lean`](../tests/proofs/CrcTables.lean) | zlib's `crc32_z` | RFC 1952 | 1,266 | About 8 seconds | `Readable` buffer, non-null address, `Tables` in place and aligned, and a pointer whose address may be looked at |

`Readable` and `Tables` hold for every real layout, called from outside any function that promised something
about memory: LangRef requires of every object that it's smaller than `2^63` and doesn't cross the top of the
address space. `adler32_z_check_value` and `crc32_z_check_value` instantiate them on a real buffer, and give the
published check values, which shows they can all hold at once.

`crc32_z` is the braided version, with 825 IR instructions across 28 blocks and two global tables. For any
`crc` and a buffer of `len` readable bytes:

```lean
theorem crc32_z_correct {crc len : BitVec 64} (B : Readable m ts block o len.toNat d) (T : Tables m ts)
    (hnn : m.addr (bufPtr ts block o 0) ≠ 0#64) :
    crc32_z (some crc) (some (bufPtr ts block o 0)) (some len) m =
      Outcome.ok (some (finish (spec (start crc) d len.toNat)), m.afterCall)
```

`m.afterCall` is `m` with its call counter moved on, and otherwise the same.

These are theorems about modeled IR. [The trust model](trust.md) says what that does and doesn't give you.

## Tested

Evidence and not proof. A pass here means no disagreement was found on the inputs tried.

- **Translation:** 88 of 88 functions in zlib's core library translate at `-O2 -fno-strict-aliasing`, including `deflate` and
  `inflate`, leaving out the `gz*` files, a layer over file descriptors. Translating says the emitter
  accepted them, not that the translation is right.
- **Against native code:** [the harness](../tests/real/zlib_harness.c) calls real zlib through every
  compression strategy, a window small enough to slide, `inflate_fast`, `inflateBack`, dictionaries, gzip
  headers and damaged streams. Lean and native code agree on all 117 results, with none skipped, on inputs
  of at most about 800 bytes, because the semantics are slow to run: each memory access walks back through
  earlier writes. The harness reaches all but 5 of zlib's functions, counted without optimization so
  nothing is inlined away: two for big-endian machines, `crc32_combine_gen`, `_tr_align` and `_tr_tally`.
- **Integer operations:** against LLVM's constant folder at many widths, and Alive2 for exact poison and
  UB at small widths: 265 variants proved exact, with none unchecked.
- **`getelementptr` flags:** 1,194 cases against Alive2, on 644 layouts. 927 are proved exact, and 267 depend on
  the layout as Alive2 confirms, with none unchecked or wrong.
- **Random functions:** fuzzed integer functions at random optimization levels, against native code.
- **Undefined behavior:** 46 functions LLVM calls undefined stop the model ([`ub.ll`](../tests/real/ub.ll)),
  including each promise being broken. 18 that LLVM doesn't call undefined stop without being called so
  ([`stops.ll`](../tests/real/stops.ll)).
- **Promises kept:** 25 functions that keep their promises match native code with no input skipped
  ([`promises.ll`](../tests/real/promises.ll)).
- **Dependence on the code:** 13 bugs injected into the C each make a proof stop checking.
- **Dependence on the rules:** as a one-off, 114 rules for GEPs and promises were each broken in turn. 108 were
  caught. Of the rest, 4 needed new tests, which now catch them, 1 only shows on layouts that can't exist and is
  checked directly in Lean, and 1 is implied by the others, with a proof.

## Measured

What the proofs cost, which is a result about the method and not about zlib. This table was measured before the
promise model. The proofs have since grown by 36 and 58 lines, mostly threading tags through, so the totals are
now 10 and 14.6 lines per line of C, while the split hasn't been measured again.

| | `adler32_z` | `crc32_z` |
| --- | --- | --- |
| Lines of C (the path clang keeps) | 65 | 84 |
| IR instructions | 351 | 825 |
| Lean on the algorithm, spec and tables | 68 | 653 |
| Lean on running the blocks | 547 | 519 |
| Lean per line of C | 9.5 | 14 |
| Lean on blocks per IR instruction | 1.56 | 0.63 |

Running code got cheaper, by 60% per instruction, and most block proofs for `crc32_z` worked the first
time. The proof as a whole didn't, because the braid needs real math that `adler32` doesn't. So the
"Affordable" stage of the old plan, where the second proof is clearly cheaper than the first, stays
open. For a memory-safety proof the block cost is the one that matters.

What `inflate` will take, on clang's `-O2` output:

| | Blocks | IR instructions |
| --- | --- | --- |
| `inflate` | 435 | 2,569 |
| `inflate_fast` | 105 | 976 |
| `inflate_table` | 86 | 563 |
| `updatewindow` | 11 | 83 |

Checking the translation takes 9 seconds and 2.3 GB, in its own module. Measured before the promise model, the
median `inflate` block was 4 lines of Lean and the largest 49, and proving things about its blocks cost about 14 seconds once per proof file, to build the equations for its `step`, then almost nothing
per block.

So the mechanics scale. At `crc32`'s 0.63 lines per instruction, the 4,191 instructions above come to
about 2,600 lines of running blocks, and the earlier plan rounded that to about 3,000. That is an
estimate, and it isn't the hard part. Nothing is measured yet for the invariant, which is.

### Probes for later phases

Small one-off experiments, not in CI, to size the work. They are not progress on [Phase 3](roadmap.md#phase-3-c-and-rust-demonstrations).
They predate the allow-lists and the promise model, which refuse more, such as `linkonce_odr` and `noalias` on
arguments, so expect fewer to translate now.

| Input | Compiled with | Translated | What stopped the rest |
| --- | --- | --- | --- |
| C++ template, class and virtual call, no standard library | `-O2 -fno-exceptions -fno-rtti` | 3 of 3 | |
| The same | `-O2` | 2 of 3 | Exception handling |
| `std::vector` sum and `push_back` | `-O2` | 1 of 2 | Exception handling |
| The same | `-O2 -fno-exceptions` | 1 of 2 | Call to external `operator delete` |
| Rust `no_std` slices, `rustc` 1.95.0 | `-O -C panic=abort` | 3 of 5 | `undef` in a `phi`, and call to external `panic_bounds_check` |

The Rust compiler's LLVM was 21.1.8, while the emitter links LLVM 23.1.3 and so upgrades the IR as it
reads it. That difference is itself a thing [Phase 3](roadmap.md#phase-3-c-and-rust-demonstrations) has to deal with.

## What's been built

1. Lean library. Done.
2. Emitter for integer functions. Done.
3. Comparison against native code in CI, including generated programs. Done.
4. All integer IR, checked against LLVM's constant folder and Alive2. Done.
5. Function calls and recursion. Done.
6. Memory, then the go/no-go: prove zlib's `adler32`. Done, at 615 lines for 65 of C, about 9:1 at the time.
7. All of zlib: pointers in globals, function pointers, the C heap, vectors. Done.
8. `crc32`. Done.
9. Promises the optimizer leaves, checked or refused. Done, apart from `mustprogress` and `willreturn`.
10. `inflate`: [measured](#measured). The next step is [its invariant](roadmap.md#phase-1-zlib-inflate-memory-safety).
