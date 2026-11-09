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
| [`Crc32.lean`](../tests/proofs/Crc32.lean), with [`CrcSpec.lean`](../tests/proofs/CrcSpec.lean) and [`CrcTables.lean`](../tests/proofs/CrcTables.lean) | zlib's `crc32_z` | RFC 1952 | 1,185 | About 5 seconds | `Readable` buffer, non-null address, `Tables` in place and aligned, and a pointer whose address may be looked at |

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

### Memory safety

zlib's `updatewindow` is proved memory-safe in [`UpdateWindow.lean`](../tests/proofs/UpdateWindow.lean). For every
stream meeting its invariant, with room behind `end`, it returns 0 having changed only the window's first `wsize` bytes
and three fields, and the invariant holds again, so the same holds across any number of calls. It assumes the window is
already allocated. Four more theorems there show four of the preconditions are needed, and
[`MemoryModel.lean`](../tests/proofs/MemoryModel.lean) proves what the model does with invalid accesses.
[Memory safety](memory.md) has the statement, its preconditions, and what it leaves out. These were checked on top of
`6293d34`: 955 lines, about 2 seconds and 0.9 GB, and 223 lines for the model's.

### LLVM's own code

87 functions from `llvm-project` at `llvmorg-23.1.3` are also proved, under the same rules, and each with its own injected bug
that stops its proof. [LLVM's own code](llvm.md) has them, how to reproduce them, what they assume, and two rewrites that
measurably beat `clang -O3`, proved to do the same. Those results are from 2026-11-06, on top of `c389ecc`, apart from
`internal::isalnum`, from 2026-11-07 on top of `6293d34`.

### llama.cpp

A rewrite of the IR clang `-O3` gives llama.cpp's q4_K matrix kernels, at release `b12189`, so they use AVX-512 VNNI.
Lean proves each of the 34 places it changes gives the same result as clang's IR on every input, from slices of the
kernels that include how clang computed their operands. For each of three wrong rewrites, it proves the rewritten slice
differs from clang's at every place. [llama.cpp](llama.md) has the details, what connects the slices to the kernels,
which is a checked argument and not a theorem, and the measurements. CI checks it in a test job of its own, which needs no
model. The proofs were checked on 2026-11-07 on top of `6293d34`, and again on 2026-11-08 merged with `main` at
`0330cd7`, with the same hashes for the IR, every slice and every generated Lean file.

A second rewrite, of the bit unpacking in llama.cpp's Q5 kernel, replaces six instructions with a `bitcast` and the
`select` that ended them.
[`LlamaBitspread.lean`](../tests/proofs/LlamaBitspread.lean) proves the exact slice and its replacement give the same
result for every input, poison included, and that every byte is defined for a defined input. Extracting the slice and
substituting its result are trusted, as for q4_K. [llama.cpp's Q5](llama-q5.md) has the details. Recorded on
2026-11-07, and the proof checked again on 2026-11-08 with the q4_K rewrite and `main` at `0330cd7`.

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
- **What the emitter accepts:** all 17,042 items the pinned IR can contain are classified, 280 modeled, 260
  assumed and 16,502 refused, and a probe of each shows the emitter does what its class says, with the Lean it
  prints for each it translates elaborating ([IR features](ir-features.md)). Since 2026-11-09.
- **Vector forms of integer operations:** the vector forms of 16 intrinsics, vector division and remainder,
  `noundef` and `range` on vectors and structs, and x86's VPTERNLOG, PSHUFB and shifts agree with Alive2 both ways,
  undefined behavior included, and with LLVM's constant folder, on 3,972 inputs to 195 operations, with a wrong
  result for each refuted ([`vecopcheck.py`](../tests/vecopcheck.py)). Checked on 2026-11-09.
- **Scalable vectors:** 43 operations on `<vscale x 4 x i8>` at `vscale` 1, 2 and 4 give exactly what they give
  on fixed-width vectors, on 1,032 inputs, splats agree with LLVM's constant folder, and `llvm.vscale` and
  `vscale_range` agree with LangRef ([scalable vectors](scalable-vectors.md)). Checked on 2026-11-09.
- **Integer operations:** against LLVM's constant folder at many widths, and Alive2 for exact poison and
  UB at small widths: 265 variants proved exact, with none unchecked.
- **Floating point's bit-level operations:** `fneg`, `fabs`, `copysign`, `fcmp`'s sixteen predicates, `llvm.is.fpclass`
  and `nofpclass`, with `nnan` and `ninf`, at `half`, `bfloat`, `float`, `double` and `fp128`, 320 variants, against the
  constant folder on 131,146 cases, the processor on 2,387,018, every operand of the one-operand operations at `half`
  among them, and Alive2 on 2,170 both ways, with none wrong ([`fpcheck.py`](../tests/fpcheck.py)). On y on 2026-11-09,
  where the processor can't run `fp128`.
- **`getelementptr` flags:** 1,194 cases against Alive2, on 644 layouts. 927 are proved exact, and 267 depend on
  the layout as Alive2 confirms, with none unchecked or wrong.
- **Random functions:** fuzzed integer functions at random optimization levels, against native code.
- **Undefined behavior:** 47 functions LLVM calls undefined stop the model ([`ub.ll`](../tests/real/ub.ll)),
  including each promise being broken. 14 memory errors each stop it for their own reason
  ([`memory_errors.ll`](../tests/real/memory_errors.ll)), and `memory_errors` fails if any reason changes. 17 that LLVM doesn't call undefined stop without being called so
  ([`stops.ll`](../tests/real/stops.ll)).
- **Promises kept:** 25 functions that keep their promises match native code with no input skipped
  ([`promises.ll`](../tests/real/promises.ll)).
- **x86 intrinsics and vector bitcasts:** PMADDUBSW, PMADDWD and VPDPBUSD at all three widths, and `bitcast` between
  vectors, agree with the processor on 8,800 results ([`x86.ll`](../tests/real/x86.ll)), which needs AVX-512 VNNI. On
  any processor, the bitcasts, PMADDUBSW and PMADDWD agree with Alive2 both ways and LLVM's constant folder, poison
  included, on 617 inputs to 38 operations, scalar bitcasts among them ([`x86check.py`](../tests/x86check.py)).
  Checked on 2026-11-08.
- **llama.cpp's rewrite natively:** each of the 34 pairs of slices gives the same results on the processor, on 200,000
  inputs each, and each wrong rewrite differs ([llama.cpp](llama.md#checked-another-way)). With the two libraries,
  `llama-perplexity` gives the same logits bit for bit on two models, on 2026-11-07.
- **llama.cpp's Q5 rewrite natively:** both helpers match a byte formula on 1,000,066 inputs, and with the rewrite,
  generating 512 tokens gives the same 77,791,232 FP32 logits bit for bit, with one thread and with eight
  ([llama.cpp's Q5](llama-q5.md#what-is-proved-and-checked)), on 2026-11-07.
- **Dependence on the code:** 16 bugs injected into the C each make a proof stop checking, three of them memory bugs in
  `updatewindow`.
- **Dependence on the rules:** as a one-off, 114 rules for GEPs and promises were each broken in turn. 108 were
  caught. Of the rest, 4 needed new tests, which now catch them, 1 only shows on layouts that can't exist and is
  checked directly in Lean, and 1 is implied by the others, with a proof.

## Measured

The q4_K rewrite makes reading a prompt with llama.cpp 5.5% to 7.2% faster on two models, on a Ryzen 9 9950X with 8
threads, in every round, and generating isn't faster with 8 threads. [llama.cpp](llama.md#measured) has the tables, the
spread and the raw rows. Measured on 2026-11-07 on top of `6293d34`, and not since, as it needs models that aren't in
the repo.

The Q5 rewrite makes generating with one thread about 5% faster, on Qwen2.5-0.5B-Instruct `Q4_K_M`: a median
inference speedup of 1.049x over 30 pairs, with a 95% interval of 1.029x to 1.057x. With eight threads it's
inconclusive. [llama.cpp's Q5](llama-q5.md#performance-and-variance) has the sessions. Measured on 2026-11-07 against
Clang 23.1.5, and not since. `llama_evidence` recomputes the pooled estimates from the committed rows.

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

Checking the translation takes 8 seconds and 1.5 GB, in its own module. Measured before the promise model, the
median `inflate` block was 4 lines of Lean and the largest 49, and proving things about its blocks cost about 14 seconds once per proof file, to build the equations for its `step`, then almost nothing
per block.

`updatewindow` cost far more per instruction: about 365 lines of running blocks for its 83 instructions, or 4.4 each.
It does little arithmetic, but every load, store and copy needs facts about what memory holds, and every store needs
what it left alone. `inflate_fast` is mostly that kind of code, so the estimate below may be low for it.

So the mechanics scale. At `crc32`'s 0.63 lines per instruction, the 4,191 instructions above come to
about 2,600 lines of running blocks, and the earlier plan rounded that to about 3,000. That is an
estimate, and it isn't the hard part. Nothing is measured yet for the invariant, which is.

### What checking costs

Measured on 2026-11-07 on an Apple M4 Max with 16 cores and 64 GB, on top of `6293d34`, with Lean 4.35.0 and clang
23.1.3, while other work kept the load average between 4 and 10. [`tests/proof_bench.py`](../tests/proof_bench.py)
checked each proof alone, 5 times, against the same generated code. Times are medians, and memory is the largest peak
of any run, which on macOS counts about 650 MB of `.olean` files that Lean maps.

| Proof | Before | After | Peak memory before | After |
| --- | --- | --- | --- | --- |
| `CrcTables` | 4.20 s | 1.89 s | 948 MB | 1,227 MB |
| `CrcSpec` | 0.87 s | Unchanged | 808 MB | Unchanged |
| `Crc32` | 2.19 s | Unchanged | 954 MB | Unchanged |
| `Adler32` | 3.69 s | Unchanged | 978 MB | Unchanged |
| `Udivmoddi4` | 7.56 s | Unchanged | 957 MB | Unchanged |

Most of the time goes to `bv_decide`, about 20 ms a call on its own, and `Udivmoddi4` makes 210 calls, 119 of them to
the SAT solver. Two things about Lean 4.35 decide how that adds up:

- **A file checks in order.** Lean elaborates theorems in parallel, but `bv_decide` and `decide +kernel` add
  declarations that wait until every earlier declaration in the file has been checked. So a file of such proofs runs
  on about one core: `Udivmoddi4` takes 7.8 s with `-j1` and 7.4 s with 16 threads. Only separate modules check in
  parallel.
- **The kernel shares work only within one declaration.** `CrcTables` checked each of its nine tables in a theorem of
  its own, working out the same CRC steps again for each. It now checks them in one theorem, with the steps counted so
  that each table's are on the way to the next one's, so each entry is worked out once, at the cost of the memory the
  kernel keeps meanwhile. The theorems `CrcSpec` uses say what they said before.

The tests, with nothing in their caches, `LEAN_JOBS=4`, alternating old and new:

| Test | Before | After |
| --- | --- | --- |
| `tests/proofs.sh`, 25 checks | 29.9, 30.3, 31.1, 32.9 and 42.1 s | 23.5 and 23.6 s |
| `tests/llvm.py`, 86 functions and 99 mutants | 105.0, 105.9 and 143.1 s, using 326 to 328 s of CPU | 83.5, 84.5 and 84.5 s, using 250 s of CPU |

The 143.1 s run had twice the system time of the others, from something else on the machine. For `tests/llvm.py`, a
Mac needs `-D_LIBCPP_DISABLE_AVAILABILITY` in `PROOF_CFLAGS` to compile the C++ targets, so they were compiled against
Apple's C++ headers and not Linux's, as CI does. Every hash, statement, axiom count and mutant in its manifest came out
the same before and after. Most of the time it saves is in mutants of `MathExtras`, which proves 23 functions in one
file: each mutant is now checked against the file only up to the end of its function's theorem. The rest is from the
axiom check importing only the parts of Lean it uses, which takes 0.3 s instead of 0.6 s to start, and from compiling
the four support modules together.

### Probes for later phases

Small one-off experiments, not in CI, to size the work. They are not progress on [Phase 3](roadmap.md#phase-3-c-and-rust-demonstrations).
They predate the allow-lists and the promise model, which refuse more, such as calls to `linkonce_odr` functions and
`noalias` on arguments, so expect fewer to translate now.

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
9. Promises the optimizer leaves, checked or refused. Done, with `mustprogress`, `willreturn` and
   `llvm.loop.mustprogress` [since SEM-07](trust.md#promises-to-progress).
10. `inflate`: [measured](#measured). Its next step is [its invariant](roadmap.md#phase-1-zlib-inflate-memory-safety).
11. A [lemma store](lemma-store.md): 164 checked lemmas from #42, #46, #48 and F3 that later proofs can find, in
    `lake build` and CI, 17 of them used by two proofs. Done in [#60](https://github.com/phongndo/ir-lean/pull/60).
12. Tier-1 proof tests, which run a property on generated inputs and have the kernel check each counterexample. Done,
    for functions without memory: [proof tests](proof-tests.md) has what they refute, and what they can't run.
13. `freeze` in the model, F3: `freeze` of poison is a value each run chooses, and `IRLean.Refines` quantifies over each
    side's choices, so inserting, removing and duplicating a `freeze` are judged as LangRef judges them, and four real
    `instcombine` runs on `freeze` are bound as refinements. `undef` stays out of the model. Done in
    [#72](https://github.com/phongndo/ir-lean/pull/72). See [refinement](refinement.md#runs-that-make-choices).
14. Calls outside the module that access no memory: the run's world answers them, the same world for source and target,
    and which of the callee's answers a call gets is the run's choice, so dropping, merging and reordering such calls
    refine under the attributes that allow it, and adding, duplicating or changing an argument doesn't. Calls with
    effects, and calls that pass or return a pointer, are still refused. See [calls](calls.md).
15. An independent verifier for claims about LLVM's passes, BIND-03, on 2026-11-09: `tools/verify_claims.py` replays
    a claim's evidence from the pinned source, sharing no code with the scorer, and `tests/llvm_scope.py` counts a
    claim only if it agrees. It replays every function in [LLVM's own code](#llvms-own-code) and refuses forged
    claims, each for its own reason. It verifies no claim about a pass yet: none can be complete before INV-04,
    BIND-02 and PASS-05 say what each dimension has to cover. See [verifying claims](verify-claims.md).
16. An inventory of chunk 1's rewrites, INV-04 for InstSimplify, InstCombine, AggressiveInstCombine and Reassociate:
    3,174 at `llvmorg-23.1.3`, 1,950 of them on integers only, each with an ID and its line, derived from the pinned
    source and checked in CI. None is proved for every input yet. See [rewrite inventory](rewrite-inventory.md).
17. Gate B1 of binding proofs to LLVM's C++, on 2026-11-09: `IRLean/LLVMHeap.lean` says what bytes in memory mean as
    LLVM's `Value`, `Use`, `ConstantInt`, `APInt` and `Type`, as the matchers read them, proved kept by
    `ConstantInt::get`, `PoisonValue::get` and `BinaryOperator::Create` as specifications of what each does to memory,
    and a layout probe agrees with it on the pinned `libLLVM`. See [LLVM's IR in memory](llvm-heap.md).
