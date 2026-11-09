# ir-lean

A Lean backend for LLVM IR.

LLVM backends lower IR to code for a target. This project adds Lean as a target: LLVM IR goes in and Lean
comes out, whichever front end produced the IR, so you can prove things about the code a compiler actually
produced.

## Status

All 88 functions in zlib's core library translate at `-O2 -fno-strict-aliasing`, and agree with native code on all
117 results of a test harness, on inputs of about 800 bytes. Three functions, as clang compiles them that way for
x86-64 Linux, are proved correct for every input, with no undefined behavior, poison or broken promises:

| Proof | Source | Against |
| --- | --- | --- |
| [`Popcount.lean`](tests/proofs/Popcount.lean) | A small example | Counting bits |
| [`Adler32.lean`](tests/proofs/Adler32.lean) | zlib's `adler32_z` | RFC 1950 |
| [`Crc32.lean`](tests/proofs/Crc32.lean) | zlib's `crc32_z` | RFC 1952 |

So are [87 functions from LLVM itself](docs/llvm.md), at the flags upstream builds them with as far as the emitter allows:
46 from `compiler-rt`, 29 from LLVM Support and 12 from `llvm-libc`, including `__udivmoddi4`, `llvm::crc32`,
`llvm::decodeULEB128`, `llvm::APInt::tcAdd`, and `llvm::xxh3_64bits` for inputs of at most 16 bytes. A search found
rewrites of `__clzsi2` and `__ctzsi2` that are faster than `clang -O3`'s output, and Lean proves they do the same.

And [a rewrite of llama.cpp's q4_K matrix kernels](docs/llama.md) uses AVX-512 VNNI where `clang -O3` doesn't. Lean
proves each of the 34 places it changes computes what clang's IR does, on every input. On two real models it reads a
prompt 5.5% to 7.2% faster, with the same logits bit for bit. [A second rewrite](docs/llama-q5.md), of its Q5 bit
unpacking, is proved on the exact slice it changes, and makes generating with one thread about 5% faster on one model.

zlib's `updatewindow`, which copies `inflate`'s output into its sliding window, is proved [memory-safe](docs/memory.md)
once the window is allocated: for every state meeting its invariant, with room behind the output it copies, it returns,
changes nothing but the window and three fields, and leaves the invariant holding for the next call.

These are theorems about the LLVM IR, in this project's model of it. They aren't about source programs or
machine code, and they rest on an unverified emitter. [Trust](docs/trust.md) has the details, and the known gaps.

## Quickstart

```console
nix develop
lake build
cmake -S . -B build -G Ninja && ninja -C build
clang -O2 -fno-strict-aliasing -S -emit-llvm -fno-discard-value-names tests/real/bi_reverse.c -o build/popcount.ll
build/ir-lean build/popcount.ll -o build/Popcount.lean
lake env lean build/Popcount.lean
```

`popcount.ll` has a function `popcount`, and [`Popcount.lean`](tests/proofs/Popcount.lean) proves this of it:

```lean
theorem popcount_correct (x : BitVec 32) :
    popcount (some x) = Outcome.ok (some (pop x))
```

## Docs

| Doc | Read it for |
| --- | --- |
| [Status](docs/status.md) | What's proved, what's tested, what's measured |
| [Trust](docs/trust.md) | What a theorem means, what it rests on, and the known gaps |
| [IR features](docs/ir-features.md) | Everything the pinned IR can contain, each item modeled, refused or assumed, and the test that the emitter agrees |
| [Refinement](docs/refinement.md) | What `IRLean.Refines` says, its laws, and what a refinement certificate says about LLVM |
| [Memory safety](docs/memory.md) | What a memory-safety theorem claims, the model of memory, and what it leaves out |
| [Verify](docs/verify.md) | Checking a claim from a script or an agent, with a JSON answer: proved, counterexample, unsupported, timeout or error |
| [Lemma store](docs/lemma-store.md) | Checked lemmas later proofs can find and reuse, the bar each meets, and looking one up from a script or an agent |
| [Proof tests](docs/proof-tests.md) | Tier 1: a property run on generated inputs, with each counterexample shrunk, checked by the kernel and stored. What it measured, and the design of tiers 2 and 3 |
| [Corpus](docs/corpus.md) | Real before-and-after IR from `opt`, one pass at a time, generated on demand for the superoptimizer and lemmas |
| [LLVM's own code](docs/llvm.md) | What's proved about llvm-project, how to reproduce it, and what it assumes |
| [llama.cpp](docs/llama.md) | A proved rewrite of the q4_K kernels that `clang -O3` misses, and what it does to real inference |
| [llama.cpp's Q5](docs/llama-q5.md) | A proved Q5 bit-unpacking rewrite, real CPU generation measurements, and the reproducer |
| [Design](docs/design.md) | What gets emitted, what the model covers, and why |
| [Testing](docs/testing.md) | How to run the tests and linters, and what each one checks |
| [Python](docs/python.md) | What the Python is for, the library every script shares, and the rules that keep it small |
| [Roadmap](docs/roadmap.md) | Where this is going, in what order, and the [first pull requests](docs/roadmap.md#near-term-pull-requests) |
| [Chunks](docs/chunks.md) | The main program: LLVM's 1,162 registered passes in nine chunks, the five gates each goes through, how each gate's percentage is measured, and where each chunk stands |
| [Stage 1](docs/stage1.md) | InstCombine's own rewrites, certified with `bv_decide` and compared with Alive2, and known miscompilations that must not be certified |
| [Prior art](docs/prior-art.md) | What others have built toward proved superoptimization, a lemma store and proof tests, and whether Trivet or Lean-MLIR already cover integer stage 1 |

Each fact lives in one doc, and the others link to it. When a result changes, update its doc in the same pull
request, with a link to the test or run that shows it.

## License

`ir-lean` is under the [Apache License, Version 2.0](LICENSE). Copyright 2026 the `ir-lean` authors.
Contributions are under the same license unless they say otherwise, as section 5 of the license puts it.

Two committed files come from other projects, and keep those projects' licenses:

| File | From | License |
| --- | --- | --- |
| `bi_reverse` in [`tests/real/bi_reverse.c`](tests/real/bi_reverse.c) | zlib 1.3.2's `bi_reverse` in `trees.c`, altered: no longer `local`, and two `__builtin_assume` lines added. Copyright (C) 1995-2026 Jean-loup Gailly and Mark Adler | [zlib](https://zlib.net/zlib_license.html) |
| [`tests/real/llama_q5_bitspread.ll`](tests/real/llama_q5_bitspread.ll) | LLVM IR generated from llama.cpp's Q5 bit-unpacking code, at release `b12189` | [MIT](https://github.com/ggml-org/llama.cpp/blob/b12189/LICENSE) |

The toolchains, libraries and programs the dev shell fetches, such as LLVM, Lean, zlib, llama.cpp and Alive2, aren't
in this repository, and each keeps its own license.
