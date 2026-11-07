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

So are [86 functions from LLVM itself](docs/llvm.md), at the flags upstream builds them with as far as the emitter allows:
46 from `compiler-rt`, 29 from LLVM Support and 11 from `llvm-libc`, including `__udivmoddi4`, `llvm::crc32`,
`llvm::decodeULEB128`, `llvm::APInt::tcAdd`, and `llvm::xxh3_64bits` for inputs of at most 16 bytes. A search found
rewrites of `__clzsi2` and `__ctzsi2` that are faster than `clang -O3`'s output, and Lean proves they do the same.

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
| [LLVM's own code](docs/llvm.md) | What's proved about llvm-project, how to reproduce it, and what it assumes |
| [Design](docs/design.md) | What gets emitted, what the model covers, and why |
| [Testing](docs/testing.md) | How to run the tests and linters, and what each one checks |
| [Roadmap](docs/roadmap.md) | Where this is going, in what order, and the [first pull requests](docs/roadmap.md#near-term-pull-requests) |

Each fact lives in one doc, and the others link to it. When a result changes, update its doc in the same pull
request, with a link to the test or run that shows it.
