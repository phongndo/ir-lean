# llvm-lean

A Lean backend for LLVM IR.

LLVM backends lower IR to code for a target. This project adds Lean as a target: LLVM IR goes in and Lean
comes out, whichever front end produced the IR, so you can prove things about the code a compiler actually
produced.

## Status

All 88 functions in zlib's core library translate at `-O2`, and agree with native code on all 117 results of
a test harness, on inputs of about 800 bytes. Three functions, as clang compiles them for x86-64 Linux at `-O2`, are
proved correct for every input, with no undefined behavior or poison:

| Proof | Source | Against |
| --- | --- | --- |
| [`Popcount.lean`](tests/proofs/Popcount.lean) | A small example | Counting bits |
| [`Adler32.lean`](tests/proofs/Adler32.lean) | zlib's `adler32_z` | RFC 1950 |
| [`Crc32.lean`](tests/proofs/Crc32.lean) | zlib's `crc32_z` | RFC 1952 |

These are theorems about the LLVM IR, in this project's model of it. They aren't about source programs or
machine code, and they rest on an unverified emitter and on promises from the optimizer that the model
doesn't check. [Trust](docs/trust.md) has the details.

## Quickstart

```console
nix develop
lake build
cmake -S . -B build -G Ninja && ninja -C build
clang -O2 -S -emit-llvm -fno-discard-value-names tests/real/bi_reverse.c -o build/popcount.ll
build/llvm-lean build/popcount.ll -o build/Popcount.lean
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
| [Design](docs/design.md) | What gets emitted, what the model covers, and why |
| [Testing](docs/testing.md) | How to run the tests and linters, and what each one checks |
| [Roadmap](docs/roadmap.md) | Where this is going, in what order, and the [first pull requests](docs/roadmap.md#near-term-pull-requests) |

Each fact lives in one doc, and the others link to it. When a result changes, update its doc in the same pull
request, with a link to the test or run that shows it.
