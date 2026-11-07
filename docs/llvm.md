# LLVM's own code

What `ir-lean` has proved about real code from [llvm/llvm-project](https://github.com/llvm/llvm-project), how to
reproduce it, and what each result rests on. For what any theorem here means, read [trust](trust.md) first.

Facts here were checked on 2026-11-06, with clang 23.1.3 and Lean 4.35.0, against `llvmorg-23.1.3`, on top of commit
`c389ecc`. All 60 source files proved about were compared with GitHub's copy at that tag, and are byte-identical. That
comparison was a one-off. `tests/llvm.py` records their hashes on each run.

## What's proved

86 functions, each with a Lean theorem saying what it returns for every input meeting the theorem's hypotheses, with no
undefined behavior or poison in the model, and no promise from its attributes broken.

| Subproject | Functions | What's there |
| --- | --- | --- |
| `compiler-rt` builtins | 46 | Shifts, `bswap`, `clz`, `ctz`, `ffs`, parity, `popcount`, comparisons and negation at 32, 64 and 128 bits, the abort-on-overflow `addv`, `subv`, `negv` and `absv`, and unsigned division |
| LLVM Support | 29 | 23 from `MathExtras.h`, `decodeULEB128`, `crc32`, `xxh3_64bits`, and `APInt::tcAdd`, `tcCompare` and `tcIsZero` |
| `llvm-libc` | 11 | `abs`, `labs`, `llabs`, and 8 of the `ctype.h` functions |

Ten have loops, and seven read or write memory. These are the five hardest:

| Function | Source | Proved against | Lines of proof | Hypotheses a reader should notice |
| --- | --- | --- | --- | --- |
| `__udivmoddi4` | [`udivmoddi4.c`](https://github.com/llvm/llvm-project/blob/llvmorg-23.1.3/compiler-rt/lib/builtins/udivmoddi4.c) | Lean's `/` and `%`, on all nine paths and the loop | 551 | Nonzero divisor, and a null `rem` or an aligned word in another allocation, from outside any function that promised something about memory |
| `llvm::crc32` | [`CRC.cpp`](https://github.com/llvm/llvm-project/blob/llvmorg-23.1.3/llvm/lib/Support/CRC.cpp) | RFC 1952's bit-at-a-time definition, and its published check value | 282 | Readable buffer, table in place and aligned, a pointer whose address may be looked at, and a build without zlib |
| `llvm::decodeULEB128` | [`LEB128.h`](https://github.com/llvm/llvm-project/blob/llvmorg-23.1.3/llvm/include/llvm/Support/LEB128.h) | What the encoding's bytes are worth, or 0 if that doesn't fit | 345 | Called with only a pointer, an encoding that ends inside readable memory, a non-null address, and `7 * k < 2 ^ 32` |
| `llvm::APInt::tcAdd` | [`APInt.cpp`](https://github.com/llvm/llvm-project/blob/llvmorg-23.1.3/llvm/lib/Support/APInt.cpp) | Addition of the numbers the word arrays hold, with the exact memory afterward | 510, with `tcCompare` and `tcIsZero` | Aligned arrays in different allocations, `c <= 1` as its source asserts, from outside any function that promised something about memory |
| `llvm::xxh3_64bits` | [`xxhash.cpp`](https://github.com/llvm/llvm-project/blob/llvmorg-23.1.3/llvm/lib/Support/xxhash.cpp) | XXH3 written out in Lean, which gives the 11 values in LLVM's own test | 407 | **Only inputs of at most 16 bytes.** Longer inputs are three more algorithms, and aren't covered |

Each of these has a theorem instantiating its hypotheses on real bytes, which shows they can all hold at once.

`__udivmoddi4` with a real pointer says this:

```lean
theorem udivmoddi4_correct (a b : BitVec 64) (hb0 : b ≠ 0#64) (hcalls : m.calls = [])
    (W : Words m [] block o 1 w) (hw : ∀ s, m.allocs block = some s → s.readonly = false ∧ s.stack = false)
    (hnn : m.addr (bufPtr [] block o 0) ≠ 0#64) :
    CrtUdivmoddi4._udivmoddi4 (some a) (some b) (some (bufPtr [] block o 0)) m =
      Outcome.ok (some (a / b), (m.setWords block o 1 (fun _ => a % b)).afterCall)
```

The final memory is exact: everything but the word it wrote is what it was.

## Reproducing it

```console
nix develop
lake build
cmake -S . -B build -G Ninja && ninja -C build
tests/llvm.py build/ir-lean --manifest build/llvm-manifest.json
```

The flake pins the monorepo, by its hash, and the shell's clang is built from the same tag. `tests/llvm.py` fails if they
disagree. For each function it does the following, and a function only counts if all of it passes:

1. Compiles the source with upstream's flags, from [`targets.toml`](../tests/llvm/targets.toml), at `-O3`.
2. Translates the IR to Lean, and checks the proof against that, with warnings as errors.
3. Allows only the standard axioms and what `bv_decide` adds, as [the proofs](testing.md#tests) do.
4. Injects at least one bug into the source, which has to change the IR and stop that function's own proof.

The manifest it writes has, for each function, the theorem statement as Lean prints it, and hashes of the source, IR, Lean
and proof, along with the flags and tool versions.

## What it assumes

Everything in [trust](trust.md) applies: these are theorems about LLVM IR in this project's model. They aren't about source
programs or machine code, and the emitter and the model are trusted. On top of that:

- **Hypotheses are in the theorem.** Nothing else is assumed about inputs. The manifest prints each statement.
- **Reading a function's statement is the check on its spec.** The spec can't be wrong in a way the proof would catch.
  Specs here use Lean's own `BitVec` operations, RFC 1952 and XXH3 as written, and not a copy of the code.
- **`-fno-strict-aliasing`, where memory is involved.** Upstream doesn't pass it. Without it the IR has `tbaa`, which the
  emitter refuses, so proofs about `crc32`, `decodeULEB128`, `xxh3_64bits`, `APInt` and `__udivmoddi4` are about IR that isn't
  quite what a Release build gets. The rest of the `compiler-rt` builtins use upstream's flags exactly.
- **A build without zlib.** `crc32` is its fallback for that, through
  [a small header](../tests/llvm/include/llvm/Config/config.h) in place of the `config.h` CMake generates. Other flags are
  also approximate: only those that change the IR are in `targets.toml`.
- **Wrappers.** Inline functions need a symbol to compile, so [`MathExtras.cpp`](../tests/llvm/wrappers/MathExtras.cpp) and
  [`LEB128.cpp`](../tests/llvm/wrappers/LEB128.cpp) each give some a name. Each only calls one function, which clang inlines.
- **x86-64 Linux.** As with the zlib proofs, this is the one target checked.
- **What happens at an abort isn't claimed.** A call to something outside the module that doesn't return stops the model
  with `noReturnCall`. So `__addvsi3`'s theorem says it reaches that call exactly on overflow, not what the call does.

## What the proofs turned up

No function here is wrong, as far as its source says what it should do. Some do something a reader might not expect:

- **`llvm::PowerOf2Ceil(2^63)` returns 0.** Its doc comment says it returns the power of two at least as large as its input,
  and `2^63` is one and fits. Its check is `A > UINT64_MAX / 2`. A first spec missed this, and failed. Native code at `-O0`
  and `-O3` agrees with the proof.
- **`__clzsi2(0)` and `__ctzsi2(0)` are 32**, though their source says `a != 0` is a precondition, while `__clzdi2(0)`,
  `__ctzdi2(0)` and the 128-bit versions are poison. Only code relying on the precondition is safe across all of them.

Mutants have caught mistakes in this work too. A first set for `__addvsi3` weakened `s >= a` to `s > a`, which the harness
reported as still passing. When `b` is negative those can't differ, so that was never a bug.

Not everything went through. `__llvm_libc::isprint` is left out, since the Lean kernel runs out of memory on its emitted
`step`, with the cause not found.

## What's next

- `decodeULEB128` with its other arguments, `encodeULEB128`, and the rest of `xxh3_64bits`.
- The rest of `APInt`'s word routines, then `KnownBits`, which is LLVM's own reasoning about values.
