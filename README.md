# llvm-lean

A Lean backend for LLVM IR.

LLVM backends lower IR to code for a target. This project adds Lean as a target: LLVM IR goes in and
Lean comes out, whichever front end produced the IR, so you can prove things about the code a
compiler actually produced.

## Status

Translates all of zlib's core library, and proves zlib's `adler32` and `crc32`, as clang compiles them
at `-O2`, safe and correct against their RFCs. See [docs/PLAN.md](docs/PLAN.md) for where this is
going, which is proving `inflate` memory-safe.

```console
nix develop
lake build
cmake -S . -B build -G Ninja && ninja -C build
clang -O2 -S -emit-llvm -fno-discard-value-names popcount.c
build/llvm-lean popcount.ll -o Popcount.lean
```

Each function becomes a type with one constructor per basic block, and a `step` function:

```lean
namespace popcount

inductive Block where
  | entry (x : Val 32)
  | while_body (c_06 x_addr_05 : Val 32)
  | while_end (c_0_lcssa : Val 32)

def step : Block → Outcome (Next Block (Val 32))
  | .entry x =>
    let tobool_not4 := Val.icmpEq x (some 0#32)
    br tobool_not4 (.while_end (some 0#32)) (.while_body (some 0#32) x)
  | .while_body c_06 x_addr_05 =>
    let and := Val.and x_addr_05 (some 1#32)
    let add := Val.add c_06 and
    let shr := Val.lshr x_addr_05 (some 1#32)
    let tobool_not := Val.icmpEq shr (some 0#32)
    br tobool_not (.while_end add) (.while_body add shr)
  | .while_end c_0_lcssa => ret c_0_lcssa

end popcount

def popcount (x : Val 32) : Outcome (Val 32) :=
  noundef x <|
  run popcount.step (.entry x)
```

You can then run it, or prove things about it. [tests/proofs/Popcount.lean](tests/proofs/Popcount.lean)
proves that clang's `-O2` output returns the bit count for every input, with no undefined behavior
or poison:

```lean
theorem popcount_correct (x : BitVec 32) :
    popcount (some x) = Outcome.ok (some (pop x))
```

## What's proved

Three theorems against freshly generated Lean, from clang's `-O2` output for real C. Each says the
function returns the right answer, with no undefined behavior or poison, for every input.

| Proof | Source | Against | Proof lines | Check time |
| --- | --- | --- | --- | --- |
| [`Popcount.lean`](tests/proofs/Popcount.lean) | A small example | Counting bits | 66 | About 1 second |
| [`Adler32.lean`](tests/proofs/Adler32.lean) | zlib's `adler32_z` | RFC 1950 | 615 | About 4 seconds |
| [`Crc32.lean`](tests/proofs/Crc32.lean) | zlib's `crc32_z` | RFC 1952 | 1,172 | About 20 seconds |

`crc32_z` is the braided version, with 825 IR instructions across 28 blocks and two global tables. For
any `crc` and a buffer of `len` readable bytes:

```lean
theorem crc32_z_correct {crc len : BitVec 64} (B : Readable m block o len.toNat d) (T : Tables m)
    (hnn : m.addr (bufPtr block o 0) ≠ 0#64) :
    crc32_z (some crc) (some (bufPtr block o 0)) (some len) m =
      Outcome.ok (some (finish (spec (start crc) d len.toNat)), m)
```

## What translates

All 88 functions in zlib's core library, compiled at `-O2`, including `deflate` and `inflate`. That
leaves out the `gz*` files, a layer over file descriptors.

[A harness](tests/real/zlib_harness.c) calls real zlib through every compression strategy, a window
small enough to slide, `inflate_fast`, `inflateBack`, dictionaries, gzip headers and damaged streams.
Lean and native code agree on all 117 results, with none skipped. The harness reaches all but 5 of
zlib's functions, counted without optimization so nothing is inlined away: two for big-endian machines,
`crc32_combine_gen`, `_tr_align` and `_tr_tally`. Inputs are at most about 800 bytes, because the
semantics are slow to run: each memory access walks back through earlier writes.

The model covers integers, pointers, structs, vectors of integers, memory, globals, function pointers,
recursion, and `malloc`, `free` and `strlen`. It doesn't cover floating point, atomics, volatile,
exceptions, or calls to anything else outside the module, and the emitter leaves those functions out
and says why.

For large modules, `--split DIR` writes one Lean module per function, which takes far less memory to
check. All of zlib takes about 3 minutes, and `inflate` about 4 GB.

## Testing

Run `lake build`, then `ctest --test-dir build`, which takes about 30 minutes. Add `-LE slow` to skip
`zlib_slow` and take about 10.

| Test | What it checks |
| --- | --- |
| `opcheck` | Each integer operation against LLVM's constant folder, and against Alive2 for exact poison and UB behavior |
| `differential` | Emitted Lean against natively compiled code, on real C |
| `vectors_pointers` | The same for vectors, function pointers, pointers in globals and the heap, failing if any input is skipped |
| `undefined` | Code LLVM calls undefined stops the model, since comparing with native code can't show that |
| `fuzz` | The same comparison on random functions, optimized at random levels |
| `proofs` | The proofs against freshly generated Lean, and that breaking the C breaks the proof |
| `names` | Every word Lean reserves is avoided in generated names |
| `zlib` | At least 90% of zlib translates, and real calls into it match native code, failing if any input is skipped |
| `zlib_slow` | The same for the calls that slide `deflate`'s window, at minutes each |
| `lint` | Every formatter and linter below, for every language |
| `lsp` | Every language server below starts, opens real files, and reports no errors in them |

## Formatters, linters and language servers

| Language | Formatter | Linter | Language server |
| --- | --- | --- | --- |
| C++ | `clang-format` | `clang-tidy` | `clangd` |
| C test inputs | `clang-format` | `clang -Wall -Wextra` | `clangd` |
| Lean | None exists | Lean's own linters, with `lake build --wfail` | `lake serve` |
| Python | `ruff format` | `ruff check`, `ty check` | `ty server`, `ruff server` |
| Shell | `shfmt` | `shellcheck` | `bash-language-server` |
| Nix | `nixfmt` | `statix`, `deadnix` | `nixd` |
| CMake | `gersemi` | `cmakelint` | `neocmakelsp` |
| TOML | `taplo fmt` | `taplo lint` | `taplo lsp` |
| YAML | `yamlfmt` | `actionlint` | `yaml-language-server` |
| Markdown | `rumdl fmt` | `rumdl check` | `rumdl server` |
| LLVM IR test inputs | None exists | `opt -passes=verify` | None exists |

`tests/lint.sh` runs them all, and `tests/lint.sh --fix` has the formatters rewrite what they can.
`editorconfig-checker` also checks whitespace in every file, which is the only check on how Lean files are
laid out. CI runs all of this, the tests and the proofs on every pull request and push to `main`, and
`zlib_slow` on pushes to `main`.

Python scripts need nothing beyond the standard library, and run through `uv`, which also pins `ruff` and
`ty` in `uv.lock`.

`clangd` needs `build/compile_commands.json`, which `cmake` writes. To open the proofs in an editor, first
run this, so the language server can find the generated modules they import:

```console
tests/proofs.sh build/llvm-lean --generate build/generated
```

## What a proof relies on

- **The emitter:** translating IR to Lean is unverified C++, checked by the tests above.
- **The model:** `LLVMLean` has to match LLVM's real behavior. LLVM's semantics are written in prose,
  not formally.
  One known gap: `getelementptr inbounds` with several indices checks where it ends up, not each step
  as LLVM says, so going out of bounds and back would go unnoticed.
- **Promises the model doesn't check:** attributes such as `noalias`, `readonly`, `memory(none)`,
  `nofree` and `captures`, and metadata such as `tbaa`, say things about the code that the optimizer
  relied on. The model ignores them, so a proof assumes they were true.
- **LLVM below IR:** a proof covers the IR, not the machine code LLVM generates from it.
- **`bv_decide`:** proofs using it trust Lean's compiled code as well as its kernel. To see this, add
  `#print axioms` to a proof file.

Some things stop the model instead of choosing an answer: `freeze` of poison, reading a stored pointer
as an integer, and calling through a pointer to something outside the module. A proof that a function
returns normally still holds in LLVM, but a proof that one of these happens says nothing about LLVM.

Reading uninitialized memory gives poison, where LLVM gives `undef`. Poison is stricter: a result that
isn't poison in the model doesn't depend on those bytes. This caught zlib's `slide_hash` reading
entries of `prev` that were never written, which a comment in its source says is harmless.
