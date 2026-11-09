# What LLVM's code reaches

[BIND-02](llvm-verification-tasks.md#bind-02-implementation-closure): every function and file a unit of LLVM's code can
reach, from the pinned build's call graph. It replaces the inventory's entry files as the anchors a
[code binding](binding-approach.md#what-a-code-binding-claims-evidence-is) has to cover, and it's what gate B2 links into
one module. The first closure is `simplifyAddInst`'s, which gates B2 and B3 need. For what any theorem means, see
[trust](trust.md).

Facts here were checked on top of `2c9e6df` on 2026-11-09, on x86-64 Linux in the dev shell, with LLVM 23.1.3 at
`llvmorg-23.1.3` and its clang.

## How it's found

[`tests/llvm_scope/closure/closure.py`](../tests/llvm_scope/closure/closure.py) `derive` compiles every `.cpp` in
`llvm/lib/IR`, `Analysis`, `Support`, `TargetParser`, `BinaryFormat` and `Demangle`, 413 files, with
[`targets.toml`](../tests/llvm/targets.toml)'s flags for LLVM, which `tests/llvm.py` and #74's census use, and the
include directory upstream's CMake adds for `Support`. Then from the root symbol it follows each direct call: to the
same file's copy for an inline function or template (`linkonce_odr`), through aliases such as a complete-object
constructor's, and otherwise to the one file that defines the function. It records each function with its file,
linkage, instruction count and the SHA-256 of its IR, and every file of llvm-project the reached files read, headers
included, from clang's `-MD`, with its SHA-256. Those files are the closure's anchors. The linker keeps one copy of an
inline function, from any file that has one, and copies can call different functions after `-O3` inlined different
things into each, so it follows the calls of every indexed copy.

Compiling the 413 files took 98 s with 4 jobs on a 32-core machine, peaking at 1.1 GB, and is cached under
`build/closure`. 10 files don't compile with the repo's minimal `llvm/Config/config.h`, since they need what the build's
private one says about the host: `CommandLine`, `ErrorHandling`, `Memory`, `Path`, `PrettyStackTrace`, `Process`,
`SipHash`, `raw_ostream`, `raw_socket_stream` and `TargetParser/Host`. A function only they define is unresolved.

## `simplifyAddInst`'s closure

[`tests/llvm_scope/closure/simplifyAddInst.json`](../tests/llvm_scope/closure/simplifyAddInst.json), from
`llvm::simplifyAddInst(Value *, Value *, bool, bool, const SimplifyQuery &)` in `InstructionSimplify.cpp`:

| | |
| --- | --- |
| Functions reached by direct calls | 2,070: 936 external, 230 internal, 897 `linkonce_odr` and 7 `weak_odr` |
| IR instructions | 240,134 |
| Files compiled | 64: 29 in `IR`, 18 in `Analysis`, 16 in `Support` and one in `TargetParser` |
| Anchors, every file of llvm-project those read | 1,531 |
| Unresolved calls | 18: `raw_ostream`'s writes, `errs()` and `report_fatal_error`, in the files that don't compile, `bcmp`, and `sin`, `cos` and `pow`, which constant folding calls on `double`s |
| Calls into the C and C++ runtimes | 29, such as `std::string`'s and `operator delete[]` |
| Intrinsics called | 43 |
| Functions with indirect calls | 20, with 17 distinct function types |

It's a lower bound on what the code reaches, and it isn't complete: `complete` is false until every call is resolved
and every indirect call has a bound tighter than its type.

**Indirect calls.** Most of the 20 call through a `function_ref`, such as `findValuesAffectedByCondition`'s callback.
The rest are virtual calls, through `CaptureTracker`, `TargetTransformInfo`'s and `AAResults`' implementations, and a
`ValueHandle`, and constant folding's calls through a pointer to `sin` and the like. The bound the emitter would use, any
function of the call's type whose address is taken, is far too coarse to be useful: over the 403 indexed files, it takes
the closure to 10,697 functions, 1,094,167 IR instructions and 314 files, since a type such as `void (ptr)` matches
every destructor and most virtual methods. A bound from the class hierarchy, each virtual call's possible overrides by
its static type, and each `function_ref`'s callbacks from where it's made, is what would make it usable. The IR alone
doesn't carry the static types, so that needs clang's type metadata, which the shipped build isn't compiled with.

**The one-definition rule.** Of the closure's 904 inline functions, 318 have copies in other indexed files whose IR
differs from the copy the closure reached. The linker keeps one copy, and which one isn't recorded. Following only the
reached copy's calls left out three functions another copy calls, which LLVM's own call graph over the linked files
found, such as `detail::scalbn`.

## The closure in one module

`closure.py link` links the 64 files with `llvm-link` and takes the closure out with `llvm-extract`: from the root with
`--recursive`, so LLVM's own call graph adds what it reaches, and every function of the closure that isn't internal by
name, since `llvm-extract` doesn't follow an alias, such as a complete-object constructor's, to the function it names.
The module holds exactly the closure's 2,070 functions. Through the call graph alone it held 1,986, all in the closure,
and the 84 left out are reached only through aliases. `ir-lean --report` translates 284 of the 2,070, 13.7%. The first
reason for each of the rest:

| First refusal, or the first of a function in a cycle with it | Functions |
| --- | --- |
| A call to a function itself refused | 437 |
| `!nonnull` or `!range` on a load | 323 |
| `!noalias`, `!alias.scope` or `llvm.experimental.noalias.scope.decl` | 180 |
| `memory(...)` on a call | 170 |
| A type: vectors of pointers, `<2 x ptr>`, and the like | 157 |
| A global outside the module | 145 |
| A call to a `linkonce_odr` copy | 144 |
| A call attribute `builtin` | 59 |
| A call to a function outside the module | 40 |
| An instruction, mostly `inttoptr` | 40 |
| A recursive function of more than 200 blocks | 38 |
| Attributes, `llvm.memmove`, `undef` and the rest | 53 |

For gate B2's check, `isKnownNegation`: two of the three functions #74's prototype cut, `Instruction::hasNoSignedWrap`
and `APInt::countLeadingZerosSlowCase`, translate once linked in. `isKnownNegation` itself is still refused, first for
`memory(read)` on its call to `countLeadingZerosSlowCase`, which the external-calls lane's work removes, and behind that
for its call to the inline `matchVector`, which needs the policy below. The static `simplifyAddInst` is refused for being
in a cycle of calls with a recursive function of more than 200 blocks, InstructionSimplify's own recursion through
`simplifyBinOp`, which is the emitter's limit.

## The share of the 18-file slice

The census from #74, [`prototypes/binding/census.sh`](../prototypes/binding/census.sh), run again on top of `2c9e6df` on
2026-11-09: 78 of 2,540 functions translate linked, 3.1%, and 146 of 3,703 file by file, 3.9%. That's #74's figure, since
no lane's emitter work has landed since, and `freeze` in the model, F3, which landed after #74 measured, didn't move it.
The first refusals moved by one or two each.

## A policy for the one-definition rule

The emitter refuses a call to a `linkonce_odr` function, as [trust](trust.md#known-gaps-in-the-model) says: the linker
keeps one copy from some file, and copies compiled in different files needn't behave the same where the source is
undefined. Gate B2 needs that changed for a linked closure, and #74's
[stop rule](binding-approach.md#when-to-stop) says it can't be changed without a stated reason the maintainer accepts.
So this is a proposal, and nothing implements it:

1. **A theorem about a linked closure is about the copy `llvm-link` keeps:** the one in the first of the closure's files
   that has it.
2. **It counts for the shipped `opt` only for a function whose every copy is that IR.** For each inline function a
   theorem rests on, every file of the build that has a copy is compiled, and the copies compared. Where all are the same
   IR, the kept copy is the one proved, whichever the linker chose.
3. **Where copies differ, each is a unit of its own,** bound to the same model, so the claim covers whichever is kept.
   318 of the closure's 904 inline functions differ even within the 403 indexed files.
4. **Not proposed: trusting the rule.** Assuming every copy behaves as the kept one where the theorem says the code is
   defined would rest on the source being defined there too. A theorem about the compiled copy can't show that, since a
   compiler may define what the source leaves undefined.

Point 2 needs every file of the build with a copy, which is more than the index: 413 files compiled in 98 s here, and
the shipped `libLLVM` has several times as many. It's the maintainer's to accept or replace.

## The checks

[`tests/llvm_closure_test.py`](../tests/llvm_closure_test.py), in CI as `llvm_closure`: the closure's 1,531 files hash as
recorded, clang is the one it was derived with, and its 64 files compile again to the same 2,070 functions' IR. A
closure with one file's hash changed fails, and so does one with one function's IR changed. It took 23 s with 4 jobs on
2026-11-09. `closure.py check simplifyAddInst` alone hashes the files and checks clang, in about a second.

## Reproduce

```console
nix develop
cmake -S . -B build -G Ninja && ninja -C build ir-lean
tools/measure.py run --label closure --heavy --max-tree-rss-mb 5000 -- tests/llvm_scope/closure/closure.py derive \
  --name simplifyAddInst --root _ZN4llvm15simplifyAddInstEPNS_5ValueES1_bbRKNS_13SimplifyQueryE \
  --file llvm/lib/Analysis/InstructionSimplify.cpp
tests/llvm_scope/closure/closure.py link simplifyAddInst build/closure/simplifyAddInst.ll
tests/llvm_closure_test.py
```
