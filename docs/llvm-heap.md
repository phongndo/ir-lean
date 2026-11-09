# LLVM's IR in memory

[`IRLean/LLVMHeap.lean`](../IRLean/LLVMHeap.lean) says what bytes in IRLean's memory mean as LLVM's own IR objects, so a
theorem about a compiled matcher, which reads those bytes, is a theorem about the IR they hold. It's gate B1 of
[binding a proof to LLVM's C++](binding-approach.md#gates): [BIND-04](llvm-verification-tasks.md#bind-04-llvms-ir-in-memory-in-lean)
for reading IR. For what any theorem means, see [trust](trust.md).

Facts here were checked on top of `2c9e6df` on 2026-11-09, on x86-64 Linux in the dev shell, with LLVM 23.1.3 at
`llvmorg-23.1.3` and Lean 4.35.0.

## What it covers

`Value`, `Use`, `ConstantInt` with its `APInt`, and `Type`, at the pin on x86-64, as far as `PatternMatch`'s compiled
matchers read them:

| Object | What the view reads | From |
| --- | --- | --- |
| `Value` | The ID, `SubclassID`, the byte at offset 0, and the type, `VTy`, the pointer at offset 8 | `llvm/IR/Value.h` |
| `BinaryOperator` | Its operands: the `Val` of each of its two `Use`s, which come before the object, at offsets -64 and -32 | `llvm/IR/Use.h`, `User.h` |
| `ConstantInt` | Its value, up to 64 bits: the word of its `APInt` at offset 24, with its width at offset 32 | `llvm/IR/Constants.h`, `llvm/ADT/APInt.h` |
| `Type` | Its ID, the low byte of the word at offset 8, and an `IntegerType`'s width, the rest of that word | `llvm/IR/Type.h` |

The IDs are `ConstantIntVal` 5, `PoisonValueVal` 1, and `InstructionVal` 30 plus a binary operator's opcode, 14 for
`add` to 31 for `xor`. Type IDs are 12 for an integer, and 18 and 19 for fixed and scalable vectors.

A `Graph` is the IR the matchers can see: each value's object, `Obj`, which is a `ConstantInt`, a `PoisonValue`, a
binary operator over two other values, or any other value with its ID, and each type, `Ty`. `View M G` says memory `M`
holds `G`: each object and type is where `G` says, laid out as above, every value's type is in `G`, a `ConstantInt`'s
is an integer type of its width, a binary operator's operands are in `G` with its type, no two entries overlap, and no
two values share an address. So comparing addresses, as `m_Specific` does, compares values.

## What's proved

| Theorem | Says |
| --- | --- |
| `View.keep` | A change to memory that keeps every byte the view reads, and changes no allocation's size or address, keeps the view |
| `View.constantIntGet` | `ConstantInt::get(Ty, X)`, as `ConstantIntGet` states what it does, keeps the view and adds the constant, given its precondition that `X` fits in the width |
| `View.poisonGet` | The same for `PoisonValue::get(Ty)` |
| `View.binOpCreate` | The same for `BinaryOperator::Create(Op, S1, S2)`, given that the `Use`s it puts the new ones before have their `Prev` field where the view reads nothing |
| `View.load_id`, `load_type`, `load_word`, `load_width`, `load_op0`, `load_op1`, `load_intType` | Each load the compiled matchers make, at the alignment they make it, gives the field the view says |
| `View.addr_eq_iff` | Two values' addresses are equal exactly when they're the same value |
| `dirty_not_constInt` | A word with a bit set at or above its width is no `ConstantInt` the view describes |

[`tests/llvm_heap/ViewExample.lean`](../tests/llvm_heap/ViewExample.lean) builds a heap byte by byte, with `i8`, the
constant 0, an argument and `sub i8 0, %arg`, proves it meets `View`, so the hypotheses can hold, and does
`ConstantInt::get(i8, 7)` as `ConstantIntGet` states it, which keeps the view and adds 7. Every theorem rests on the
standard axioms, and `leanchecker` replays the module and the example.

## What it trusts

- **The layout.** The offsets and IDs in `Layout` are read from the pinned headers.
  [`tests/llvm_heap/layout_probe.cpp`](../tests/llvm_heap/layout_probe.cpp) is built with the numbers Lean prints from
  `IRLean.LLVMHeap` itself, by [`Facts.lean`](../tests/llvm_heap/Facts.lean), so it checks the numbers the proofs use.
  On objects the pinned `libLLVM` builds, at `i1`, `i8`, `i32` and `i64`, 316 facts hold, and a probe built with the
  `ConstantInt`'s word one field off fails. A wrong layout would make a theorem about the view say nothing about real
  heaps, rather than something false.
- **What each constructor does.** `ConstantIntGet`, `PoisonGet` and `BinOpCreate` state what `ConstantInt::get`,
  `PoisonValue::get` and `BinaryOperator::Create` do to memory. They aren't translations of `Constants.cpp` or
  `Instructions.cpp`, which would need those files' closure through the emitter, gates B2 and B3. The probe checks
  each on the pinned `libLLVM`, finitely: the bytes of what it makes, that the same constant comes back for the same
  type and word and another for another, that each operator's `Use`s hold its operands and the first operand's
  `UseList` and the old first `Use`'s `Prev` are written as `Use::addToList` says, and that what the view reads of
  every value and type already made is unchanged, across 5,000 more constants too, which grow the context's map of
  them. That's evidence for one build on one target, not proof.
- **The context's storage.** `ConstantInt::get` and `PoisonValue::get` may write any byte in `ctx`, the context's own
  storage, and free an allocation wholly in it, such as a map's old buckets when the map grows. `ctx` is a set of
  bytes, not allocations, since `LLVMContextImpl` holds both the maps and the common integer types, which the view
  reads. A theorem using either needs that no byte the view reads is in `ctx`. `BinaryOperator::Create` is stated with
  no place to insert the operator: inserting it also writes the block's list.
- **`APInt`'s clean words.** `APInt` keeps the bits above its width 0, and the compiled matchers rely on it: `m_ZeroInt`
  compares the whole word with 0. The pinned release build doesn't keep it when a caller breaks
  `ConstantInt::get`'s precondition, as [#74](https://github.com/phongndo/ir-lean/pull/74) found: `ConstantInt::get(i1,
  7)` holds the word 7. So the view describes clean words only. `View.constantIntGet` takes the precondition as a
  hypothesis, `hX`, and `dirty_not_constInt` shows a dirty word is no `ConstantInt` the view can describe, so a theorem
  resting on the view says nothing about a heap holding one. The probe found one more consequence: the context finds
  constants by their `APInt`, so that dirty `1` at `i1` is a different object from `ConstantInt::get(i1, 1)`, and two
  `Value *`s hold what the IR calls the same constant.
- **Use lists.** `View.binOpCreate` takes as a hypothesis, `hprev`, that the `Use` each new one goes before has its
  `Prev` field where the view reads nothing. That holds when LLVM's use lists hold only `Use`s, which the view doesn't
  describe yet.

## What it doesn't cover

Use lists, which `m_OneUse` reads; `Instruction`'s other fields, such as its flags and parent; `BasicBlock`; vectors and
their constants; constant expressions; values wider than 64 bits, whose words are behind a pointer; and writing IR,
which is gate B4. A theorem about a matcher that reads any of these needs the view extended first.

## Reproduce

```console
nix develop
lake build IRLean.LLVMHeap
tests/llvm_heap.sh
```

`tests/llvm_heap.sh` builds the module with warnings as errors, checks the example, runs `leanchecker`, and builds and
runs the probe twice, in about 5 s. CTest runs it as `llvm_heap`.
