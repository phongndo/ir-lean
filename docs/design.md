# Design

How `ir-lean` works, and the decisions behind it. Change a decision only with a reason written here.

## What gets emitted

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

## What the model covers

The model covers integers, pointers, structs, vectors of integers, memory, globals, function pointers,
recursion, and `malloc`, `free` and `strlen`. [Memory safety](memory.md) says what of memory it covers, exactly. It doesn't cover floating point, atomics, volatile,
exceptions, or calls to anything else outside the module, and the emitter leaves those functions out
and says why.

For large modules, `--split DIR` writes one Lean module per function, which takes far less memory to check. All
of zlib takes about a minute of CPU one module at a time, and `inflate` about 2.5 GB. Lean that's only proved about,
not run, can use `--no-code`, so Lean doesn't generate code for it: `inflate` checks in 8 seconds instead of 10.

## Decisions

- **The C++ emitter is a printer.** All semantics live in the `IRLean` Lean library. Anything the library
  can't model exactly is refused, not guessed.
- **No LLVM passes in the emitter.** It translates IR as given, so a proof covers what was compiled.
- **Blocks are data.** Each function gets a type with one constructor per basic block, carrying its `phi`
  values and whatever it needs from earlier blocks, plus a `step` function. `IRLean.run` loops over `step`,
  so an emitted non-recursive function contains no recursion of its own.
- **Recursive functions** call their blocks directly, inside a `mutual` block.
- **Poison is a value** (`Val w` is `Option (BitVec w)`), and **UB is separate from non-termination**
  (`Outcome α` is `Option (Except Stop α)`), so a proof can rule out UB.
- **Undefined isn't the same as no answer.** `Stop` is either `undefined`, what LLVM calls undefined behavior, or
  `model`, where the model stops instead of choosing an answer. A refinement can't count the second as UB.
- **Promises are checked, not trusted.** A pointer carries a `Tag` for each argument it came through, saying what
  that argument promised, and tags follow copies, offsets and memory. A function that promises something about
  memory runs in a `Call`, holding its `memory(...)` effects and what it has written. Every access checks both.
  Each call gets a new number, since a pointer can outlive its call, so a theorem's final memory is `m.afterCall`.
- **`tbaa` is out of the IR.** The model doesn't check it yet, so proof targets compile with
  `-fno-strict-aliasing`, and the emitter refuses it.
- **Lean holds at most 244 constructors per type**, and checking a type gets slower faster than it grows,
  so functions over 32 blocks nest their blocks in groups of 16. Recursive functions can't, which limits
  them to 200.
- **Tests run the library natively**, and the compiler replaces `Mem.write` with `Mem.writeCompacting`, which
  keeps a load from walking back through every earlier store. `write_eq_writeCompacting` proves the two equal,
  so a test still runs what the proofs are about, and proofs never see the replacement.
- **Choices the program can't see are oracles in `Mem`:** where each allocation lives, and whether each
  `malloc` fails. A theorem that holds for every `Mem` holds whatever those choices are.
- **Function addresses are allocations that hold nothing.** A call through a pointer tries each function in the
  module with that signature whose address is taken. Anything else stops the model.
- **An `_odr` definition is proved about as this copy.** C++ gives inline functions and templates `linkonce_odr` or
  `weak_odr` linkage, and the linker keeps one copy of each. The one-definition rule says the copies come from the same
  source, not that their IR does the same where that source is undefined, which is why LLVM treats them as possibly less
  refined. So one translates like any other definition, and its theorem is about the copy in this IR, while a call to
  it, directly, through a pointer or an alias, or from itself, is refused, since it may run another copy.
- **A call that doesn't return stops the model.** Calling something outside the module with `noreturn` is
  `ModelStop.noReturnCall`, without saying what it does. A theorem saying `= Outcome.ok` shows it isn't reached.
- **`nobuiltin` on a call is allowed unless the callee is the C library's**, since it only says not to treat a callee as
  a library function, and `Mem` does that for `malloc`, `free` and `strlen`.
- **Vectors are a `Val` per lane**, so one lane can be poison, and an operation on a vector is the scalar
  operation on each lane.

## IR and Lean, both ways

Three different things that are easy to run together.

| Direction | What it is | Status |
| --- | --- | --- |
| **LLVM IR to generated Lean** | The C++ emitter prints one Lean module of shallow definitions. All proofs today go through this | Works, and is the priority |
| **Lean to LLVM IR, for IR itself** | An IR syntax tree as Lean data, with a printer to `.ll` | Planned, only for [Phase 4](roadmap.md#phase-4-certified-translation-validation-and-superoptimization) |
| **General Lean 4 programs to LLVM IR** | A compiler for the Lean language, with its runtime, closures and reference counting | **Non-goal.** Lean has its own compiler, and this wouldn't help verify anything here |

The second direction, if we get there, is built in steps. A step only counts when its check runs in CI.

1. **Syntax tree and denotation:** an IR syntax tree in Lean, and a function giving its meaning in terms of the existing semantics.
2. **A check inside Lean:** the emitter also prints the tree, and Lean checks that its meaning equals the shallow definitions, per function. This moves trust away from the emitter's printing of semantics, leaving how it reads the IR. Whether Lean can check this on `inflate`'s 433 blocks is the open question, so try it on `popcount` and then `crc32_z` first.
3. **Printer, closed by round trip:** Lean prints `.ll`, `opt -passes=verify` accepts it, the emitter reads it back, and Lean checks that the tree is unchanged. The printer needs no proof, since each use checks it. LLVM's parser stays on both sides of that loop, so it stays trusted.

Step 2 is the one piece that could come earlier, since it serves fidelity directly. Treat it as a
research spike after Phase 1, kept only if its costs on real functions are acceptable.

## Targets and machine independence

Clang's IR is already target-specific: it has `sizeof`, ABI lowering, vector widths and target intrinsics
built in. So "machine independent" has to be stated in levels, and a theorem only claims the level it
checked.

| Level | Claim | Status |
| --- | --- | --- |
| L0 | This IR, this triple and data layout | Today. The proofs compile for x86-64 Linux on every host, while `tests/zlib.sh` compiles for the host |
| L1 | The same theorem, with its target and data layout recorded in a manifest | [Phase 0](roadmap.md#phase-0-semantic-fidelity-and-trust-infrastructure) |
| L2 | One spec and one proof script checked separately against each target's own IR, for `x86_64-linux-gnu` and `aarch64-linux-gnu` | [Phase 2](roadmap.md#phase-2-reusable-contracts-and-frame-reasoning) |
| L3 | Other pointer widths or big-endian | Refused for functions using memory, because `Mem` is 64-bit little-endian. No plan until someone needs it |

A one-off probe shows why L2 means separate IR. Compiling freestanding zlib for both targets gives the
same number of translated functions, but different IR: 426 against 347 indented IR lines for `adler32.c`,
388 against 359 for `crc32.c`, and 3,747 against 3,652 for `inflate.c`. A theorem for one says nothing
about the other until it has been checked against it.

The emitter also computes struct offsets and GEP strides from the data layout at translation time, so
generated Lean is tied to that layout. That's fine as long as the manifest records it.
