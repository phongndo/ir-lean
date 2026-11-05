# Plan

## End state

Point `llvm-lean` at real C compiled by stock clang and get a Lean theorem about that exact compiled
code, at a cost someone would actually pay. The headline result to aim for is real zlib `inflate`,
compiled at `-O2`, proved memory-safe.

## How we know we got there

The thresholds here are proposals, to adjust as we learn.

| Stage | Done when | What it shows | Status |
| --- | --- | --- | --- |
| Trustworthy | At least 90% of zlib's functions translate, with no unexplained mismatches against native in CI | The translator works | Done: 88 of 88 in the core library, and 117 results match native with none skipped. Testing is limited to inputs of about 800 bytes |
| First real proof | `adler32` from `-O2` IR is proved safe and correct against RFC 1950 | Proofs over memory are possible | Done: 615 lines for 65 of C, about 9:1 |
| Affordable | `crc32` and the next function cost far less, with AI provers writing most of it | The cost falls with reuse | Open: see below |
| Headline | `inflate` is proved memory-safe | It scales to code people rely on | Not started |
| Wanted | An outside user adopts it, or it finds a real bug that gets accepted | It matters to someone else | Not started |

### What the second proof cost

The plan's stop condition is a second proof that isn't clearly cheaper than the first. The result is
mixed, so this stage stays open:

| | `adler32_z` | `crc32_z` |
| --- | --- | --- |
| Lines of C (the path clang keeps) | 65 | 84 |
| IR instructions | 351 | 825 |
| Lean on the algorithm, spec and tables | 68 | 653 |
| Lean on running the blocks | 547 | 519 |
| Lean per line of C | 9.5 | 14 |
| Lean on blocks per IR instruction | 1.56 | 0.63 |

Running code did get cheaper, by 60% per instruction, and most block proofs for `crc32_z` worked the
first time. The proof as a whole didn't, because the braid needs real math that `adler32` doesn't. For
a memory-safety proof, like the one planned for `inflate`, the block cost is the one that matters.

## Checks on every proof

- **Real input:** CI regenerates the Lean from clang's output, so nothing can be hand-edited.
- **Break it on purpose:** injecting a bug into the C must make the proof fail.
- **Clean axioms:** `#print axioms` shows no `sorry`, only `bv_decide`'s native axioms.
- **Checked spec:** a person reads the theorem statement, and the spec passes known test vectors.

## When to stop or change course

- The `adler32` proof goes past about 30:1 proof to code, or needs weeks of hand work even with AI
  provers.
- The second proof isn't clearly cheaper than the first.
- Someone else ships the same thing, in which case contribute to theirs instead.

Also try `adler32` in Frama-C or VST. If one gives the same confidence for less work, this project
isn't needed for that job.

That comparison hasn't been done yet.

## Design

- **The C++ emitter is a printer.** All semantics live in the `LLVMLean` Lean library. Anything the
  library can't model exactly is refused, not guessed.
- **No LLVM passes in the emitter.** It translates IR as given, so a proof covers what was compiled.
- **Blocks are data.** Each function gets a type with one constructor per basic block, carrying its
  `phi` values and whatever it needs from earlier blocks, plus a `step` function. `LLVMLean.run`
  loops over `step`, so an emitted non-recursive function contains no recursion of its own.
- **Recursive functions** call their blocks directly, inside a `mutual` block.
- **Poison is a value** (`Val w` is `Option (BitVec w)`), and **UB is separate from non-termination**
  (`Outcome α` is `Option (Except UB α)`), so a proof can rule out UB.
- **Lean holds at most 244 constructors per type**, so functions over 200 blocks nest their blocks.
- **Choices the program can't see are oracles in `Mem`:** where each allocation lives, and whether each
  `malloc` fails. A theorem that holds for every `Mem` holds whatever those choices are.
- **Function addresses are allocations that hold nothing.** A call through a pointer tries each function
  in the module with that signature whose address is taken. Anything else stops the model.
- **Vectors are a `Val` per lane**, so one lane can be poison, and an operation on a vector is the scalar
  operation on each lane.

## Build order

1. Lean library. Done.
2. Emitter for integer functions. Done.
3. Comparison against native code in CI, including generated programs. Done.
4. All integer IR, checked against LLVM's constant folder and Alive2. Done.
5. Function calls and recursion. Done.
6. Memory, then the go/no-go: prove zlib's `adler32`. Done.
7. All of zlib: pointers in globals, function pointers, the C heap, vectors. Done.
8. `crc32`. Done.
9. `inflate`: measured below. The next step is its invariant.

## What `inflate` will take

Measured on clang's `-O2` output:

| | |
| --- | --- |
| `inflate` | 433 blocks, 2,515 IR instructions. The median block is 4 lines of Lean, the largest 49 |
| Checking the translation | 37 seconds and 4 GB, in its own module |
| Proving things about its blocks | About 14 seconds once per proof file, to build the equations for its `step`, then almost nothing per block |
| What it also needs | `inflate_fast` (976 instructions), `inflate_table` (559), `updatewindow`, and the proved `adler32` and `crc32` |

So the mechanics scale. At `crc32`'s 0.63 lines per instruction, running the blocks comes to about 3,000
lines. That's an estimate, and it isn't the hard part.

The hard part is the theorem's invariant, for which nothing is measured yet. Memory safety means that
for any input bytes, `inflate` stays inside its buffers across calls, so it needs a statement of what
`inflate_state` always holds:

- Where `next_in`, `next_out`, `window` and `state` point, and how far each is valid.
- Bounds on `hold`, `bits`, `have`, `nlen`, `ndist` and `wnext`, per decoding mode.
- That `lencode` and `distcode` point into `codes` or the fixed tables, and every link in them stays in
  bounds. This is what `inflate_table` has to establish, and the riskiest part.
- That `inflate_fast`'s window copies stay in range.

The order to do this in, so each step tests the riskiest thing left:

1. `inflate_table`: every entry it writes stays inside `codes`, and links stay in the table it built.
2. `inflate_fast`, assuming tables with that property. This is where a memory bug would most likely be.
3. The invariant across `inflate`'s modes, one mode at a time, starting with stored blocks.

If step 1 goes past about 30:1, or the invariant keeps needing to change with each new mode, stop and
rethink.
