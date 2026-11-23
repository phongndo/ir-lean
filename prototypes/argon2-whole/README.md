# The Argon2 round's rewrite, as whole functions

A spike, outside CI. The candidate rewrite of libsodium 1.0.22's `blamka-round-avx512f.h` changes
`fill_block_with_xor` and `argon2_fill_segment_avx512f` at four regions, each inside one block.
`prototypes/argon2-rotate` (branch `pilot/argon2-rotate-a`) proves each region's slices equal, 32 theorems. This
turns those into a theorem about each function, checked by Lean's kernel, where before the step from slices to
functions was an argument.

## What's proved

For both functions, with `Base` the translation of `candidate.base.pic.ll` and `Cand` of `candidate.pic.ll`:

```lean
theorem fill_block_with_xor_same (a0 a1 a2 : PtrVal) (m : Mem) :
    Outcome.Sim Eq (Base.fill_block_with_xor a0 a1 a2 m) (Cand.fill_block_with_xor a0 a1 a2 m)

theorem fill_block_with_xor :
    Refines (fun a0 a1 a2 m => (Base.fill_block_with_xor a0 a1 a2 m).answered) Cand.fill_block_with_xor
```

and the same two for `argon2_fill_segment_avx512f (a0 : PtrVal) (a1 a2 : Val 64) (m : Mem)`. The first says: where
the baseline returns, the candidate returns the same memory, and where the baseline never finishes, neither does the
candidate. The second is the form `tests/cut/GhAdBlocks.lean` has, and follows from the first. Both rest on
`propext`, `Classical.choice` and `Quot.sound`.

Neither says the two functions are equal: where the baseline is undefined or stops the model, there's no claim.

## How

Two blocks are related when they have the same name and the same fields, memory included, and two results when
they're equal. `Outcome.Sim.promised` then asks, block by block, that related blocks step to related blocks:

- A block that's the same text on both sides is walked by `sim_same`, which gives each instruction's result one
  name for both sides. It uses no fact about any operation, so nothing of `IRLean/Mono.lean`.
- In a block that holds a region, `cut_store` writes the value each side stores as an expression of the eight
  vectors that enter the region, checks it's what that output's slice returns, to the letter, and replaces the
  candidate's by the baseline's with the slice's theorem.
- `argon2_fill_segment_avx512f` calls `fill_block_with_xor`, the baseline its own and the candidate its own.
  `call_same` steps over the call with `fill_block_with_xor_same`.

`Refines.sim_cut` isn't used: it's for a cut that's refined, where the code after has to keep refinement. These
slices are equal.

## Files

- `Whole.lean`: the lemmas and tactics. Nothing in it is about Argon2.
- `gen.py`: writes a function's proof from the baseline's translation, the baseline's IR and `regions.json`. It
  doesn't read the candidate.
- `fill_block_with_xor.main.lean`, `argon2_fill_segment_avx512f.main.lean`: each function's own theorem, about
  its attributes, written by hand. `gen.py` appends it.
- `FillBlockWithXor.lean`, `FillSegment.lean`: what `gen.py` wrote, kept to read. `prove.py --write` writes them
  again.
- `Rotate.lean`: the slices' tactic, from `prototypes/argon2-rotate` on `pilot/argon2-rotate-a`, unchanged.
- `prove.py`: everything from the two IR files: translates, proves the slices, the two functions, replays them
  with `leanchecker`, and plants four wrong candidates, which the same proof files have to stop on.

## Running it

```sh
nix develop -c python3 prototypes/argon2-whole/prove.py build/kernels/pilot/libsodium build/ir-lean \
  .lake/build/lib/lean
```

It needs the pilot's files, `build/ir-lean` and `lake build`. About 30 s. Each Lean process runs under
`timeout 900` and `-M 8000`, one at a time.

## What it doesn't cover

- A cut whose slices are refined and not equal. That needs `Refine.le` between the blocks' fields and
  `IRLean/Mono.lean`, as `tests/cut/GhAdBlocks.lean` does.
- A cut whose results leave another way than a `store` of a vector in the cut's block.
- Checks other than `noundef`, `Mem.dereferenceable` and `Mem.observeAddress`. Each is a lemma of a few lines
  and a row in `checks`.
- Equality of the two functions. It needs a lemma that `run` and `runPromised` give equal results for two `step`s
  that agree through a map between their blocks, which the library doesn't have.
