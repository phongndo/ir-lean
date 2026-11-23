# libsodium's Argon2 round

The first pilot of [the engine as it's been since 2026-11-22](roadmap.md): a candidate proposed for a kernel of the
[kernel corpus](kernels.md) outside llama.cpp, checked, timed by the corpus's protocol, and then proved, slice by
slice. For what any theorem here means, read [trust](trust.md) first.

Facts here were checked on 2026-11-22, on z, an AMD Ryzen 9 9950X, with clang 23.1.3 and Lean 4.35.0, against
libsodium `1.0.22-RELEASE`, the corpus's pin, `77e1ce5`.

**It isn't a win yet,** by [what a win is](kernels.md#what-a-win-is). It's measured by the protocol, and its slices
are proved. The proofs are a prototype outside CI, nobody has reviewed their statements, and the step from the slices
to the functions is an argument, not a theorem: [what's left](#whats-left).

## What `clang -O3` leaves

Argon2id spends its time in one unit, `crypto_pwhash/argon2/argon2-fill-block-avx512f.c`. On libsodium's own
`pwhash_argon2id` test in benchmark mode, the corpus's `argon2id` workload, `perf` put 63.7% of the cycles spent in
user code in `fill_block_with_xor` and 35.5% in `argon2_fill_segment_avx512f`, which has `fill_block` inlined.

Both run BLAKE2's round on rows of a 4 by 4 matrix, `A`, `B`, `C` and `D`, eight 64-bit lanes to a vector. A round
mixes the columns, rotates rows `B`, `C` and `D` by one, two and three lanes so that the diagonals become columns,
mixes again, and rotates them back:

```c
#define DIAGONALIZE(A0, B0, C0, D0, A1, B1, C1, D1) \
    B0 = _mm512_permutex_epi64(B0, _MM_SHUFFLE(0, 3, 2, 1)); ...
    C0 = _mm512_permutex_epi64(C0, _MM_SHUFFLE(1, 0, 3, 2)); ...
    D0 = _mm512_permutex_epi64(D0, _MM_SHUFFLE(2, 1, 0, 3)); ...
```

`B` is the last value a mix computes, and the first the next one reads. So the permute of `B` sits on the path
every later instruction waits for. Rotating `A`, `C` and `D` instead, by three, one and two lanes, lines up the same
diagonals, one lane over, and `A`, `C` and `D` are ready before `B` is. It's the choice BLAKE3's implementations
make. clang keeps the rotation where the source puts it: moving it needs the fact that a mix does the same to every
lane, so that rotating its operands rotates its results, and the round's end to undo it.

## The candidate

[`rotate-a.patch`](../prototypes/argon2-rotate/rotate-a.patch) changes twelve lines of
`blamka-round-avx512f.h`: which rows `DIAGONALIZE` and `UNDIAGONALIZE` permute, and by how much. It's a proposal,
and nothing rests on it being right: what's timed and proved is the IR it gives.

[`candidate.py`](../prototypes/argon2-rotate/candidate.py) compiles the unit from the patched header with the
build's own two compile commands, turns each IR into an object with `llc -O3`, puts them in a copy of the build,
and has `make` link the libraries again. The IR the shared library's object comes from differs from clang's in
88 lines, shuffles and the operands of what reads them, in four places: the second half of the round, in each of
the two loops of each function. Both functions change, and no other. Each keeps its number of instructions, 445 and
749.

It was the first candidate proposed, by an agent, of a budget of twenty for this pilot. No other was tried.

## Measured

By [the harness](kernels.md#the-harness), on core 12 alone, one thread. The plan was written down before any
confirmation session: this candidate, as hashed, two sessions of 15 pairs on each of libsodium's two workloads,
with new seeds.

| Workload | Sessions | Pairs | Pooled median | 95% interval | Ratios | Reading |
| --- | ---: | ---: | ---: | --- | --- | --- |
| `argon2id`, exploratory | 1 | 5 | 1.0190 | | 1.018 to 1.025 | Doesn't count |
| `argon2id` | 2 | 30 | 1.0180 | 1.0175 to 1.0185 | 1.011 to 1.026, all above 1 | `faster` |
| `secretstream` | 2 | 30 | 1.0001 | 0.9999 to 1.0003 | | Not slower |

So it's measurably faster by the rule: `timing.py read` gives `faster`, through `irlean.verdict`, with every condition
held, and each session's median is 1.0180. The plan is `plan.txt` beside the records, and the exploratory session is
there too, as `003.json`, which `read` lists and leaves out. A run of the baseline is about 11.9 s, of which about 2.9
s is spent in the kernel, which the candidate doesn't change: in the exploratory session the time in user code fell
from about 8.94 s to 8.73 s. The confirmation sessions' records are in
[`bench/kernels/results/timing/libsodium`](../bench/kernels/results/timing/libsodium), with the hashes of what each
variant loaded.

Each session ran libsodium's own test of Argon2id against its known answers on the candidate first, as the
manifest's check has it, and it passed every time. `secretstream` spends no time in Argon2. It's measured because
the rule asks that no other workload be slower.

## Proved

For each of the four places, and each of the eight vectors that leave it, a theorem that the candidate computes
exactly what clang's IR does, for every value of the eight vectors that enter, poison included:

```lean
theorem r0_o0_same (v327 v333 v336 v337 v343 v349 v352 v353 : Vec 8 64) :
    R0Tgt.r0_o0_tgt v327 v333 v336 v337 v343 v349 v352 v353 =
      R0Src.r0_o0_src v327 v333 v336 v337 v343 v349 v352 v353
```

That's 32 theorems. [`regions.py`](../prototypes/argon2-rotate/regions.py) cuts the slices. The two IRs have the
same instructions under the same numbers, so it compares them line by line: a region runs from the first to the
last differing line of one round, what it reads from before it is a parameter, and each value it defines that a
`store` or a later line reads is an output. Every line of a slice is a line of the function. It stops unless both
versions of a region take the same parameters and give the same outputs.

[`Rotate.lean`](../prototypes/argon2-rotate/Rotate.lean) has the proof, which is the same for all 32: lane by
lane, both sides come to the same expression of the parameters' lanes. It needs no fact about the arithmetic, only
what `shufflevector` and an operation on each lane do to a lane, so each theorem rests on the standard three
axioms, with nothing from `bv_decide`, and all 32 check in under 4 seconds. `leanchecker` replays each of the four
modules through the kernel. The project's own axiom audit, `tests/check_axioms.lean`, which reads a module as data,
wasn't run on them: the axioms are what `#print axioms` says.

A wrong rewrite doesn't pass. [`prove.py`](../prototypes/argon2-rotate/prove.py) plants two in the first place:
row `A` rotated the other way, which stops all 8 of its theorems, and two lanes of one row swapped, which stops 4.
Each stops with an error of its own, unsolved goals, and no limit.

## What it assumes

Everything in [trust](trust.md) applies: these are theorems about LLVM IR in this project's model, and the emitter
is unverified. On top of that:

- **From the slices to the functions is an argument, not a theorem.** Outside the four regions the two IRs are the
  same text, but for the module's name and `uselistorder` lines, which say in what order a value's uses are listed.
  Inside one, the lines that aren't in a slice are `store`s, of the outputs, the same lines in both, which
  `regions.py` checks. So equal outputs give the same stores of the same values in the same order. No proof says that
  here. Both functions translate as built, and the Lean for them elaborates, so [the cut
  lemma](refinement.md#the-cut-lemma) could say it. That isn't done.
- **The static archive's object wasn't sliced.** libtool compiles the unit twice. The proofs are about the IR of the
  object the shared library links, which `argon2id` runs. `secretstream` links the archive, whose object comes from
  the same patched source with `-fPIE`, and runs none of it.
- **One processor.** The timings are z's, a Zen 5. Where a permute costs less, the candidate gains less.
- **The patch isn't upstream, as far as was looked.** libsodium's `master`, at `7614ada` on 2026-11-18, has the header
  the pin has, and so does the Argon2 reference implementation's `blamka-round-opt.h`, which rotates `B` too. Searches
  of both repositories' open pull requests for `argon2` and `blamka` found none that changes it. That's a search, not
  a reading of every pull request. Nothing was sent, and nothing should be without the maintainer's own reading of it.

## What's left

Before this is a win, in the order it would be done:

1. **The proofs in CI.** They're a prototype: nothing in CI builds the candidate, cuts the regions or checks the
   theorems, and the two wrong rewrites aren't a test.
2. **A review of the statements,** by a second agent on another provider's model, as decision 11 asks.
3. **The functions, not the slices,** through the cut lemma, so that cutting and putting back isn't trusted.
4. **A decision on the checkpoint.** Whether this meets it is the roadmap's to say, once
   [#125](https://github.com/phongndo/ir-lean/pull/125) settles how it reads.

## Reproducing it

In `nix develop`, after `lake build` and building `build/ir-lean`. The build is libsodium's own, as
`bench/kernels/profile.sh` makes it, with `make V=1`'s output kept:

```console
src=$(bench/kernels/kernels.py source libsodium)
w=build/kernels/pilot/libsodium && mkdir -p $w/base && cd $w/base
NIX_ENFORCE_NO_NATIVE=0 NIX_HARDENING_ENABLE= CC=clang $src/configure --disable-dependency-tracking
NIX_ENFORCE_NO_NATIVE=0 NIX_HARDENING_ENABLE= make -j16 V=1 >../build.log 2>&1 && cd -
prototypes/argon2-rotate/candidate.py $src $w/base $w/build.log $w/candidate
```

`candidate.py` also writes clang's own IR for each object, from the same command, which the regions are cut
against:

```console
prototypes/argon2-rotate/regions.py $w/candidate.base.pic.ll $w/candidate.pic.ll $w/regions
prototypes/argon2-rotate/prove.py $w/regions
bench/kernels/timing.py session libsodium argon2id --baseline $w/base --candidate $w/candidate \
  --cpus 12 --seed N --kind confirmation --sessions bench/kernels/results/timing
```

The candidate measured has a `libsodium.so.26.4.0` whose SHA-256 starts `07e55016`. Built again from these
scripts on 2026-11-22, it was the same file.
