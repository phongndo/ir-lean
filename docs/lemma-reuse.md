# Lemma reuse

Whether a hard optimization proof can be cut into lemmas that a tool states, checks and keeps, so that the original
proof goes on from them and the next proof starts with some of them. This is a research note on a prototype, in
[`prototypes/lemma-reuse`](../prototypes/lemma-reuse), which is outside the library, the build and CI. It changes
nothing `ir-lean` claims: [status](status.md) and [trust](trust.md) still say what's true.

It's tried on two proofs. The main one is this quarter's q4_K proof: that a VNNI rewrite of llama.cpp's q4_K matrix
kernels computes what `clang -O3` does, at 34 places, which makes reading a prompt 5.5% to 7.2% faster, in
[llama.cpp](llama.md). What's measured below was measured on its branch, `feat/prove-llvm-optimization-1`. The second
is compiler-rt's population counts, where the rewrite is the one `tests/superopt.py` finds, and one `bv_decide` call
can't finish the proof.

Measured on 2026-11-07 on top of `28c2364`, and of `531650a` for the q4_K branch, on an Apple M4 Max with 16 cores
and 64 GB, with Lean 4.35.0, clang 23.1.3 and Alive2 built on the same LLVM, in the dev shell, while other work kept
the load average between 4 and 7. [`check-q4k.sh`](../prototypes/lemma-reuse/check-q4k.sh) and
[`check.sh`](../prototypes/lemma-reuse/check.sh) reproduce everything here but the longer limits, which have their
commands [below](#reproducing). Their last runs are in [`q4k/report.json`](../prototypes/lemma-reuse/q4k/report.json)
and [`report.json`](../prototypes/lemma-reuse/report.json).

## What it found

- **The q4_K proof splits where the rewrite starts.** Each of its 34 theorems runs both slices of the kernel, then
  proves in one go that every operand is what the rewrite needs and that eight `vpdpbusd` and a multiply give what
  eight `pmaddubsw` and a `pmaddwd` do. The tool cuts each one where clang's code and the rewrite stop computing the
  same thing: a core lemma about any operands that meet the facts, and a lemma for each fact about how clang's code
  builds that operand. It saves both, and finishes each theorem with one `exact`.
- **27 lemmas prove all 34 places.** Two core lemmas, one for the 256-bit kernels and one for the 512-bit, cover
  18 and 16 places, and 25 facts cover the operands. 24 of the 34 places needed no new lemma, and took all 4 of
  theirs from the store. Each place's theorem, continued that way, checks in 0.25 to 0.28 s, where `vnni_slice`
  takes 0.34 to 0.72 s: 8.8 s for all 34, against 16.2 s. From an empty store, with each lemma's check, once, and the 12
  facts that don't hold, the checks add up to 23.7 s.
- **It's about the same code the branch proved.** Compiled on this Mac, the kernels' IR hashes the same as the
  IR the branch's manifest records from a Ryzen, and so do all 68 slices.
- **compiler-rt's population counts need cutting, not just reuse.** With a truncation added, `superopt.py`'s search
  finds `ctpop` for `__popcountdi2` and `__popcountti2`. As one `bv_decide` call neither finishes at the default
  limit, and Alive2 can't say either way at its own. Given 600 s, the 64-bit one takes 40 s as one call, and 183 s in
  Alive2. The 128-bit one got no answer in 30 minutes from either. Cut at values that hold counts of set bits, each
  lemma checks in under 0.4 s, and the proofs, continued with them, in 0.6 s and 0.9 s.
- **Saved lemmas carry over there too.** The 128-bit proof takes 3 of its 7 lemmas from what the 64-bit one saved,
  and `popcountsi2_same`, which `Rewrites.lean` already proves, takes 2 of its 5. Those 3 only match because the store
  saved them more generally than the 64-bit proof needed.
- **Every theorem rests on what the project's proofs rest on.** The standard three axioms and `bv_decide`'s, checked
  again by each branch's `tests/check_axioms.lean`, with every module replayed by `leanchecker`. The store isn't
  trusted: a lemma in it is checked again where it's used.
- **Each knows one kind of code.** For q4_K, the core lemma's proof and the facts are the branch's own
  `Vnni.lean`, which a person wrote. The tool decides where to cut, states and keeps the lemmas, and finds which ones
  each place can share. See [the gaps](#gaps).

## llama.cpp's q4_K kernels

What clang leaves and what the rewrite computes are in [llama.cpp](llama.md). In short, at each place clang
computes `pmaddwd(p0 + p1 + ... + p7, c)` with `p_k = pmaddubsw(a_k, b_k)`, and the rewrite computes a chain of eight
`vpdpbusd` on the same `a_k` and `b_k`, times the low half of each lane of `c`. They only agree because clang masks the
weights `a_k` to 4 bits and repeats each scale in both halves of `c`'s lanes. [`tests/llama.py`](../tests/llama.py) cuts each
place out of both kernels, back to loads and arguments, and proves the two slices equal with `vnni_slice`, a tactic
over the 527 lines of [`tests/llama/Vnni.lean`](../tests/llama/Vnni.lean). Alive2 gives no verdict on them: it timed
out after 10 minutes on the first slice of `gemv`, [llama.cpp](llama.md#checked-another-way) says.

### How it splits a place

[`q4k.py`](../prototypes/lemma-reuse/q4k.py) compiles the kernels from the pinned llama.cpp, rewrites them and cuts
out the 34 places with `tests/llama.py`'s own scripts, and checks each slice against its manifest. Then,
for each place, it reads both slices' Lean, which is a list of `let`s:

1. **The cut.** A `let` that both slices have, word for word, is how an operand is built. The ones that differ are the
   rewrite. The shared values the differing ones read are the frontier: at `s00`, the eight weight vectors, the eight
   activation vectors and the scales, 17 in all.
2. **Facts.** For each frontier value, it tries each fact in a small vocabulary that fits its type, `Nibbles` for
   bytes and `Pairs` for 16-bit lanes, both from `Vnni.lean`, as a lemma about how clang's code computes that value,
   from only the arguments it reads, proved by `vnni_facts`. At every place, the weights are `Nibbles` and the scales
   are `Pairs`. The activations aren't `Nibbles`, and those 12 attempts fail, and are recorded so they aren't tried
   again.
3. **The core.** What the rewrite and clang's code compute from the frontier, as a lemma about any values there, with
   the facts that held as hypotheses, proved by what `vnni_slice` does after running both slices. Shortened from
   how it's [saved](../prototypes/lemma-reuse/q4k/store/Lemma_core_01920f5ad1.lean):

   ```lean
   theorem core_01920f5ad1 (x0 : Vec 32 8) (x1 : Vec 32 8) ... (x16 : Vec 16 16)
       (h0 : Nibbles x0) (h2 : Nibbles x2) ... (h14 : Nibbles x14) (h16 : Pairs x16) :
       (Vec.map2 (fun a b => Val.mul a b) (X86.vpdpbusd (... (X86.vpdpbusd (Vector.replicate 8 (some 0#32)) x0 x1)
         ...) x14 x15) ...) =
       X86.pmaddwd 8 (Vec.map2 (fun a b => Val.add a b) (... (X86.pmaddubsw 16 x0 x1) ...)) x16
   ```

4. **The store.** Each lemma is named by a hash of its statement, with the frontier values and arguments renamed in
   order, so the same lemma from any place has the same name. It's checked only if the store doesn't have it.
5. **The original theorem, continued.** The statement is the one `tests/llama.py` writes. The proof runs both slices
   as `vnni_slice` does, then applies the core lemma to the facts, as in
   [`Splits04.lean`](../prototypes/lemma-reuse/q4k/proofs/Splits04.lean):

   ```lean
     unfold S04Tgt.s04_tgt S04Src.s04_src
     rw [run, run]
     simp only [S04Tgt.s04_tgt.step, S04Src.s04_src.step, ret, Outcome.ok]
     refine congrArg (fun x => some (Except.ok x)) ?_
     exact LemmaReuse.Store.core_25cc0c39f5 _ _ ... _ (LemmaReuse.Store.fact_1de73dfe1c v159 v161 v175 v177) ...
   ```

### What's saved, and when it's reused

[`q4k/store`](../prototypes/lemma-reuse/q4k/store) has the 27 lemmas, and its `index.json` says what each states,
which place saved it, which places used it, and the 12 facts that didn't hold.

| Lemma | What it says | Saved by | Places using it |
| --- | --- | --- | --- |
| `core_01920f5ad1` | The 256-bit core: 8 `vpdpbusd` and a multiply are 8 `pmaddubsw` and a `pmaddwd` | `s00` | 18 |
| `core_25cc0c39f5` | The 512-bit core | `s02` | 16 |
| 25 `fact_…` | That a weight vector is `Nibbles`, or a scale vector `Pairs`, from how clang builds it | 10 places | 1 to 8 each |

| Places | Lemmas each needs | From the store | New |
| --- | --- | --- | --- |
| `s00`, the first of `gemv` | 4 | 0 | 4 |
| `s01`, the other of `gemv` | 4 | 2 | 2 |
| `s02`, the first at 512 bits | 4 | 0 | 4 |
| `s03`, `s06`, `s07`, `s18`, `s19`, `s22`, `s23` | 4 | 1 or 2 | 2 or 3 |
| The other 24 | 4 | 4 | 0 |

Each place uses its 4 lemmas 10 times: the core once, and each fact for every operand it covers. The facts differ
between places only in which lanes clang's shuffles take, so the 8 weight vectors at a place need 2 of them.

### Proof time

Each module's own check. The originals and the continued proofs were checked one at a time, and the new lemmas a
place needed in parallel with each other, so the totals are sums of those checks, not time elapsed:

| | Each place | All 34 |
| --- | --- | --- |
| The theorem as `tests/llama.py` proves it, with `vnni_slice` | 0.34 to 0.72 s | 16.2 s |
| The same theorem, continued from the store | 0.25 to 0.28 s | 8.8 s |
| Checking the 27 lemmas, once | 0.29 to 0.56 s a lemma | 10.1 s |
| Trying the 12 facts that don't hold, once | | 4.9 s |

So from an empty store, the split's checks add up to more than proving each place outright, 23.7 s against 16.2 s,
and once the store has its lemmas to about half. The q4_K proofs were never slow. What the split changes is their shape: 34
proofs of everything become 27 lemmas, each checked once, and 34 one-line uses of them, and a new place of a shape
the store knows needs nothing new.

The place theorems rest on the standard three axioms and 4 to 6 from `bv_decide`, as the originals do in the branch's
manifest, and the core lemmas on 1, all from `Vnni.lean`'s own lemmas. The branch's `tests/check_axioms.lean` checks
each place's module and each lemma's, and `leanchecker` replays each.

## compiler-rt's population counts

### The goals

Each says a rewrite returns what clang's code returns, on every input, as the theorems in `Rewrites.lean` do. Neither
side is undefined or poison, so each refines the other. clang's code is compiler-rt's, compiled as
[`targets.toml`](../tests/llvm/targets.toml) says.

| Goal | Rewrite | Alive2, 10 s | One `bv_decide` call, 10 s | With more time |
| --- | --- | --- | --- | --- |
| `popcountdi2_same` | `trunc(ctpop(a))` for `__popcountdi2`, on 64 bits | Unknown | Timed out after 11.5 s | One call: 39.5 s, given 600 s. Alive2: 183 s, given 600 s |
| `popcountti2_same` | `trunc(ctpop(a))` for `__popcountti2`, on 128 bits | Unknown | Timed out after 11.6 s | One call: no answer, given 1,800 s, after 1,951 s. Alive2: timed out, given 1,800 s |
| `popcountsi2_same` | `ctpop(a)` for `__popcountsi2`, on 32 bits | Correct, 0.8 s | Proved in 0.7 s | |

The 32-bit goal is no challenge for one call. It's here to show reuse on a theorem the project already has, the
rewrite in [`tests/llvm/rewrites`](../tests/llvm/rewrites). The other two are in
[`rewrites`](../prototypes/lemma-reuse/rewrites), and `lemmas.py rewrite` checks that the search still finds them. It
runs `superopt.py`'s own `search`, on the IR as `lemmas.py` simulates it, since `ctypes` has no 128-bit integers, and
adds the truncation that the search's grammar can't express.

### How it cuts a proof

Without a hand-written proof of clang's code to go through, the original proof is:

```lean
theorem popcountdi2_same (a : BitVec 64) :
    RwPopcountdi2._popcountdi2 (some a) = CrtPopcountdi2._popcountdi2 (some a) := by
  llvm_exec RwPopcountdi2._popcountdi2
  llvm_exec CrtPopcountdi2._popcountdi2
  apply IRLean.result_congr
  bv_decide
```

The first three steps take 0.6 s, even at 128 bits. They leave `BitVec.setWidth 32 a.cpop` on one side and clang's 18
instructions on the other: two very different ways of adding up 64 bits, which is where the solver runs out of time.
[`lemmas.py`](../prototypes/lemma-reuse/lemmas.py) keeps the first three steps, and replaces the last:

1. **It finds cut points by running clang's code.** On a few hundred inputs, it looks for values that hold, in each
   `k`-bit field, the count of the input's set bits in that field. In `__popcountdi2` those are `%sub`, with 2-bit
   fields, `%add`, with 4, and `%and6`, with 8. After the last of them it takes the values that everything later
   reaches only through them, and for each step from one to the next, finds which input fields each output field adds
   up, by setting one field to 1 at a time. It checks that on random fields within what the goal needs, and then
   finds the largest bound for which it still holds.
2. **It states a lemma for each step.** The first cut, from the input, is a lemma on the whole input, proved by
   `bv_decide`. The rewrite's side becomes a sum of the fields' counts, by an instance of `cpop_fieldSum`, which
   [`Count.lean`](../prototypes/lemma-reuse/Count.lean) proves once, by induction, for every width. Each step after
   the first cut is a lemma about fresh variables, proved by `bv_decide`, such as this one, shortened from
   how it's [saved](../prototypes/lemma-reuse/store/Lemma_step_6934d83747.lean):

   ```lean
   theorem step_6934d83747 {x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8} (_h0 : x0 ≤ 127#8) ... (_h7 : x7 ≤ 127#8) :
       BitVec.setWidth 32 (((x7 ++ x6 ++ x5 ++ x4 ++ x3 ++ x2 ++ x1 ++ x0) >>> 32#64) +
         (x7 ++ x6 ++ x5 ++ x4 ++ x3 ++ x2 ++ x1 ++ x0)) =
         (x7 + x3) ++ (x6 + x2) ++ (x5 + x1) ++ (x4 + x0)
   ```

3. **It looks in the store for each lemma, and checks the rest,** each in a module of its own, so they check in
   parallel. A step is checked at the largest bound simulation found, and at what the goal needs if Lean disagrees.
   What checks is saved.
4. **It continues the original proof.** It rewrites the first cut and the population count, introduces a variable
   for each 8-bit field's count with `field_le`'s bound on it, rewrites each step with the fields it has there,
   leaving each bound to `bv_decide`, and ends with `ac_rfl`, since both sides are then sums of the same variables.
   The [finished proofs](../prototypes/lemma-reuse/proofs) are what Lean checked.

That's the cut the hand-written `popcountdi2_correct` in [`Popcountdi2.lean`](../tests/llvm/Popcountdi2.lean) makes,
at bytes, with `fold8` and `fold4Small` from [`Bits.lean`](../tests/llvm/Bits.lean) as its steps. Here the tool finds
the cut, and its steps are smaller.

If the lemma for the first cut runs out of time, it's replaced by one for each cut inside it, each from the one
before. `--finest` does that anyway, and gives 3 lemmas, from 2- to 4- to 8-bit fields, which check and give the same
theorem. No goal here needs it.

### What's saved, and when it's reused

The [store](../prototypes/lemma-reuse/store) is a directory of Lean modules, a lemma each, and `index.json`, which
says what each lemma states, the bound it was proved for and the one its first goal needed, how long it took to
check, which goal saved it and which goals used it. A lemma's name is a hash of its statement with the bound left
out, so the same step, from any goal, has the same name. A goal takes a lemma from the store if it says the same,
with a bound at least what the goal needs, and proves each bound where it uses it.

| Lemma | Step | Bound, and what its first goal needed | Saved by | Also used by |
| --- | --- | --- | --- | --- |
| `step_6934d83747` | 8 bytes in 64 bits, `(X >>> 32) + X`, to 32 bits | 127, 8 | 64-bit | 128-bit |
| `step_baa1347fcb` | 4 bytes in 32 bits, `(X >>> 16) + X` | 127, 16 | 64-bit | 128-bit, 32-bit |
| `step_81f8a11ca6` | 4 bytes in 32 bits, `(X >>> 8) + X` | 127, 32 | 64-bit | 128-bit, 32-bit |
| `step_344daa4124` | `X &&& 127` | 127, 64 | 64-bit | |
| `step_3d395ad3fc` | 16 bytes in 128 bits, `(X >>> 64) + X`, to 64 bits | 127, 8 | 128-bit | |
| `step_b4f1aa7047` | `X &&& 255` | 255, 128 | 128-bit | |
| `step_b7ebfec089` | `X &&& 63` | 63, 32 | 32-bit | |
| `layer_…`, `split_…` | The first cut, and the population count as a sum, one of each for each width | | Each goal | |

Generalizing is what lets these carry. The 128-bit proof needs the 64-bit proof's first step for fields up to 16,
where the 64-bit proof needed 8, and the next two for fields up to 32 and 64. The 32-bit proof needs them for up to 8
and 16, less than the 64-bit proof did. Saved as first needed, 2 of the 5 would have matched.

Counting `field_le` and `cpop_fieldSum` from `Count.lean`, which every goal uses, 5 of the 9 lemmas the 128-bit proof
uses come from a shared library, and 4 of the 7 the 32-bit one uses. Phase 2 of the [roadmap](roadmap.md) asks for
60% of each proof's lemmas. This is close, and short of it.

### Proof time

From an empty store, in the order of [`goals.toml`](../prototypes/lemma-reuse/goals.toml), leaving out Alive2 and
the one-call attempt, which `check.sh` also runs:

| Goal | Lemmas | Checking them, in parallel | Continued proof | Axioms and kernel replay | From start to end |
| --- | --- | --- | --- | --- | --- |
| `popcountdi2_same` | 6 found, 0.30 to 0.32 s each | 0.6 s | 0.6 s | 5.5 s | 7.4 s |
| `popcountti2_same` | 4 found, 0.25 to 0.38 s each, and 3 from the store | 0.7 s | 0.9 s | 6.5 s | 8.8 s |
| `popcountsi2_same` | 3 found, 0.24 to 0.26 s each, and 2 from the store | 0.5 s | 0.5 s | 4.6 s | 6.1 s |

Each also spends 0.6 s compiling and translating clang's code and the rewrite. A lemma from the store costs nothing
once compiled, as `build/lemma-reuse` keeps its `.olean`, and what it took the first time when a new checkout
compiles it again from the store: `check.sh`'s second run does that, with `--fresh`, in 0.24 to 0.37 s a lemma.

Against the other ways to prove the same:

| | 64 bits | 128 bits |
| --- | --- | --- |
| One `bv_decide` call | 39.5 s, given 600 s | No answer, given 1,800 s |
| Alive2 | 183 s, given 600 s | Timed out, given 1,800 s |
| Cut into lemmas: checking the lemmas, then the proof | 0.6 s and 0.6 s | 0.7 s and 0.9 s |
| The hand-cut proof of clang's code against `cpop`, its whole file | 0.8 s | 1.1 s |

The hand-cut proofs are of a different theorem, clang's code against `cpop` rather than against a rewrite, but that's
the hard half of each goal here: the rewrite's half is `llvm_exec` alone.

Don't overread this:

- **Cutting saves the time, and reuse saves the finding.** Each lemma here checks in a third of a second, so taking 3
  from the store saves about a second. What it saves is lemmas that don't have to be found, stated, generalized and
  checked, which matters more where finding them is the hard part.
- **One machine's timings,** with other work running, and none of it in CI.

## What it rests on

A proved theorem is about the two functions or slices as this LLVM IR, in this project's model of it, and rests on
everything [trust](trust.md) lists, the emitter among them. For q4_K, that's the branch's model, with its x86
intrinsics, and its emitter. Beyond that, for the population counts:

- **`bv_decide`'s axioms**, one for each call, in every lemma and in the continued proof: 31, 43 and 21 of them.
  `tests/check_axioms.lean` reruns the toolchain's checker on each, as `tests/llvm.py` does, and allows nothing but
  those and the standard three.
- **The kernel,** which replays the continued proof, every lemma it uses, `Count.lean`, `Bits.lean` and `Kit.lean`,
  through `leanchecker`. So neither the store nor its index is trusted: a lemma in the store is checked again by Lean
  where it's used, and a wrong one would stop the proof. `check.sh` tries one that's proved by an axiom of its own,
  which Lean accepts, and the goal using it stops at `not an allowed axiom: LemmaReuse.Store.trust_me`.
- **Nothing the tool finds by running code.** Cut points, how fields add up and how general a lemma is are only what
  to ask Lean. A wrong guess costs a lemma that doesn't check, never a wrong theorem.
- **`llvm_exec`**, which discharges `nuw`, `nsw` and the return's `range` with `bv_decide` on the whole input, before
  any cut, as every proof in `tests/llvm` does.

Each entry in `report.json` lists these under `assumptions`, and the axioms under `audit`.

For q4_K, the same holds of the store, the cut and the facts: the facts tried are only what to ask Lean, and the
store is checked again where it's used. The compile on a Mac needs one change the branch doesn't make: the dev
shell's libc++ assumes an Apple target, so `q4k.py` compiles with a copy of its configuration that turns off
Apple's availability markup. The IR comes out byte for byte what the branch's manifest records, which is the check
that this changed nothing that matters.

## Gaps

For q4_K:

- **The proof of the core is the branch's.** The core lemma is proved by `final` and `vnni_inv`, and the facts by
  `vnni_facts`, all from `Vnni.lean`. The tool decides where to cut, and which facts each operand has, but doesn't
  find the invariant that makes eight 16-bit sums one 32-bit sum. A new rewrite needs its own.
- **The vocabulary is two facts,** chosen by an operand's type. A fact outside it, or about an operand the rewrite
  changes, isn't found.
- **Two cores, because two widths.** The 256-bit and 512-bit cores are the same argument on different numbers of
  lanes. Lemmas for every width would need statements with the width as a variable.
- **It needs llama.cpp's source,** which only `nix develop .#llama` has, as the default shell leaves it out.
- **No speedup the first time.** From an empty store the split checks 7.5 s more than the original proofs.
- **Only the 34 places.** [Q5](llama-q5.md) and the other quantizations use other proofs, and nothing here was tried
  on them.

For the population counts:

- **One kind of code.** It cuts code that adds up counts of set bits field by field, against a rewrite that counts
  set bits. `clz`, `ctz`, parity, anything with branches, loops or memory, and functions of more than one argument it
  reports it can't cut. Each would need its own notion of what a cut point holds, and seed lemmas for it. Given
  `Rewrites.lean`'s `clzsi2_same`, through `--goals`, it says `@__clzsi2 has what this doesn't model: %cmp = icmp
  ult i32 %a, 65536`. Given `ctpop` as a rewrite of `__paritydi2`, which is false, it says `no value holds
  field-by-field counts of the input`, and one `bv_decide` call refutes it in 0.3 s.
- **Constants and widths don't carry.** A lemma is reused if its statement is the same, under a weaker bound. The
  three last steps differ only in their masks, 127, 255 and 63, and are three lemmas. Each width has its own first
  cut and its own sum. Lemmas for every width would need proofs by induction, as `Count.lean`'s are, rather than
  `bv_decide`.
- **The same step, written differently, is a different lemma,** such as with an addition's operands swapped.
- **The split of a first cut that runs out of time is untested by a real timeout.** No goal here needs it, and
  `--finest` only shows the smaller lemmas compose.
- **Statements have to match `llvm_exec`'s goal exactly**, for `rw` to find them. They do for these three. A mismatch
  stops the continued proof, and can't prove anything wrong.
- **`llvm_exec`'s own `bv_decide` calls aren't cut.** They take 0.6 s at 128 bits, but at a width where they didn't
  finish, nothing here would help.
- **No versioning.** A store from another Lean, ir-lean or `Count.lean` has to be checked again, which `--fresh`
  does, and a lemma that stops checking is reported, not repaired.
- **Hypotheses that hold of everything stay.** `step_b4f1aa7047` asks for `x ≤ 255#8`, which every 8-bit value is.
- **The rewrites aren't benchmarked.** `superopt.py --bench` needs x86-64 Linux, and this ran on a Mac. A rewrite
  is only proved to do the same, not shown to be faster.
- **The search ran on simulated IR,** not on native code as `superopt.py` does, so it depends on `lemmas.py`'s
  reading of a dozen instructions. The theorem doesn't.

## Reproducing

The q4_K proof needs llama.cpp's source, which only `nix develop .#llama` has:

```console
nix develop -c bash -c 'lake build && cmake -S . -B build -G Ninja && ninja -C build'
nix develop .#llama -c prototypes/lemma-reuse/check-q4k.sh .
```

That proves the 34 places from an empty store, and again from what that saved, checking each lemma again, and
compares what was saved with [`q4k/store`](../prototypes/lemma-reuse/q4k/store) and its proofs. On 2026-11-08, with
the q4_K proof merged with `main` at `0330cd7`, on the Ryzen 9 9950X its measurements are from, it proved the 34
places, matched all 68 slices to the manifest, and saved the same lemmas and proofs as the store here, in 1 minute 43
seconds with 6 Lean jobs.

The population counts, from this repo, in `nix develop`:

```console
lake build
cmake -S . -B build -G Ninja && ninja -C build
prototypes/lemma-reuse/check.sh build/ir-lean
```

That proves the three goals from an empty store, and again from what that saved, and compares what was saved with
the store here. The longer limits, each in a store of its own:

```console
prototypes/lemma-reuse/lemmas.py prove popcountdi2_same --store build/lemma-reuse/long --baseline 600 --alive 600000
prototypes/lemma-reuse/lemmas.py prove popcountti2_same --store build/lemma-reuse/long --baseline 1800 \
  --alive 1800000
```

## What would come next

- **The next llama.cpp rewrite.** The q4_K store is two cores and the facts they need. A rewrite of another kernel
  with the same shape, such as the other quantizations' `maddubs` and `madd`, would show how many of its lemmas are
  already there.
- **Another kind of code,** such as parity, which counts set bits modulo 2, to see how much of this carries over.
- **Lemmas for every width,** for the steps that differ only in width, proved by induction from the `bv_decide`
  instances.
- **Lemmas from an agent.** [Verify](verify.md) already checks a claim from a script or an agent and answers in JSON.
  A lemma an agent proposes could be checked, generalized and saved the same way.
- **Real search.** Rewrites `superopt.py --bench` shows are faster, on code real programs call, where the store
  would have to grow past one family.
