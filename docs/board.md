# The results board

Every proved win on [the kernel corpus](kernels.md), labeled by tier, with its measured speedup, and what
doesn't count and why. It's S8 in the [roadmap](roadmap.md), the headline of decision 6 after #103.

This page is generated: `nix develop -c bench/kernels/board.py write` writes it from the records in
[`bench/kernels/board/`](../bench/kernels/board) and the harness's controls in
[`bench/kernels/results/controls/`](../bench/kernels/results/controls), and the `board` test fails if it isn't
what that gives. Don't edit it by hand.

**0 wins from 0 projects,** against S3's bar of 10 from 3.
The corpus is approved, not fixed, so no win can count yet: decision 7 waits for libsodium's bulk-encryption driver, and then the manifest's `[lock]`.

## Wins

A win is one rewrite, proved, reviewed and measurably faster on a workload of its project, found on the
fixed corpus after its lock: [what a win is](kernels.md#what-a-win-is). Each carries four labels, and every
combination counts toward the bar.

None yet.

## Not counting

Proved rewrites on the corpus's projects that don't count toward the bar, each with why.

| Project | Functions | Proved | Rests on | Source IR | Found by | Proof | Measured | Why it doesn't count |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| [llama.cpp](llama.md) | `ggml_gemm_q4_K_8x8_q8_K`, `ggml_gemv_q4_K_8x8_q8_K` | slice | standard and bv_decide | as built | by hand | [`Vnni.lean`](../tests/llama/Vnni.lean) | 10 rounds on 8 threads, against the pinned clang -O3, in 2026-11-07's runs: medians 1.055 to 1.072 for reading a prompt and for perplexity, and 0.999 to 1.000 for generating, with no pairs or interval | Decision 2 of the kernel corpus: it was chosen and found by hand before the corpus existed, and was measured in rounds, without pairs or an interval. It counts once the rule search finds it again on the fixed corpus and it's measured by the protocol, labeled as resting on a rule written for its site |
| [llama.cpp](llama-q5.md) | `ggml_vec_dot_q5_0_q8_0` | slice | standard and bv_decide | as built | by hand | [`LlamaBitspread.lean`](../tests/proofs/LlamaBitspread.lean) | 1.049 [1.029, 1.057] in inference time, over 30 pairs in 2 confirmation sessions on one thread, against clang 23.1.5 -O3; on 8 threads, 1.004 [0.979, 1.351] | Decision 2 of the kernel corpus: it was chosen and found by hand before the corpus existed, and was timed against clang 23.1.5, not the pinned 23.1.3. It counts once the rule search finds it again on the fixed corpus and it's measured by the protocol, which needs its matcher's pattern stated as a rule |

## Harness controls

Checks on [the harness](kernels.md#the-harness), not on any rewrite, and never wins: a candidate the same as
the baseline has to come out inconclusive, one known slower slower, and one known faster faster. Each was
worked out again from its sessions when this page was written. A ratio above 1 is the candidate faster.

| Run | Project | Workload and baseline | Control | Baseline against candidate | Verdict | Ratio, median [95% interval] | Sessions, pairs | Load average, each session's median | CPUs |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| [2026-11-10](../bench/kernels/results/controls/2026-11-10/zlib-ng) | zlib-ng | compress, -O3 | a/a | baseline against aa | **inconclusive** | 1.000 [0.999, 1.001] | 2, 40 | 5.1, 2.0 | 8 |
| [2026-11-10](../bench/kernels/results/controls/2026-11-10/zlib-ng) | zlib-ng | compress, -O3 | faster | o0 against baseline | **faster** | 1.290 [1.288, 1.291] | 2, 40 | 3.2, 2.1 | 8 |
| [2026-11-10](../bench/kernels/results/controls/2026-11-10/zlib-ng) | zlib-ng | compress, -O3 | slower | baseline against o0 | **slower** | 0.775 [0.773, 0.775] | 2, 40 | 4.4, 1.7 | 8 |

## How a win gets here

1. The rule search finds a rewrite on the fixed corpus, and Lean proves it, in a module a test checks in CI.
2. [`bench/kernels/harness.py`](../bench/kernels/harness.py) builds the project's baseline and the candidate,
   and checks before timing that they differ only in the rewritten functions, that `llc` on the unchanged IR
   gives the baseline's machine code, and that each workload's output or check is the baseline's.
3. A plan is written down, then its confirmation sessions run, and `harness.py compare` reads them by
   [the rule](kernels.md#measurably-faster), against `-O3`, and against the project's own level where that's
   `-O2`, with every other workload of the project measured.
4. An entry in `bench/kernels/board/` cites the comparisons, the proof and the review, and
   `bench/kernels/board.py check` refuses it unless all of that holds.
