# llama.cpp's q4_K kernels

A rewrite of the IR that `clang -O3` produces for llama.cpp's q4_K matrix kernels, proved in Lean to compute the
same values on every input, which makes real inference faster. For what any theorem here means, read
[trust](trust.md) first.

Facts here were checked on 2026-11-07, with clang 23.1.3 and Lean 4.35.0, against llama.cpp's release
[`b12189`](https://github.com/ggml-org/llama.cpp/tree/b12189) (commit `80d2c0c`), on an AMD Ryzen 9 9950X, on top of
commit `6293d34`. `tests/llama.py`, its proofs, native comparison and mutants, ran again on 2026-11-08, merged with
`main` at `0330cd7`, with its stricter axiom check, and gave the same hashes for everything in the manifest. What needs
models, the measurements and the logits check, didn't.

## What `clang -O3` misses

Most weights in a `Q4_K_M` model, the quantization most GGUF models ship in, are `Q4_K`: 4-bit values in blocks of
256, with a 6-bit scale for each 32. On x86 with AVX2, llama.cpp repacks them, eight rows interleaved, and multiplies
them with [`ggml_gemm_q4_K_8x8_q8_K`](https://github.com/ggml-org/llama.cpp/blob/b12189/ggml/src/ggml-cpu/arch/x86/repack.cpp#L2042)
when it reads a prompt and [`ggml_gemv_q4_K_8x8_q8_K`](https://github.com/ggml-org/llama.cpp/blob/b12189/ggml/src/ggml-cpu/arch/x86/repack.cpp#L1464)
when it generates. With `perf`, on Qwen2.5-1.5B-Instruct `Q4_K_M` with 8 threads, the first was 46% of the time spent
reading 512 tokens, and the second 54% of the time spent generating.

For each block of 32 weights and each row, both compute this, written with AVX2 intrinsics:

```c
iacc = _mm256_add_epi16(iacc, _mm256_maddubs_epi16(weights_0, activations_0));  // eight of these
...
iacc = _mm256_madd_epi16(iacc, scales);
```

`maddubs` multiplies unsigned bytes by signed ones and adds pairs into 16 bits, saturating. `madd` multiplies 16-bit
lanes and adds pairs into 32 bits. On a processor with AVX-512 VNNI, `vpdpbusd` does a `maddubs` and the 16-bit sum in
one instruction, adding four products straight into 32 bits. llama.cpp's `q4_0` and `q8_0` kernels use it, by hand.
These don't, and with `-march=native` on Zen 5 clang doesn't either: it keeps 8 `vpmaddubsw` and 7 `vpaddw` for each
block, at every width, which is 256 and 224 of them in `gemm`. It does use VNNI's 16-bit `vpdpwssd`, for a `madd` and
the add after it, in `gemv`. After the rewrite, each block is 8 `vpdpbusd` and a `vpmulld`.

The two are only the same because of three facts about this code, which LLVM doesn't track through x86 intrinsics:

- The weights are masked to 4 bits, so a `maddubs` sum is at most 2 × 15 × 128 = 3,840, and never saturates.
- Eight of those fit in 16 bits, so the `add` never wraps.
- Each scale is repeated in both 16-bit halves of a 32-bit lane, so `madd` multiplies the sum of the two halves by one
  scale.

So [`tests/llama/vnni.py`](../tests/llama/vnni.py) rewrites clang's IR, at each place it finds this shape:

```llvm
; clang -O3                                             ; rewritten
%p0 = call @llvm.x86.avx2.pmadd.ub.sw(%a0, %b0)         %d0 = call @llvm.x86.avx512.vpdpbusd.256(zeroinitializer, %a0, %b0)
...                                                     ...
%p7 = call @llvm.x86.avx2.pmadd.ub.sw(%a7, %b7)         %d7 = call @llvm.x86.avx512.vpdpbusd.256(%d6, %a7, %b7)
%s  = add <16 x i16> (an add tree over %p0 to %p7)      %c  = bitcast <16 x i16> %scales to <8 x i32>
%r  = call @llvm.x86.avx2.pmadd.wd(%s, %scales)         %r  = mul %d7, ashr (shl %c, 16), 16
```

It keeps the name `%r`, so the rest of the kernel is untouched. That's 34 places: 2 in `gemv`, and 32 in `gemm`, at 256
and 512 bits. No other function's machine code changes.

## What's proved

For each of the 34 places, a theorem that the rewritten IR computes exactly what clang's does, for every input, poison
included:

```lean
theorem s00_same (v90 v92 : Vec 4 64) (v176 v9 : Vec 2 64) (v94 v96 v98 v100 : Vec 4 64) (v179 : Vec 2 64)
    (v102 v104 : Vec 4 64) (v123 v127 v125 : Val 32) :
    S00Tgt.s00_tgt v90 v92 v176 v9 v94 v96 v98 v100 v179 v102 v104 v123 v127 v125 =
      S00Src.s00_src v90 v92 v176 v9 v94 v96 v98 v100 v179 v102 v104 v123 v127 v125
```

`s00_src` and `s00_tgt` are a slice of the kernel, before and after, cut out by
[`tests/llama/slices.py`](../tests/llama/slices.py): everything the rewritten value is a pure function of, back to
loads, phis and arguments. Those become the parameters, so the theorem holds whatever they are. The slices include how
clang computed the operands, the masking with `0x0F0F0F0F` and the shuffles that repeat each scale, so the three facts
above are proved from clang's own instructions, and aren't hypotheses. Every line of a slice is a line of the kernel,
and the script lines the two kernels up as a diff, and checks that every line that differs is in a slice and every other
line is where it was: 32 removed and 24 added in `gemv`, and 512 removed and 384 added in `gemm`. Which lines each has
isn't enough, since a store moved into another block keeps every line and changes what the kernel does. `tests/llama.py`
moves one, and edits a comparison outside every slice, and the script has to refuse both.

[`Vnni.lean`](../tests/llama/Vnni.lean) has the proof, which is the same for every place: an invariant that holds after
each `maddubs` and `vpdpbusd` pair, that each 16-bit sum is the exact integer sum and at most 3,840 in size for each
`maddubs` in it, and that the 32-bit accumulator is the total of the two 16-bit sums under it. After eight, nothing has
saturated or wrapped, and `madd` with paired scales is the multiply. The facts about operands go through shuffles and
bitcasts with lemmas about each lane, so the 512-bit kernels need nothing more. Each theorem rests on the standard three
axioms and five from `bv_decide`, which the project's [axiom check](../tests/check_axioms.lean) works out again, reading
the theorem and what it imports as data. It also checks the theorem is about both slices, as `ir-lean` generated them,
and `leanchecker` replays it through the kernel.

A wrong rewrite can't pass this way. `vnni.py --mutant` makes three: reading the weights as signed instead of the
activations, leaving out the last `vpdpbusd`, and multiplying by the whole 32-bit lane of scales. For each, at every one
of the 34 places, Lean proves the rewritten slice gives a different result from clang's on one input, with
`decide +kernel`, which has the kernel work both out and adds no axiom. So the theorem that they're the same is false
at every place, and `tests/llama.py` doesn't try it. Before these proofs, it did, and each ran out of heartbeats, which
refutes nothing. And `tests/llama.py` changes clang's mask from `0x0F` to `0x1F` in each byte, which
breaks the first fact: every theorem stops on it with an error of its own, though the input Lean tries doesn't tell the
two apart.

To translate the kernels, the model learned four things, in [`X86.lean`](../IRLean/X86.lean) and
[`Vec.lean`](../IRLean/Vec.lean): `bitcast` between integer vectors, which LangRef defines, and PMADDUBSW, PMADDWD and
VPDPBUSD, from Intel's pseudo-code, which it doesn't. [`x86.ll`](../tests/real/x86.ll) runs each against the
processor: 22 functions at all three widths, 400 inputs each, with the saturating and wrapping extremes, and all 8,800
results agree. That needs AVX-512 VNNI and can't see poison, so [`x86check.py`](../tests/x86check.py) also checks the
bitcasts, PMADDUBSW and PMADDWD on any processor, against Alive2 both ways and LLVM's constant folder, poison included:
29 operations, every shape the kernels use and more, on 473 inputs, all exact. Neither knows VPDPBUSD.

## Checked another way

None of these depend on the Lean model.

- **Natively.** [`native_check.py`](../tests/llama/native_check.py) runs each pair of slices on the processor against
  each other, on 200,000 inputs each, a quarter of them from bytes at the extremes. None of the 34 differ.
- **Wrong rewrites.** On 20,000 inputs, the native run catches each of the three wrong rewrites and the mask change
  above.
- **Whole programs.** `llama-perplexity`, with the two libraries, gives the same logits bit for bit, on both models in
  the table below, for 16 chunks of 512 tokens of WikiText-2. Before the reproducer existed, a run of 60 chunks on the
  first model did too: 4.6 GB of logits each, and a perplexity of 10.0878 both times.
- **Alive2** doesn't know VPDPBUSD. With each call replaced by its definition in plain IR, by a one-off script that
  isn't in the repo, it timed out after 10 minutes on the first slice of `gemv`, so it gives no verdict here.

## Measured

`tests/llama_bench.py` builds the pinned llama.cpp with its own CMake, as its README says: Release, and `GGML_NATIVE`
on, its default. From that build's compile command it takes the kernels' IR, checks that `llc -O3` gives the machine
code the build has, and that the functions are the ones the theorems are about. Then it links a second
`libggml-cpu.so` from the rewritten IR with the build's own link command. Both variants run the same binaries, with only
that library swapped through `LD_LIBRARY_PATH`. Each round runs each workload with each, alternating which goes first,
pinned to one CCD of the processor with 8 threads.

10 rounds with 8 threads on CPUs 8 to 15, on 2026-11-07, with a load average of 7 to 10.7 from other work on the
machine. `pp512` is `llama-bench` reading a 512-token prompt, and `tg128` generating 128 tokens, each the average of its
3 repetitions in that round. Perplexity is `llama-perplexity` on 24 chunks of 512 tokens of WikiText-2's test set,
timed from start to exit, model loading included. The speedup is the rewritten library's over clang's, in each round:

| Model | Workload | `clang -O3`, median | Rewritten, median | Speedup, median | Least and most | Rounds faster |
| --- | --- | --- | --- | --- | --- | --- |
| Qwen2.5-1.5B-Instruct `Q4_K_M` | `pp512` | 1,117 tokens/s | 1,189 tokens/s | 1.064 | 1.059 to 1.069 | 10 of 10 |
| | Perplexity | 13.52 s | 12.82 s | 1.055 | 1.051 to 1.060 | 10 of 10 |
| | `tg128` | 53.97 tokens/s | 53.96 tokens/s | 1.000 | 0.997 to 1.016 | 6 of 10 |
| Llama-3.2-3B-Instruct `Q4_K_M` | `pp512` | 574 tokens/s | 614 tokens/s | 1.072 | 1.061 to 1.082 | 10 of 10 |
| | Perplexity | 24.43 s | 22.95 s | 1.064 | 1.062 to 1.075 | 10 of 10 |
| | `tg128` | 26.74 tokens/s | 26.74 tokens/s | 0.999 | 0.995 to 1.002 | 3 of 10 |

Perplexity was 10.3476 and 11.1036 in every run of each variant. `perf stat` counts fewer cycles too, by the same
amount: a median of 4.86 × 10¹¹ against 5.14 × 10¹¹ for the first model's perplexity run, and 8.85 × 10¹¹ against 9.43 ×
10¹¹ for the second's.

So reading a prompt, or a document as perplexity does, is 5.5% to 7.2% faster, in every round. Generating isn't faster
with 8 threads, where it waits on memory: the rewrite takes out instructions, and that doesn't help a kernel that isn't
waiting on them.

Then 6 rounds with 1 thread on CPU 12, the same day, with a load average of 1 to 4.6, for the kernels alone, since a
single thread has no other threads to wait on:

| Model | Workload | `clang -O3`, median | Rewritten, median | Speedup, median | Least and most | Rounds faster |
| --- | --- | --- | --- | --- | --- | --- |
| Qwen2.5-1.5B-Instruct `Q4_K_M` | `pp512` | 172.3 tokens/s | 182.3 tokens/s | 1.058 | 1.054 to 1.061 | 6 of 6 |
| | `tg128` | 24.53 tokens/s | 24.63 tokens/s | 1.002 | 0.976 to 1.006 | 4 of 6 |
| Llama-3.2-3B-Instruct `Q4_K_M` | `pp512` | 82.4 tokens/s | 87.8 tokens/s | 1.067 | 1.062 to 1.071 | 6 of 6 |
| | `tg128` | 11.47 tokens/s | 12.63 tokens/s | 1.104 | 1.059 to 1.152 | 6 of 6 |

On one core, generating with the second model is faster too, in every round. Clang's library gave 11.41 to 11.48
tokens/s each time, while the rewritten one gave either about 12.2 or about 13.1, three rounds each, which isn't
explained. The first model's generation isn't faster even on one core. With 8 threads, `perf` put 31% of its generating
in the `Q6_K` tensors that `Q4_K_M` keeps, which this doesn't touch. The second model wasn't profiled, so why they
differ isn't known.

The raw rows are in [`llama-8-threads.csv`](data/llama-8-threads.csv) and
[`llama-1-thread.csv`](data/llama-1-thread.csv), and each run's whole output, with its build checks, model hashes and
logits check, in [`llama-8-threads.log`](data/llama-8-threads.log) and [`llama-1-thread.log`](data/llama-1-thread.log).
The single-thread run skipped the logits check, which the 8-thread run had just done. Its summary lines are in an
earlier format of `--summary`, with the same numbers.

Earlier runs on this machine, under a load average of 10 to 16 from other sessions, varied far more, up to a factor of 7
in generation, and a run of the prompt workload came out at 1.002. They were stopped and replaced by the reproducer, and
aren't in the table.

## Reproducing it

```console
nix develop .#llama
lake build
cmake -S . -B build -G Ninja && ninja -C build
tests/llama.py build/ir-lean --manifest build/llama-manifest.json
```

`nix develop .#llama` is the default shell with llama.cpp's source, which the flake fetches by hash. The default shell
leaves it out, as it's 185 MB that no binary cache has, and in it `ctest` skips the `llama` test. In CI, it's the
`llama` test job, in `nix develop .#llama`. That compiles the kernels from the pinned release, rewrites them, checks the 34
theorems, runs the native comparison if the processor has AVX-512 VNNI, and checks the four mutants. It needs no
model, and takes under 3 minutes with 6 Lean jobs, or about 3 and a half with 4 and no native comparison.

The manifest has the hashes of the source, IR and rewritten object, each theorem's statement and axioms, and what each
mutant did. [`llama-manifest.json`](data/llama-manifest.json) is the one behind this page. Three runs on this machine,
two of them hours apart and the third a day later on the merged tree, gave the same hashes for everything in it: the
source, IR, rewritten IR and object, all 68 slices, and every generated Lean file. Another machine with the same flake
should too: on an Apple M4 Max, [lemma reuse](lemma-reuse.md) got the same IR and all 68 slices, and the rest hasn't
been tried. On a processor without AVX-512 VNNI, the native comparison is skipped, and Lean's proofs that each wrong
rewrite differs from clang's are what refute them, as in CI. `--no-native` does the same on any processor.

The measurement needs models and text, which aren't in the repo, and runs in `nix develop .#llama` too:

| File | Where | SHA-256 |
| --- | --- | --- |
| `qwen2.5-1.5b-instruct-q4_k_m.gguf` | [Qwen/Qwen2.5-1.5B-Instruct-GGUF](https://huggingface.co/Qwen/Qwen2.5-1.5B-Instruct-GGUF) | `6a1a2eb6d15622bf3c96857206351ba97e1af16c30d7a74ee38970e434e9407e` |
| `Llama-3.2-3B-Instruct-Q4_K_M.gguf` | [bartowski/Llama-3.2-3B-Instruct-GGUF](https://huggingface.co/bartowski/Llama-3.2-3B-Instruct-GGUF) | `6c1a2b41161032677be168d354123594c0e6e67d2b9227c84f296ad037c728ff` |
| `wikitext-2-raw-v1.zip`, for `wiki.test.raw` | [ggml-org/ci](https://huggingface.co/datasets/ggml-org/ci/resolve/main/wikitext-2-raw-v1.zip), as llama.cpp's `scripts/get-wikitext-2.sh` fetches it | `ef7edb566e3e2b2d31b29c1fdb0c89a4cc683597484c3dc2517919c615435a11` |

```console
tests/llama_bench.py qwen2.5-1.5b-instruct-q4_k_m.gguf Llama-3.2-3B-Instruct-Q4_K_M.gguf \
  --text wikitext-2-raw/wiki.test.raw --rounds 10 --cpus 8-15 --threads 8 --csv bench.csv
tests/llama_bench.py --summary bench.csv
```

## What it assumes

Everything in [trust](trust.md) applies: these are theorems about LLVM IR in this project's model. They aren't about the
C++ source or the machine code. On top of that:

- **From the slices to the kernel is an argument, not a theorem.** Each theorem is about a slice, and the kernel uses
  floating point, which the model doesn't have, so there's no theorem about the whole kernel. A script checks that each
  slice is the kernel's own lines, that every changed line is in a slice and every other line is where it was, and that
  the rewritten value keeps its name.
  The instructions the rewrite adds or takes out are `vpdpbusd`, `pmaddubsw`, `pmaddwd`, `add`, `mul`, `shl`, `ashr`
  and `bitcast`, which don't touch memory and aren't undefined on any input. Replacing such a value with an equal one
  doesn't change a program, but no proof says that here.
- **x86's intrinsics are as Intel describes them**, and as `X86.lean` writes them. The processor agrees on every input
  tried, and so do Alive2 and LLVM's constant folder for PMADDUBSW and PMADDWD, which isn't a proof. Only the processor
  checks VPDPBUSD, and LLVM's own reading of it, in `createVPDPBUSD`, is the same sum.
- **Poison in a target intrinsic is per lane.** LangRef doesn't say. LLVM's constant folds of PMADDWD and PMADDUBSW,
  and Alive2, are per lane too. If poison in any lane made the whole result poison instead, the rewrite would still
  refine clang's IR: clang's result is all poison whenever any operand lane is, while the rewrite's only loses the lanes
  whose scale is poison. That argument isn't checked. And these operands come from loads of quantized weights and
  activations, which are initialized.
- **The proofs compile for `-march=znver5`.** On the machine measured, `-march=native` gives the same function bodies,
  and only spells the target features differently. `tests/llama_bench.py` checks that for the build it measures.
- **The rewritten code needs AVX-512 VNNI with AVX-512VL**, which Zen 4 and Zen 5, and Intel's server processors since
  Cascade Lake, have.
  It's a rewrite for a build that targets those, as `-march=native` does on them, and isn't for other processors.
- **Stock clang.** The dev shell's compiler wrapper adds hardening and frame pointers, and drops `-march=native`, and
  Nix sets `SOURCE_DATE_EPOCH`, which turns `GGML_NATIVE` off. Both scripts undo all of that, so the build is what clang
  does by default. OpenMP isn't in the shell, so llama.cpp uses its own thread pool, the same way for both variants.
- **One machine, shared.** Other sessions were running on it, a single-threaded process sat on one core of the other
  CCD for hours, and timings vary with that. The rounds alternate, and the table gives every round's spread.

## What's next

- `ggml_vec_dot_q6_K_q8_K` was 31% of generating with this model, for the `Q6_K` tensors `Q4_K_M` keeps, and isn't
  rewritten.
- Generating is limited by memory at 8 threads, so this rewrite doesn't change it there. On one core it's faster for
  one model, and the two speeds the rewritten library settles at aren't explained.
- The same rewrite could go into llama.cpp's source, or into LLVM as a combine on x86 intrinsics, if it knew the
  range of each lane.
