# The kernel corpus

The fixed list of real projects the superoptimizer is judged on. It serves decisions 6, 7 and 8 of the thirteen
decisions of 2026-11-09, after #103, in the [roadmap](roadmap.md): the headline is proved speedup over `clang -O3`, in
wall time on a real workload, on a corpus fixed before the search runs, and the bar is at least 10 proved wins from at
least 3 projects.

**Approved on 2026-11-10.** The maintainer approved the proposal as it recommended: the six projects, llama.cpp,
zlib-ng, xxHash, libsodium, FLAC and libwebp, and all seven [decisions](#what-the-maintainer-decided-on-2026-11-10),
which the roadmap records in [the kernel corpus, decided on 2026-11-10](roadmap.md#the-kernel-corpus-decided-on-2026-11-10).
[`bench/kernels/manifest.toml`](../bench/kernels/manifest.toml) says `state = "approved"`, and names the six. It isn't
fixed yet: decision 7 asks for libsodium's bulk-encryption driver to be written first, and then the manifest's `[lock]`
fixes the list ([how](#the-manifest)). No search or candidate rewrite has been run on any of these projects.

Until then this page was the proposal, and it reads as one where it gives the case for each choice.

**Two things are called a corpus.** [The corpus](corpus.md) is pairs of IR that `tools/corpus/capture.py` takes from
`opt`. This is the *kernel corpus*: projects, their hot kernels and their workloads. It lives in `bench/kernels/`, and
neither renames the other.

Facts here were measured on 2026-11-10, on z, an AMD Ryzen 9 9950X, at commit `df3e997`, with clang 23.1.3, unless
they say otherwise. [What the emitter does with them](#what-the-emitter-does-with-them-today) was measured again
after #105 and #107. Each has its source or the command that reproduces it.

## What the maintainer decided on 2026-11-10

Each decision had a recommendation, and on 2026-11-10 the maintainer took every one as it stood. The table is the
proposal's, kept as the record, with the alternatives that weren't taken. Its counts are the proposal's, at `df3e997`:
after #105 and #107, decision 1's 16 of the six's 64 named kernels are 22, the 14 intrinsics libwebp's SIMD needed are
all modeled, and decision 4's 24 and 241 of 798 functions are 31 and 279
([below](#what-the-emitter-does-with-them-today)).

| # | Decision | Recommended, and decided on 2026-11-10 | The alternative, not taken, and what it would have cost |
| --- | --- | --- | --- |
| 1 | Which projects | Six: **llama.cpp, zlib-ng, xxHash, libsodium, FLAC and libwebp**, one or two from each of the five domains. In all but llama.cpp, a kernel the profile calls hot translates today: 16 of the six's 64 named kernels do, in the [relaxed run](#what-the-emitter-does-with-them-today) | Add zstd, the first alternate: its hot kernels are match finders and entropy coders with little SIMD, which is why it isn't in the six, and three of them translate today. Or drop libwebp: its lossy decoder is 78% scalar, and its SIMD needs 14 intrinsics the model lacks. Fewer than five projects leaves a domain out |
| 2 | Whether the two llama.cpp rewrites on `main` count toward the ten | **No, as they stand.** Each counts once the rule search finds it again on the fixed corpus and it's measured again by [the protocol](#the-benchmark-protocol), labeled as resting on a rule written for its site | Count both now: the bar becomes 8 wins from the engine, on results chosen before the corpus existed. [Arguments each way](#the-two-llamacpp-rewrites) |
| 3 | What the baseline is | The project's own flags, with the pinned clang, at `-O3`. Where the project builds at `-O2`, as zlib-ng does, a win has to beat that build too | `-O3` alone: simpler, and a reader can say the project's own build was never beaten |
| 4 | Whether a win proved on IR compiled with `-fno-strict-aliasing` counts | **Yes, labeled**, and measured against the baseline of decision 3, which keeps strict aliasing. The emitter refuses `!tbaa`, so as built it translates 24 of the 798 functions in the units named, and relaxed 241 | Only as-built IR: every whole-function win then waits for `!tbaa` in the model, outside libsodium, which builds with the flag itself. Slice wins are unaffected: a slice has no loads |
| 5 | What "measurably faster" means | The [rule below](#measurably-faster): at least 30 randomized pairs in at least 2 confirmation sessions, the pooled 95% interval of the median paired speedup at or above 1.005, every session's median above 1, and no other workload of the project slower | A looser rule, such as the interval above 1.000, counts wins of a tenth of a percent, which z's noise can produce |
| 6 | The names | "The kernel corpus", `docs/kernels.md`, `bench/kernels/` | Any other name that isn't "corpus" alone |
| 7 | libsodium's workload | Its Argon2id test in benchmark mode, which is its own and 99% kernel time. Bulk encryption needs a driver of ours, about 30 lines over its documented `crypto_secretstream` example, written before the list is fixed | Argon2id only: ChaCha20-Poly1305 and BLAKE2b then have no workload a win could be measured on |

Decisions 3 to 5 are rules the board is read by, which is why they were settled with the list.

## The criteria

Set before any project was measured, so the list isn't chosen after the fact. The first six are the brief's, of
2026-11-09. The last two, and the threshold for hot, were added before the first profile was taken. A project that
fails one is rejected, and the manifest says which.

1. **Real users.** Someone else ships, vendors or wraps it, shown by a source checked on the day.
2. **A hot kernel the pinned clang compiles.** The functions its workload spends time in are C or C++ in its default
   build for x86-64 Linux, so clang 23.1.3 gives IR for them. Hand-written assembly is out of reach.
3. **SIMD in a hot kernel,** through intrinsics or the vectorizer: vector types in the IR of a hot function.
4. **A real workload, and a benchmark of the project's own,** that runs on z with no GPU and no new hardware, on
   inputs pinned by hash.
5. **A license that allows it:** one that lets this repo commit IR generated from the source and publish a rewrite of
   it. `bench/kernels/kernels.py` lists them: Apache-2.0, BSD-2-Clause, BSD-3-Clause, CC0-1.0, ISC, MIT and Zlib.
6. **Within reach of the model soon:** a hot kernel translates today, or what stops it is on a lane's list.
7. **Pinned and reproducible:** a release tag, or a commit where there are none, with its Nix hash, fetched through
   Nix and built with the dev shell alone.
8. **Distinct:** it doesn't share its hot kernels with a project already listed, so one win isn't counted twice.

**Hot** means at least 1.5% of the cycles a workload spends in user code, by `perf record -e cycles:u` on z. A kernel
is a function the profile names, as the linker sees it.

## The candidates

Fifteen, across the five domains. The six recommended are the six the maintainer approved on 2026-11-10. Each was
fetched with `nix flake prefetch github:OWNER/REPO/REV` on 2026-11-09, at the latest release tag `git ls-remote --tags`
showed that day. llama.cpp stays at `b12189`, the release both rewrites on `main` are about. The manifest has each Nix
hash.

| Project | Domain | What it is | Who uses it | License | Pin | Commit | Proposal |
| --- | --- | --- | --- | --- | --- | --- | --- |
| [llama.cpp](https://github.com/ggml-org/llama.cpp) | Inference | LLM inference, with ggml's quantized kernels | Ollama pins and builds it | MIT | `b12189` | `80d2c0c2c56e4a1bbf74be98f64b99927bf230bc` | **Recommended** |
| [XNNPACK](https://github.com/google/XNNPACK) | Inference | Neural-network operators, as generated microkernels | TensorFlow Lite, PyTorch Mobile, ONNX Runtime Mobile and MediaPipe, by its README, and Chromium | BSD-3-Clause | No tags: its default branch on 2026-11-09 | `8a7926edb1b57eb12abcefd81f653f818db80585` | Alternate |
| [zlib-ng](https://github.com/zlib-ng/zlib-ng) | Compression | zlib rewritten for modern processors | Fedora's system zlib since Fedora 40 | Zlib | `2.3.3` | `12731092979c6d07f42da27da673a9f6c7b13586` | **Recommended** |
| [zstd](https://github.com/facebook/zstd) | Compression | Zstandard | The Linux kernel and Chromium vendor it | BSD-3-Clause, or GPL-2.0 | `v1.5.7` | `f8745da6ff1ad1e7bab384bd1f9d742439278e99` | Alternate, the first to add |
| [libdeflate](https://github.com/ebiggers/libdeflate) | Compression | Whole-buffer DEFLATE | htslib recommends it | MIT | `v1.26` | `92e6a0db9fa848d742f9eb286c92afc60f2c3dda` | Alternate |
| [lz4](https://github.com/lz4/lz4) | Compression | A very fast LZ77 | The Linux kernel vendors it | BSD-2-Clause | `v1.11.0` | `c72c7c0ec132ad2ce2fe9fad7b0c728d9faee2fc` | Rejected: 3 |
| [FLAC](https://github.com/xiph/flac) | Codecs | The reference FLAC encoder and decoder | It's what distributions ship as `flac` and `libFLAC` | BSD-3-Clause | `1.5.0` | `1507800de4b70e21be71f38caa0d9079d0bc6e45` | **Recommended** |
| [libwebp](https://github.com/webmproject/libwebp) | Codecs | The reference WebP encoder and decoder | Chromium vendors it | BSD-3-Clause | `v1.6.0` | `4fa21912338357f89e4fd51cf2368325b59e9bd9` | **Recommended** |
| [Opus](https://github.com/xiph/opus) | Codecs | The reference Opus audio codec | Chromium vendors it, for WebRTC | BSD-3-Clause | `v1.6.1` | `22244de5a79bd1d6d623c32e72bf1954b56235be` | Alternate |
| [dav1d](https://github.com/videolan/dav1d) | Codecs | An AV1 decoder | Chromium vendors it | BSD-2-Clause | `1.5.4` | `54706fc6bc0cdecab7e9593974a4039cc038fca7` | Rejected: 2 |
| [base64](https://github.com/aklomp/base64) | Codecs | Base64 with SIMD codecs | None confirmed | BSD-2-Clause | `v0.5.3` | `5d5074cb856b9a53fe64f04ddf47812a85f4fb5a` | Rejected: 1, 2 |
| [xxHash](https://github.com/Cyan4973/xxHash) | Hashing | XXH3, XXH32 and XXH64 | The Linux kernel and zstd vendor it | BSD-2-Clause | `v0.8.4` | `c87183a77d67f7d37e3d2d1b7eaac5e7c695e4f0` | **Recommended** |
| [BLAKE3](https://github.com/BLAKE3-team/BLAKE3) | Hashing | The BLAKE3 hash, in C | LLVM vendors it, with the assembly | CC0-1.0, or Apache-2.0 | `1.8.7` | `f3149ec5bb5449af877ba20377a11008ff499fa2` | Rejected: 2 |
| [libsodium](https://github.com/jedisct1/libsodium) | Crypto | Encryption, hashing, password hashing, signatures | PHP's sodium extension wraps it | ISC | `1.0.22-RELEASE` | `77e1ce5d6dee871c49ef211222ba18ef0c486bda` | **Recommended** |
| [OpenSSL](https://github.com/openssl/openssl) | Crypto | TLS and general cryptography | Most TLS on Linux servers | Apache-2.0 | `openssl-4.1.0` | `2f4e3a5fec05394068cfa7379890ab552483a8a6` | Rejected: 2 |

Where each claim of use comes from, all read on 2026-11-10:

- **Vendored:** `lib/zstd/`, `lib/xxhash.c` and `lib/lz4/` in [Linux](https://github.com/torvalds/linux), and
  `third_party/zstd`, `libwebp`, `opus`, `dav1d` and `xnnpack` in [Chromium](https://github.com/chromium/chromium),
  each fetched from its default branch. zstd's own `lib/common/xxhash.h`, and LLVM's `llvm/lib/Support/BLAKE3`, at
  the pins.
- **Stated:** [Fedora's change page](https://fedoraproject.org/wiki/Changes/ZlibNGTransition) for zlib-ng in Fedora
  Linux 40. Ollama's [`llama/README.md`](https://github.com/ollama/ollama/blob/main/llama/README.md):
  "`LLAMA_CPP_VERSION` pins Ollama's llama.cpp source". htslib's
  [`INSTALL`](https://github.com/samtools/htslib/blob/develop/INSTALL): "libdeflate (optional, but strongly
  recommended for faster gzip)". PHP's [`ext/sodium`](https://github.com/php/php-src/tree/master/ext/sodium).
  XNNPACK's and FLAC's own READMEs, at the pins.
- **Not confirmed:** base64. Node.js is said to vendor it, and `deps/base64` isn't on Node's `main` branch.

The licenses are each project's `LICENSE` or `COPYING` at the pin. FLAC's and xxHash's libraries are BSD, and their
command-line tools, which a workload only runs, are GPL-2.0-or-later.

### Why five are rejected

| Project | Fails | Why | How it's known |
| --- | --- | --- | --- |
| dav1d | 2 | Its kernels on x86-64 are hand-written assembly | `cat src/x86/*.asm \| wc -l` gives 160,805 lines, against 30,546 in `src/*.c` |
| OpenSSL | 2 | Its kernels on x86-64 are generated assembly | 31 `crypto/*/asm/*-x86_64.pl` generators, for AES, GHASH, ChaCha20, Poly1305, SHA and the bignum code |
| BLAKE3 | 2 | Its default build on x86-64 is assembly | `c/CMakeLists.txt`, lines 106 and 107, sets `BLAKE3_SIMD_TYPE` to `amd64-asm`, and its configure compiles the three `.S` files. Its intrinsics build is an option nobody's default takes: [its demand](#what-the-emitter-does-with-them-today) is measured in case that changes |
| lz4 | 3 | No SIMD | `grep -c '_mm_\|_mm256_' lib/*.c` gives 0 for every file |
| base64 | 1, 2 | No user confirmed, and its AVX2 encoder is inline assembly under GCC and clang | `lib/arch/avx2/codec.c`, lines 15 to 19, and the emitter refuses that function for `inline assembly` |

Three more were set aside without being fetched, each for a reason that needs no measurement. whisper.cpp shares
ggml's kernels with llama.cpp, which is criterion 8. libjpeg-turbo's SIMD is assembly, as dav1d's is. ONNX Runtime's
hot kernels on x86-64 are assembly too. These three are from what's known of the projects, not from a check on the day.

## Where the time goes

Each project was built its own way, with its CMake or its configure script, in a Release build, with the dev
shell's clang and none of its wrapper's hardening, and run under `perf record -e cycles:u`:

```console
nix develop -c bench/kernels/kernels.py inputs build/kernels/inputs
nix develop -c bench/kernels/profile.sh zlib-ng build/kernels/inputs
```

The first fetches the inputs the manifest pins, through Nix, each checked against its SHA-256, and makes `silesia.tar`
from the Silesia corpus's zip, the same bytes every time: SHA-256 `0b5ec70c8048321525f820bc1d76429840bd22ee2c7a116175253a0fec2c724d`.
It leaves out llama.cpp's model, over a gigabyte, unless asked for by name. Shares are of the cycles spent
in user code, on z on 2026-11-10, in one run each, with other lanes' work on the machine. A share says where the time
is. It isn't a timing.

| Project | Workload | Functions at 1.5% or more, with their share |
| --- | --- | --- |
| zlib-ng | `minigzip -6` on `silesia.tar` | `longest_match_avx512` 54.1, `deflate_medium` 18.0, `compress_block` 8.0, `quick_insert_string` 7.8, `insert_string` 7.4, `build_tree` 3.4 |
| | `minigzip -d` | `inflate_fast_avx512` 90.2, `zng_inflate_table` 3.4, `chunkmemset_avx512` 2.1, `crc32_fold_vpclmulqdq` 2.0 |
| xxHash | `xxhsum -b -i5` | `XXH64` 25.6, `XXH32` 25.4, `XXHL64_default_avx512` 24.5, `XXHL128_default_avx512` 24.4 |
| | `xxhsum -H3 silesia.tar`, ten times | `XXH3_update_avx512` 93.4 |
| libsodium | `pwhash_argon2id` | `fill_block_with_xor` 62.9, `argon2_fill_segment_avx512f` 36.2 |
| | `aead_chacha20poly1305` | `chacha20_encrypt_bytes` 42.2, `poly1305_blocks` 11.1, `crypto_onetimeauth_poly1305_sse2_update` 9.3, `poly1305_finish_ext` 6.7 |
| | `generichash` | `sodium_hex2bin` 53.7, `blake2b_compress_avx2` 37.1 |
| | `aead_aes256gcm` | `chacha20_encrypt_bytes` 31.0, from its random bytes, `crypto_aead_aes256gcm_beforenm` 14.1, `gh_ad_blocks` 11.2 |
| FLAC | `flac -8` on the Sintel master | `FLAC__lpc_compute_autocorrelation_intrin_fma_lag_16` 22.2, `FLAC__lpc_compute_residual_from_qlp_coefficients_16_intrin_avx2` 15.4, `FLAC__MD5Transform` 13.4, `find_best_partition_order_` 10.2, `FLAC__bitwriter_write_rice_signed_block` 8.1, `FLAC__lpc_compute_residual_from_qlp_coefficients_intrin_avx2` 5.1, `FLAC__fixed_compute_best_predictor_wide_intrin_avx2` 4.4, `FLAC__precompute_partition_info_sums_intrin_avx2` 4.1 |
| | `flac -5` | `FLAC__MD5Transform` 31.8, `FLAC__bitwriter_write_rice_signed_block` 16.9, `FLAC__fixed_compute_best_predictor_wide_intrin_avx2` 9.4, `FLAC__lpc_compute_autocorrelation_intrin_fma_lag_12` 9.4 |
| | `flac -d` | `FLAC__MD5Transform` 34.6, `FLAC__lpc_restore_signal` 27.2, `FLAC__bitreader_read_rice_signed_block_bmi2` 23.4, `read_frame_` 7.3, `FLAC__crc16_update_words64` 4.1 |
| libwebp | `dwebp`, five lossy images | `GetCoeffsFast` 54.2, `GetLargeValue` 13.9, `VP8ParseIntraModeRow` 9.7, `Transform_SSE2` 3.5, `VP8YuvToRgb32_SSE41` 3.2 |
| | `dwebp`, five lossless images | `DecodeImageData` 62.5, `PredictorAdd13_SSE2` 5.8, `BuildHuffmanTable` 5.2, `VP8LDoFillBitWindow` 3.5, `TransformColorInverse_AVX2` 2.3, `PredictorAdd12_AVX2` 2.2 |
| | `cwebp -lossless` | `CombinedShannonEntropy_AVX2` 37.3, `GetCombinedEntropyUnrefined_C` 14.0, `VP8LResidualImage` 6.6, `CollectColorBlueTransforms_AVX2` 6.5 |
| | `cwebp -q 75` | `VP8LHashChainFill` 11.3, `VP8LGetBackwardReferences` 7.7, `GetCombinedEntropyUnrefined_C` 7.6, `VP8LResidualImage` 7.5, `VectorMismatch_AVX2` 4.6, `QuantizeBlock_SSE41` 4.3, `FTransform_SSE2` 4.0, `ITransform_SSE2` 3.4, `SSE4x4_SSE2` 3.0 |
| zstd | `zstd -b3 -i5` on `silesia.tar` | `ZSTD_compressBlock_doubleFast` 58.1, `ZSTD_decompressSequences_bmi2` 17.0, `ZSTD_encodeSequences_bmi2` 7.1, `HIST_count_parallel_wksp` 2.4 |
| | `zstd -b19 -i5` | `ZSTD_btGetAllMatches_noDict_3` 51.0, `ZSTD_compressBlock_opt2` 24.0, `ZSTD_insertBt1` 15.6, `ZSTD_decompressSequences_bmi2` 7.0 |
| libdeflate | `benchmark -6` on `silesia.tar` | `deflate_compress_lazy` 83.0, `deflate_decompress_bmi2` 10.0, `deflate_flush_block` 5.9 |
| Opus | `opus_demo -e audio`, 96 kb/s | `exp_rotation` 10.7, `op_pvq_search_sse2` 10.1, `transient_analysis` 6.5, `run_analysis` 5.9, `opus_fft_impl` 5.8, and 16 more under 5 |
| | `opus_demo -d` | `decode_pulses` 18.0, `opus_fft_impl` 13.4, `exp_rotation` 10.1, `quant_partition` 9.3, `clt_mdct_backward_c` 5.8 |

Three weren't profiled here:

- **llama.cpp,** whose profiles are on `main`: `ggml_gemm_q4_K_8x8_q8_K` is 46% of reading a prompt and
  `ggml_gemv_q4_K_8x8_q8_K` 54% of generating, with `ggml_vec_dot_q6_K_q8_K` at 31% ([llama.cpp](llama.md)), and
  `ggml_vec_dot_q5_0_q8_0` is 45% of one thread's generating on another model ([llama.cpp's Q5](llama-q5.md)).
- **XNNPACK,** whose build downloads its dependencies while it configures, `cmake/Download*.cmake`, which Nix would
  have to pin. Its kernels
  here are four of the 15 its CMake lists as production AVX-512 VNNI microkernels,
  `cmake/gen/avx512vnni_microkernels.cmake`, which `src/configs/gemm-config.c` picks on a processor with AVX-512 VNNI.
  That they're hot is the project's claim, not a measurement.
- **The rejected projects.**

What the profiles say that the list doesn't:

- **libsodium has no bulk benchmark of its own.** Its tests in benchmark mode run through libtool's wrapper script, and
  all but Argon2id spend much of their time parsing hex test vectors. Only `pwhash_argon2id` is a workload as it is.
- **libwebp's lossy decoder is scalar.** 78% of it is the boolean decoder, in `GetCoeffsFast`, `GetLargeValue` and
  `VP8ParseIntraModeRow`. Its SIMD is in the encoder and the lossless predictors.
- **FLAC spends 13% to 35% in MD5,** which it computes over the audio to detect corruption. It's scalar, and it
  translates in the relaxed run.
- **Opus is flat and mostly scalar floating point.** No SIMD kernel reaches 2% of decoding.
- **zlib-ng's Adler-32 kernels aren't hot here,** since gzip uses CRC-32. A zlib-format workload would make
  `adler32_avx512_vnni` hot, and it calls only intrinsics the model has.

## How each project builds its kernels

Read from each build's `compile_commands.json`, or the `Makefile` its configure wrote, on 2026-11-10. The manifest has
every flag.

| Project | Kernels are | Its own level | Its flags for SIMD | Run-time dispatch |
| --- | --- | --- | --- | --- |
| llama.cpp | C and C++ with intrinsics | `-O3` | `-march=native`, which on z is `znver5` | None: the build targets the host |
| XNNPACK | C with intrinsics, generated | `-O2` | On each AVX-512 VNNI file: `-mf16c -mfma -mavx512f -mavx512cd -mavx512bw -mavx512dq -mavx512vl -mavx512vnni` | Yes |
| zlib-ng | C with intrinsics | `-O2` | On each file: `-mavx2 -mbmi2`, or `-mavx512f -mavx512dq -mavx512bw -mavx512vl -mbmi2 -mtune=cascadelake`, with `-mavx512vnni` or `-mpclmul -mvpclmulqdq` where needed | Yes: on z it takes the AVX-512 kernels |
| zstd | C, with SSE2 for 16-byte copies and row masks | `-O3` | None. `huf_decompress_amd64.S` is assembly, and it's under 1.5% here | For BMI2 only |
| libdeflate | C with intrinsics | `-O2` | None: a target attribute on each function | Yes |
| FLAC | C with intrinsics | `-O3`, with `-fassociative-math -fno-signed-zeros -fno-trapping-math -freciprocal-math` on every file | None: a target attribute on each function | Yes |
| libwebp | C with intrinsics | `-O3` | `-msse4.1` or `-mavx2` on those files | Yes |
| Opus | C with intrinsics, floating point | `-O3` | `-msse4.1`, or `-mavx2 -mfma -mavx`, on those files | Yes |
| xxHash | C with intrinsics | `-O3` | None: a target attribute, in `xxh_x86dispatch.c`, which its `Makefile` adds on x86 with `DISPATCH ?= 1` | Yes: on z it takes AVX-512 |
| libsodium | C with intrinsics | `-O3 -fno-strict-aliasing -fno-strict-overflow -fstack-protector` | `-mavx2`, `-mavx512f`, `-maes -mpclmul` on those files | Yes. Curve25519 and one Salsa20 path are assembly, and neither was hot |

The corpus compiles every unit at `-O3`, [decision 3](#what-the-maintainer-decided-on-2026-11-10). Three build at
`-O2`: zlib-ng, libdeflate and XNNPACK.

## What the emitter does with them today

```console
nix develop -c bench/kernels/demand.py run      # writes bench/kernels/results/demand.json
nix develop -c bench/kernels/demand.py table    # prints the tables below
```

[`bench/kernels/demand.py`](../bench/kernels/demand.py) fetches each project through Nix at its pin, compiles each
unit the manifest names to IR, with the project's flags at `-O3`, runs `build/ir-lean --report` on it, and counts.
It compiles each unit twice:

- **As built:** the project's flags.
- **Relaxed:** the same with `-fno-strict-aliasing`, since the emitter refuses `!tbaa`, which a default build puts on
  nearly every load. For FLAC it also drops three of its four fast-math flags, which put an attribute on every
  function that the emitter refuses. No project is built this way but libsodium. It says what stops a function next.

The emitter gives a function's first reason only, so a function refused for one thing may have more behind it.
Translating says the emitter accepted a function. It doesn't say the Lean elaborates, which wasn't checked here, or
that the translation is right ([trust](trust.md#trust-boundaries)). A unit is a whole source file, so the counts
include its functions that aren't hot.

**Measured again after #105 and #107,** on z, at commit `41bd400`, which is `main` at `9718b50` with this page's
proposal on it, and changes nothing the emitter does. `demand.json` dates the run 2026-11-11, in UTC: it was the
evening of 2026-11-10 on z. The proposal's run, at `df3e997` on 2026-11-10, translated 24 of the 798 functions in the
ten projects that aren't rejected as built and 241 relaxed, and 19 of their 85 named kernels relaxed, 16 of them in
the six. Now it's 31 and 279, and 25 of the 85, 22 of them in the six. Every gain is #107's: VZEROUPPER, PCLMULQDQ,
AESNI, the saturating packs, PMULH, PAVG, PSADBW, PSIGN, PHADD and BZHI are modeled now. No function translated
before and is refused now, so #105's new refusals cost none here. The tables are the new run's. It was run once more
at `5c99def`, which changes nothing the emitter does either, with the same counts, so that each project in
`demand.json` carries what it was measured with: its own date, commit and clang. A run of some projects keeps the
others' counts with their own, and so can't pass them off as its own.

| Project | Units | Instructions | Functions | Translate as built | Relaxed |
| --- | ---: | ---: | ---: | ---: | ---: |
| base64 | 2 | 1,528 | 4 | 0 | 2 |
| blake3 | 2 | 8,483 | 5 | 0 | 3 |
| flac | 12 | 39,563 | 247 | 0 | 109 |
| libdeflate | 2 | 15,867 | 28 | 1 | 9 |
| libsodium | 6 | 10,491 | 30 | 7 | 7 |
| libwebp | 14 | 29,633 | 234 | 8 | 68 |
| llama.cpp | 2 | 22,170 | 40 | 0 | 0 |
| opus | 6 | 7,716 | 30 | 3 | 8 |
| xnnpack | 4 | 2,214 | 4 | 0 | 0 |
| xxhash | 2 | 18,251 | 93 | 10 | 27 |
| zlib-ng | 7 | 6,835 | 25 | 1 | 20 |
| zstd | 5 | 37,947 | 67 | 1 | 31 |

Of the kernels the profiles name:

| Project | Kernels named | Translate as built | Relaxed |
| --- | ---: | ---: | ---: |
| base64 | 4 | 0 | 2 |
| blake3 | 2 | 0 | 0 |
| flac | 16 | 0 | 6 |
| libdeflate | 3 | 0 | 0 |
| libsodium | 7 | 4 | 4 |
| libwebp | 21 | 0 | 3 |
| llama.cpp | 5 | 0 | 0 |
| opus | 7 | 0 | 0 |
| xnnpack | 4 | 0 | 0 |
| xxhash | 5 | 0 | 2 |
| zlib-ng | 10 | 0 | 7 |
| zstd | 7 | 0 | 3 |

Twenty-five of the 85 named kernels in the projects that aren't rejected translate whole in the relaxed run, 22 of
them in the six approved projects, against 19 and 16 in the proposal's run. Those new since #107 are marked *new*:

- **zlib-ng:** `longest_match_avx512`, 54% of compressing, and `compress_block`, `build_tree`, `insert_string`,
  `quick_insert_string` and `zng_inflate_table`, and *new* `crc32_fold_vpclmulqdq`, with its 84 PCLMULQDQ calls.
- **libsodium, as built:** `fill_block_with_xor` and `argon2_fill_segment_avx512f`, 99% of Argon2id between them, and
  `blake2b_compress_avx2`, and *new* `gh_ad_blocks`, AES-GCM's GHASH, which has no workload of its own here.
- **xxHash:** `XXH64` and `XXH32`, each a quarter of `xxhsum -b`. Both are scalar.
- **FLAC:** `FLAC__MD5Transform`, `FLAC__crc16` and `FLAC__crc16_update_words64`, all three scalar, and *new* its two
  integer residual kernels, 20% of `flac -8` between them, and `FLAC__precompute_partition_info_sums_intrin_avx2`, all
  three AVX2, whose first reason was VZEROUPPER.
- **libwebp:** `BuildHuffmanTable` and `VectorMismatch_AVX2`, and *new* `CombinedShannonEntropy_AVX2`, 37% of
  `cwebp -lossless`.
- **zstd,** an alternate: `ZSTD_btGetAllMatches_noDict_3`, 51% of level 19, `ZSTD_insertBt1` and
  `ZSTD_encodeSequences_bmi2`.

And base64's two decoders, *new*, though base64 is rejected.

### What stops the rest

Functions by first reason, relaxed, in each project:

| Project | What stops the rest, relaxed: functions by first reason |
| --- | --- |
| base64 | inline assembly: 1; intrinsic llvm.x86.avx512.pmultishift.qb.512: 1 |
| blake3 | intrinsic llvm.prefetch: 2 |
| flac | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet: 64; function attribute memory on a function whose calls outside the module access memory: 17; function attribute norecurse on a function that calls outside the module: 13; function attribute nofree on a function whose calls outside the module have effects: 10; parameter attribute noalias: 8; metadata !alias: 7; call to @_, which isn't translated: 6; call to external @_, which touches memory: F4: 4; others: 10 |
| libdeflate | call to @_, which isn't translated: 3; instruction load volatile: 3; metadata !range: 3; call parameter attribute readonly: 2; intrinsic llvm.experimental.noalias.scope.decl: 2; intrinsic llvm.prefetch: 2; call to external @_, which touches memory: F4: 1; call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet: 1; others: 2 |
| libsodium | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet: 17; call to @_, which isn't translated: 2; function attribute norecurse on a function that calls outside the module: 2; call to external @_, which may be null: 1; instruction load volatile: 1 |
| libwebp | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet: 41; parameter attribute noalias: 28; in a cycle with a function refused for: parameter attribute noalias: 27; call to external @_, which touches memory: F4: 23; metadata !alias: 14; intrinsic llvm.experimental.noalias.scope.decl: 11; in a cycle with a function refused for: call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet: 10; function attribute norecurse on a function that calls outside the module: 3; others: 9 |
| llama.cpp | intrinsic llvm.fma: 15; type: a vector of pointers: 9; instruction freeze of a vector: 4; intrinsic llvm.x86.avx.max.ps.256: 4; intrinsic llvm.fmuladd: 3; intrinsic llvm.experimental.noalias.scope.decl: 2; parameter attribute noalias: 2; call to external @_, which touches memory: F4: 1 |
| opus | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet: 12; call to @_, which isn't translated: 2; call to external @_, which touches memory: F4: 1; fast-math flag nnan: 1; function attribute norecurse on a function that calls outside the module: 1; intrinsic llvm.fmuladd: 1; intrinsic llvm.x86.sse.rcp.ps: 1; metadata !alias: 1; others: 2 |
| xnnpack | instruction inttoptr: 3; intrinsic llvm.masked.load: 1 |
| xxhash | intrinsic llvm.experimental.noalias.scope.decl: 24; call attribute memory: 23; intrinsic llvm.prefetch: 6; call return attribute dereferenceable_or_null: 3; metadata !noalias: 3; call parameter attribute captures(address): 2; call to @_, which isn't translated: 2; parameter attribute noalias: 2; others: 1 |
| zlib-ng | call to @_, which isn't translated: 2; call parameter attribute readonly: 1; call to external @_, which touches memory: F4: 1; intrinsic llvm.memmove: 1 |
| zstd | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet: 18; call to @_, which isn't translated: 9; intrinsic llvm.memmove: 3; inline assembly: 2; call attribute memory: 1; intrinsic llvm.prefetch: 1; metadata !noalias: 1; type: a vector of pointers: 1 |

And added up over the ten projects that aren't rejected, which is the coverage lanes' demand:

| What stops a function, relaxed, in the projects that aren't rejected | Functions | Projects |
| --- | ---: | --- |
| call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | 153 | flac, libdeflate, libsodium, libwebp, opus, zstd |
| parameter attribute noalias | 41 | flac, libwebp, llama.cpp, opus, xxhash |
| intrinsic llvm.experimental.noalias.scope.decl | 39 | libdeflate, libwebp, llama.cpp, xxhash |
| call to external @_, which touches memory: F4 | 31 | flac, libdeflate, libwebp, llama.cpp, opus, zlib-ng |
| call to @_, which isn't translated | 28 | flac, libdeflate, libsodium, libwebp, opus, xxhash, zlib-ng, zstd |
| in a cycle with a function refused for: parameter attribute noalias | 27 | libwebp |
| call attribute memory | 24 | xxhash, zstd |
| metadata !alias | 23 | flac, libwebp, opus, xxhash |
| function attribute norecurse on a function that calls outside the module | 19 | flac, libsodium, libwebp, opus |
| function attribute memory on a function whose calls outside the module access memory | 17 | flac |
| intrinsic llvm.fma | 15 | llama.cpp |
| type: a vector of pointers | 11 | llama.cpp, opus, zstd |
| function attribute nofree on a function whose calls outside the module have effects | 10 | flac |
| in a cycle with a function refused for: call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | 10 | libwebp |
| intrinsic llvm.prefetch | 9 | libdeflate, xxhash, zstd |
| intrinsic llvm.fmuladd | 8 | flac, llama.cpp, opus |
| call return attribute dereferenceable_or_null | 5 | flac, xxhash |
| instruction freeze of a vector | 5 | libwebp, llama.cpp |
| intrinsic llvm.memmove | 5 | libdeflate, zlib-ng, zstd |
| indirect call that can reach @_, which isn't translated | 4 | flac, libdeflate, libwebp |
| instruction load volatile | 4 | libdeflate, libsodium |
| intrinsic llvm.x86.avx.max.ps.256 | 4 | llama.cpp |
| metadata !noalias | 4 | xxhash, zstd |
| call parameter attribute readonly | 3 | libdeflate, zlib-ng |
| instruction inttoptr | 3 | xnnpack |
| metadata !range | 3 | libdeflate |
| call parameter attribute captures(address) | 2 | xxhash |
| inline assembly | 2 | zstd |
| llvm.loop.mustprogress off a loop's latch, in a function with irreducible control flow | 2 | flac |
| more than one parameter with attribute initializes | 2 | libwebp |
| call to external @_, which may be null | 1 | libsodium |
| constant ptr getelementptr inbounds nuw (i8, ptr @_, i64 16) with flags that don't plainly hold | 1 | libwebp |
| constant ptr getelementptr inbounds nuw (i8, ptr @_, i64 8) with flags that don't plainly hold | 1 | libwebp |
| fast-math flag nnan | 1 | opus |
| intrinsic llvm.masked.load | 1 | xnnpack |
| intrinsic llvm.x86.sse.rcp.ps | 1 | opus |
| parameter attribute dead_on_unwind | 1 | libwebp |

What that asks of the lanes, most functions first:

1. **`!tbaa`,** which the relaxed run sets aside. As built, 767 of 798 functions are refused, and `!tbaa` is the
   first reason for 294 of them, more than any other, with 27 more in a cycle with one.
2. **Calls outside the module from a function with a stack frame,** 153 functions and 10 more behind them: F4's.
3. **`noalias`,** as a parameter attribute, `llvm.experimental.noalias.scope.decl`, `!noalias` and `!alias.scope`:
   134 functions, all memory lane. It was 114 in the proposal's run: what an intrinsic stopped first then, `noalias`
   stops now, in libwebp most.
4. **Floating point.** `llvm.fma` is the first reason for four of llama.cpp's five kernels, and the only intrinsic
   they call that the model refuses, and `llvm.fmuladd` for FLAC's autocorrelation, 22% of `flac -8`.
5. **`llvm.prefetch`,** 299 calls. It changes no value. It's the first reason for `XXHL64_default_avx512`, and it's
   in three of the four XNNPACK kernels.
6. **FLAC's function attributes:** `"no-signed-zeros-fp-math"` and its three siblings sit on every function, with or
   without floating point in it, and stop all 247 as built.

In the proposal's run, `llvm.x86.avx.vzeroupper` was fifth: four calls, the first reason for FLAC's two integer
residual kernels and its partition sums. It's modeled since #107, and all three translate.

### The x86 intrinsics

| Project | `llvm.x86.*` the model has, with calls | `llvm.x86.*` it refuses, with calls |
| --- | --- | --- |
| base64 | `avx.ptestz.256` 28, `avx2.pmadd.ub.sw` 30, `avx2.pmadd.wd` 30, `avx2.pshuf.b` 86 | `avx512.permvar.qi.512` 10, `avx512.pmultishift.qb.512` 10 |
| blake3 | None | None |
| flac | `avx.vzeroupper` 4, `avx2.pmadd.wd` 78, `avx2.psra.d` 24, `avx2.psrl.q` 12 | None |
| libdeflate | None | None |
| libsodium | `aesni.aesenc` 988, `aesni.aesenclast` 76, `aesni.aeskeygenassist` 13, `pclmulqdq` 490 | None |
| libwebp | `avx2.packssdw` 7, `avx2.packsswb` 2, `avx2.packuswb` 10, `avx2.pavg.b` 28, `avx2.pmadd.wd` 3, `avx2.pmulh.w` 7, `avx2.psad.bw` 14, `sse2.packssdw.128` 59, `sse2.packsswb.128` 48, `sse2.packuswb.128` 146, `sse2.pavg.b` 47, `sse2.pmadd.wd` 158, `sse2.pmulh.w` 30, `sse2.pmulhu.w` 96, `sse2.psad.bw` 20, `ssse3.psign.w.128` 8 | None |
| llama.cpp | `avx2.packssdw` 20, `avx2.packsswb` 10, `avx2.pavg.b` 16, `avx2.pmadd.ub.sw` 598, `avx2.pmadd.wd` 267, `avx2.pshuf.b` 74, `avx2.psign.b` 454, `avx512.pmaddubs.w.512` 384, `avx512.pmaddw.d.512` 120, `avx512.pshuf.b.512` 48, `avx512.vpdpbusd.256` 237, `avx512.vpdpbusd.512` 192, `sse2.packuswb.128` 1, `sse2.pmadd.wd` 2, `ssse3.phadd.d.128` 2, `ssse3.phadd.w.128` 7, `ssse3.pshuf.b.128` 28 | `avx.cvt.ps2dq.256` 40, `avx.max.ps.256` 55, `avx.round.ps.256` 40, `sse.max.ps` 18, `sse.max.ss` 9, `vcvtps2ph.128` 9 |
| opus | None | `avx.hadd.ps.256` 3, `avx.maskload.ps.256` 9, `sse.max.ps` 5, `sse.rcp.ps` 1, `sse.rsqrt.ps` 3, `sse2.cvttps2dq` 1 |
| xnnpack | `avx512.mask.pmovs.db.512` 14, `avx512.vpdpbusd.512` 156 | `avx512.mask.cvtps2dq.512` 14, `avx512.max.ps.512` 10, `avx512.min.ps.512` 24 |
| xxhash | `avx512.pternlog.d.512` 10 | None |
| zlib-ng | `avx2.pshuf.b` 1, `avx512.pternlog.d.512` 32, `bmi.bzhi.32` 7, `pclmulqdq` 96, `pclmulqdq.512` 64, `ssse3.pshuf.b.128` 38 | None |
| zstd | None | None |

Every intrinsic the units call that the model refuses, over the ten projects that aren't rejected, which is the x86
lane's demand, with the floating-point and memory lanes' beside it:

| Intrinsic the model refuses, in the projects that aren't rejected | Calls | Lane | Projects |
| --- | ---: | --- | --- |
| `llvm.fmuladd` | 499 | floating point | flac, libwebp, llama.cpp, opus |
| `llvm.experimental.noalias.scope.decl` | 372 | memory | libdeflate, libwebp, llama.cpp, opus, xxhash |
| `llvm.prefetch` | 299 | none | libdeflate, libsodium, xnnpack, xxhash, zstd |
| `llvm.fma` | 198 | floating point | llama.cpp, opus, xnnpack |
| `llvm.masked.gather` | 77 | memory | llama.cpp |
| `llvm.vector.reduce.fadd` | 73 | floating point | flac |
| `llvm.memmove` | 68 | memory | flac, libdeflate, zlib-ng, zstd |
| `llvm.x86.avx.max.ps.256` | 55 | long tail | llama.cpp |
| `llvm.x86.avx.cvt.ps2dq.256` | 40 | long tail | llama.cpp |
| `llvm.x86.avx.round.ps.256` | 40 | long tail | llama.cpp |
| `llvm.pdep` | 36 | long tail | llama.cpp |
| `llvm.masked.store` | 28 | memory | xnnpack, zlib-ng |
| `llvm.x86.avx512.min.ps.512` | 24 | long tail | xnnpack |
| `llvm.x86.sse.max.ps` | 23 | long tail | llama.cpp, opus |
| `llvm.masked.load` | 20 | memory | llama.cpp, xnnpack, zlib-ng |
| `llvm.x86.avx512.mask.cvtps2dq.512` | 14 | long tail | xnnpack |
| `llvm.x86.avx512.max.ps.512` | 10 | long tail | xnnpack |
| `llvm.x86.avx.maskload.ps.256` | 9 | long tail | opus |
| `llvm.x86.sse.max.ss` | 9 | long tail | llama.cpp |
| `llvm.x86.vcvtps2ph.128` | 9 | long tail | llama.cpp |
| `llvm.sqrt` | 3 | floating point | opus |
| `llvm.x86.avx.hadd.ps.256` | 3 | long tail | opus |
| `llvm.x86.sse.rsqrt.ps` | 3 | long tail | opus |
| `llvm.floor` | 2 | floating point | opus |
| `llvm.stackrestore` | 1 | none | opus |
| `llvm.stacksave` | 1 | none | opus |
| `llvm.x86.sse.rcp.ps` | 1 | long tail | opus |
| `llvm.x86.sse2.cvttps2dq` | 1 | long tail | opus |

Read by what a kernel needs, not by count:

- **Every `llvm.x86.*` intrinsic left is on floating-point values:** 14 of them, 241 calls, in llama.cpp, Opus and
  XNNPACK, and only llama.cpp is approved. They wait for the floating-point lane, as `llvm.fma` and `llvm.fmuladd` do.
- **`llvm.pdep`,** 36 calls in llama.cpp. At this pin it reaches IR as a generic intrinsic, not as `llvm.x86.*`.
- **`chunkmemset_avx512`,** in front of `inflate_fast_avx512`, 90% of zlib-ng's decompressing, now stops at `call
  parameter attribute readonly`, the first reason behind BZHI.

In the proposal's run, the x86 lane's demand was 39 refused `llvm.x86.*` intrinsics with 3,025 calls, read as: the
saturating packs, 303 calls and nearly every libwebp kernel; the high multiplies `pmulh.w` and `pmulhu.w`, 133;
`pavg.b` and `psad.bw`, 125; `psign.b`, 454, in llama.cpp's `q5_0` and `q8_0` dot products; `pclmulqdq`, 650 with the
512-bit form, zlib-ng's CRC-32 and libsodium's GHASH; `aesni.aesenc`, 988, libsodium's AES-GCM only; and
`bmi.bzhi.32`, 7, in front of `chunkmemset_avx512`. #107 modeled every one of them.

### Each kernel

| Project | Kernel | Instructions | As built | Relaxed | Intrinsics it calls |
| --- | --- | ---: | --- | --- | --- |
| flac | `FLAC__lpc_compute_autocorrelation_intrin_fma_lag_12` | 338 | function attribute "no-signed-zeros-fp-math" | intrinsic llvm.fmuladd | `fmuladd` 50, `memset` 1, `vector.reduce.fadd` 12 |
| flac | `FLAC__lpc_compute_autocorrelation_intrin_fma_lag_16` | 464 | function attribute "no-signed-zeros-fp-math" | intrinsic llvm.fmuladd | `fmuladd` 103, `memset` 1, `vector.reduce.fadd` 16 |
| flac | `FLAC__lpc_compute_residual_from_qlp_coefficients_16_intrin_avx2` | 1,309 | function attribute "no-signed-zeros-fp-math" | ok | `vector.reduce.add` 1, `x86.avx.vzeroupper` 1, `x86.avx2.pmadd.wd` 78, `x86.avx2.psra.d` 12 |
| flac | `FLAC__lpc_compute_residual_from_qlp_coefficients_intrin_avx2` | 963 | function attribute "no-signed-zeros-fp-math" | ok | `vector.reduce.add` 1, `x86.avx.vzeroupper` 1, `x86.avx2.psra.d` 12 |
| flac | `FLAC__fixed_compute_best_predictor_wide_intrin_avx2` | 233 | function attribute "no-signed-zeros-fp-math" | function attribute norecurse on a function that calls outside the module | `abs` 5, `umin` 6, `vector.reduce.add` 5 |
| flac | `FLAC__precompute_partition_info_sums_intrin_avx2` | 258 | function attribute "no-signed-zeros-fp-math" | ok | `abs` 10, `assume` 1, `ctlz` 1, `vector.reduce.add` 2, `x86.avx.vzeroupper` 1 |
| flac | `FLAC__MD5Transform` | 542 | function attribute "no-signed-zeros-fp-math" | ok | `fshl` 64 |
| flac | `FLAC__lpc_restore_signal` | 721 | function attribute "no-signed-zeros-fp-math" | parameter attribute noalias | `assume` 3, `vector.reduce.add` 9 |
| flac | `FLAC__lpc_compute_lp_coefficients` | 155 | function attribute "no-signed-zeros-fp-math" | intrinsic llvm.fmuladd | `fmuladd` 7, `lifetime.end` 1, `lifetime.start` 1, `umax` 1, `vector.reduce.fadd` 1 |
| flac | `FLAC__bitreader_read_rice_signed_block_bmi2` | 205 | function attribute "no-signed-zeros-fp-math" | llvm.loop.mustprogress off a loop's latch, in a function with irreducible control flow | `ctlz` 2, `lifetime.end` 2, `lifetime.start` 2, `umax` 1 |
| flac | `FLAC__bitwriter_write_rice_signed_block` | 351 | function attribute "no-signed-zeros-fp-math" | function attribute memory on a function whose calls outside the module access memory | `bswap` 7, `fshl` 6 |
| flac | `find_best_partition_order_` | 307 | function attribute "no-signed-zeros-fp-math" | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `ctlz` 2, `memcpy` 2, `uadd.sat` 1, `umax` 1, `umin` 1, `vector.reduce.or` 1 |
| flac | `read_frame_` | 1,888 | function attribute "no-signed-zeros-fp-math" | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `assume` 1, `lifetime.end` 31, `lifetime.start` 15, `memcpy` 2, `memset` 2, `umax` 1, `umin` 2 |
| flac | `FLAC__crc16_update_words64` | 54 | function attribute "no-signed-zeros-fp-math" | ok | None |
| flac | `FLAC__crc16` | 117 | function attribute "no-signed-zeros-fp-math" | ok | None |
| flac | `FLAC__fixed_compute_residual` | 374 | function attribute "no-signed-zeros-fp-math" | metadata !alias | `memcpy` 1 |
| libdeflate | `deflate_compress_lazy` | 1,764 | intrinsic llvm.experimental.noalias.scope.decl | intrinsic llvm.experimental.noalias.scope.decl | `assume` 1, `ctlz` 2, `cttz` 4, `experimental.noalias.scope.decl` 1, `lifetime.end` 1, `lifetime.start` 1, `memset` 2, `prefetch` 8, `sadd.sat` 32, `smin` 2, `umin` 4, `vector.reduce.add` 3 |
| libdeflate | `deflate_flush_block` | 1,506 | metadata !tbaa | call to @_, which isn't translated | `assume` 1, `memcpy` 2, `smin` 1, `umax` 2, `umin` 2, `vector.reduce.add` 9 |
| libdeflate | `deflate_decompress_bmi2` | 1,223 | metadata !tbaa | metadata !range | `assume` 1, `memcpy` 1, `memset` 6, `umax` 1, `umin` 2 |
| libsodium | `chacha20_encrypt_bytes` | 1,096 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `fshl` 40, `lifetime.end` 1, `lifetime.start` 1 |
| libsodium | `poly1305_blocks` | 584 | instruction load volatile | instruction load volatile | `fshl` 2 |
| libsodium | `blake2b_compress_avx2` | 689 | ok | ok | `fshl` 24 |
| libsodium | `fill_block_with_xor` | 561 | ok | ok | `fshl` 32 |
| libsodium | `argon2_fill_segment_avx512f` | 747 | ok | ok | `fshl` 32, `lifetime.end` 6, `lifetime.start` 6, `memcpy` 1, `memset` 6 |
| libsodium | `salsa20_encrypt_bytes` | 1,333 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `fshl` 84, `lifetime.end` 1, `lifetime.start` 1 |
| libsodium | `gh_ad_blocks` | 494 | ok | ok | `x86.pclmulqdq` 122 |
| libwebp | `GetCoeffsFast` | 252 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `bswap` 4, `ctlz` 3, `experimental.noalias.scope.decl` 8, `fshl` 4 |
| libwebp | `GetLargeValue` | 603 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `bswap` 11, `ctlz` 11, `experimental.noalias.scope.decl` 22, `fshl` 11 |
| libwebp | `VP8ParseIntraModeRow` | 743 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `bswap` 13, `ctlz` 12, `experimental.noalias.scope.decl` 26, `fshl` 13, `memset` 2 |
| libwebp | `Transform_SSE2` | 206 | metadata !tbaa | parameter attribute noalias | `x86.sse2.packuswb.128` 4, `x86.sse2.pmulh.w` 8 |
| libwebp | `VP8YuvToRgb32_SSE41` | 177 | metadata !tbaa | metadata !alias | `uadd.sat` 4, `usub.sat` 4, `x86.sse2.packuswb.128` 6, `x86.sse2.pmulhu.w` 20 |
| libwebp | `DecodeImageData` | 652 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `memcpy` 2, `smax` 1, `smin` 1 |
| libwebp | `BuildHuffmanTable` | 541 | metadata !tbaa | ok | `assume` 1, `lifetime.end` 2, `lifetime.start` 2, `memset` 1, `smin` 1 |
| libwebp | `PredictorAdd13_SSE2` | 52 | metadata !tbaa | parameter attribute noalias | `x86.sse2.packuswb.128` 1 |
| libwebp | `TransformColorInverse_AVX2` | 63 | in a cycle with a function refused for: metadata !tbaa | in a cycle with a function refused for: parameter attribute noalias | `x86.avx2.pmulh.w` 2 |
| libwebp | `PredictorAdd12_AVX2` | 131 | in a cycle with a function refused for: metadata !tbaa | in a cycle with a function refused for: parameter attribute noalias | `x86.avx2.packuswb` 8 |
| libwebp | `VP8LHashChainFill` | 373 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `memset` 2, `smax` 2, `smin` 3, `usub.sat` 1 |
| libwebp | `VP8LGetBackwardReferences` | 2,229 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `assume` 2, `ctlz` 1, `lifetime.end` 19, `lifetime.start` 12, `memcpy` 11, `memset` 6, `smin` 1, `umin` 2 |
| libwebp | `GetCombinedEntropyUnrefined_C` | 156 | more than one parameter with attribute initializes | more than one parameter with attribute initializes | `experimental.noalias.scope.decl` 4, `memset` 2 |
| libwebp | `VP8LResidualImage` | 1,082 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `assume` 2, `lifetime.end` 5, `lifetime.start` 3, `memcpy` 28, `memset` 2, `smax` 1, `smin` 5, `umax` 1 |
| libwebp | `CombinedShannonEntropy_AVX2` | 118 | metadata !tbaa | ok | `cttz` 1, `x86.avx2.packssdw` 4, `x86.avx2.packsswb` 2 |
| libwebp | `VectorMismatch_AVX2` | 80 | metadata !tbaa | ok | None |
| libwebp | `CollectColorBlueTransforms_AVX2` | 240 | metadata !tbaa | parameter attribute noalias | `x86.avx2.pmulh.w` 3 |
| libwebp | `QuantizeBlock_SSE41` | 75 | metadata !tbaa | parameter attribute noalias | `abs` 2, `smin` 2, `x86.sse2.packssdw.128` 2, `x86.sse2.packsswb.128` 1, `x86.sse2.pmulhu.w` 2, `x86.ssse3.psign.w.128` 2 |
| libwebp | `FTransform_SSE2` | 111 | metadata !tbaa | metadata !alias | `x86.sse2.packssdw.128` 4, `x86.sse2.pmadd.wd` 6 |
| libwebp | `ITransform_SSE2` | 256 | intrinsic llvm.experimental.noalias.scope.decl | intrinsic llvm.experimental.noalias.scope.decl | `experimental.noalias.scope.decl` 5, `x86.sse2.packuswb.128` 5, `x86.sse2.pmulh.w` 12 |
| libwebp | `SSE4x4_SSE2` | 53 | metadata !tbaa | parameter attribute noalias | `vector.reduce.add` 1, `x86.sse2.pmadd.wd` 2 |
| llama.cpp | `ggml_gemm_q4_K_8x8_q8_K` | 3,034 | metadata !tbaa | intrinsic llvm.fma | `assume` 1, `fma` 32, `lifetime.end` 6, `lifetime.start` 6, `memset` 4, `x86.avx2.pmadd.ub.sw` 128, `x86.avx2.pmadd.wd` 24, `x86.avx512.pmaddubs.w.512` 128, `x86.avx512.pmaddw.d.512` 24, `x86.ssse3.phadd.w.128` 4 |
| llama.cpp | `ggml_gemv_q4_K_8x8_q8_K` | 386 | instruction freeze of a vector | instruction freeze of a vector | `assume` 1, `fma` 2, `memset` 9, `x86.avx2.pmadd.ub.sw` 16, `x86.avx2.pmadd.wd` 3, `x86.ssse3.phadd.w.128` 1 |
| llama.cpp | `ggml_vec_dot_q4_K_q8_K` | 172 | metadata !tbaa | intrinsic llvm.fma | `fma` 2, `x86.avx2.pmadd.ub.sw` 8, `x86.avx2.pmadd.wd` 8, `x86.sse2.pmadd.wd` 1, `x86.ssse3.phadd.w.128` 1 |
| llama.cpp | `ggml_vec_dot_q5_0_q8_0` | 146 | metadata !tbaa | intrinsic llvm.fma | `assume` 1, `fma` 3, `x86.avx2.psign.b` 6, `x86.avx512.vpdpbusd.256` 3 |
| llama.cpp | `ggml_vec_dot_q6_K_q8_K` | 162 | metadata !tbaa | intrinsic llvm.fma | `fma` 1, `x86.avx2.pmadd.ub.sw` 8, `x86.avx2.pmadd.wd` 9 |
| opus | `op_pvq_search_sse2` | 335 | metadata !tbaa | intrinsic llvm.x86.sse.rcp.ps | `assume` 3, `fabs` 3, `fmuladd` 2, `memcpy` 1, `memset` 3, `smax` 6, `vector.reduce.add` 1, `x86.sse.max.ps` 5, `x86.sse.rcp.ps` 1, `x86.sse.rsqrt.ps` 3, `x86.sse2.cvttps2dq` 1 |
| opus | `exp_rotation` | 837 | function attribute norecurse on a function that calls outside the module | function attribute norecurse on a function that calls outside the module | `assume` 4, `fmuladd` 36 |
| opus | `opus_fft_impl` | 1,422 | type: a vector of pointers | type: a vector of pointers | `fmuladd` 30, `lifetime.end` 1, `lifetime.start` 1, `smax` 1 |
| opus | `encode_pulses` | 73 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `abs` 2, `smax` 4, `smin` 3 |
| opus | `decode_pulses` | 162 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `fmuladd` 4, `smax` 2, `smin` 2 |
| opus | `quant_partition` | 491 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `assume` 2, `lifetime.end` 1, `lifetime.start` 1, `memset` 1, `smax` 1, `smin` 2 |
| opus | `celt_pitch_xcorr_avx2` | 143 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `fma` 16, `x86.avx.hadd.ps.256` 3, `x86.avx.maskload.ps.256` 9 |
| xnnpack | `xnn_qs8_qc8w_igemm_minmax_fp32_ukernel_7x16c8__avx512vnni_prfm` | 623 | instruction inttoptr | instruction inttoptr | `lifetime.end` 2, `lifetime.start` 2, `masked.store` 7, `prefetch` 6, `smax` 7, `x86.avx512.mask.cvtps2dq.512` 7, `x86.avx512.mask.pmovs.db.512` 7, `x86.avx512.min.ps.512` 7, `x86.avx512.vpdpbusd.512` 42 |
| xnnpack | `xnn_qs8_qc8w_gemm_minmax_fp32_ukernel_7x16c8__avx512vnni_prfm` | 598 | instruction inttoptr | instruction inttoptr | `lifetime.end` 1, `lifetime.start` 1, `masked.store` 7, `prefetch` 6, `smax` 7, `x86.avx512.mask.cvtps2dq.512` 7, `x86.avx512.mask.pmovs.db.512` 7, `x86.avx512.min.ps.512` 7, `x86.avx512.vpdpbusd.512` 42 |
| xnnpack | `xnn_qd8_f32_qc8w_gemm_minmax_ukernel_10x16c8__avx512vnni_prfm` | 899 | instruction inttoptr | instruction inttoptr | `fma` 10, `masked.store` 10, `prefetch` 6, `x86.avx512.max.ps.512` 10, `x86.avx512.min.ps.512` 10, `x86.avx512.vpdpbusd.512` 60 |
| xnnpack | `xnn_qs8_rsum_ukernel__avx512vnni_u128_acc2` | 94 | metadata !tbaa | intrinsic llvm.masked.load | `masked.load` 1, `vector.reduce.add` 1, `x86.avx512.vpdpbusd.512` 12 |
| xxhash | `XXHL64_default_avx512` | 173 | intrinsic llvm.prefetch | intrinsic llvm.prefetch | `assume` 1, `prefetch` 2, `x86.avx512.pternlog.d.512` 1 |
| xxhash | `XXHL128_default_avx512` | 161 | intrinsic llvm.experimental.noalias.scope.decl | intrinsic llvm.experimental.noalias.scope.decl | `assume` 1, `experimental.noalias.scope.decl` 6, `lifetime.end` 1, `lifetime.start` 1, `prefetch` 2, `x86.avx512.pternlog.d.512` 1 |
| xxhash | `XXH3_update_avx512` | 283 | intrinsic llvm.experimental.noalias.scope.decl | intrinsic llvm.experimental.noalias.scope.decl | `assume` 12, `experimental.noalias.scope.decl` 9, `memcpy` 4, `prefetch` 4, `x86.avx512.pternlog.d.512` 2 |
| xxhash | `XXH64` | 220 | metadata !tbaa | ok | `assume` 1, `fshl` 24 |
| xxhash | `XXH32` | 196 | metadata !tbaa | ok | `assume` 1, `fshl` 18 |
| zlib-ng | `longest_match_avx512` | 251 | metadata !tbaa | ok | `cttz` 5, `usub.sat` 1 |
| zlib-ng | `deflate_medium` | 476 | metadata !tbaa | call to external @_, which touches memory: F4 | `umin` 1 |
| zlib-ng | `compress_block` | 232 | metadata !tbaa | ok | None |
| zlib-ng | `build_tree` | 521 | metadata !tbaa | ok | `memset` 1, `umax` 1 |
| zlib-ng | `insert_string` | 38 | metadata !tbaa | ok | None |
| zlib-ng | `quick_insert_string` | 27 | metadata !tbaa | ok | None |
| zlib-ng | `inflate_fast_avx512` | 923 | metadata !tbaa | call to @_, which isn't translated | `abs` 1, `masked.load` 1, `masked.store` 1, `memcpy` 20, `umin` 8, `x86.bmi.bzhi.32` 1 |
| zlib-ng | `chunkmemset_avx512` | 223 | call parameter attribute readonly | call parameter attribute readonly | `abs` 1, `ctpop` 1, `cttz` 1, `lifetime.end` 1, `lifetime.start` 1, `masked.load` 6, `masked.store` 3, `memcpy` 1, `memmove` 1, `memset` 1, `x86.avx2.pshuf.b` 1, `x86.bmi.bzhi.32` 6, `x86.ssse3.pshuf.b.128` 2 |
| zlib-ng | `zng_inflate_table` | 562 | metadata !tbaa | ok | `assume` 2, `lifetime.end` 2, `lifetime.start` 2, `memset` 1, `umax` 1, `umin` 1 |
| zlib-ng | `crc32_fold_vpclmulqdq` | 560 | metadata !tbaa | ok | `lifetime.end` 2, `lifetime.start` 2, `memcpy` 3, `x86.avx512.pternlog.d.512` 16, `x86.pclmulqdq` 52, `x86.pclmulqdq.512` 32, `x86.ssse3.pshuf.b.128` 18 |
| zstd | `ZSTD_compressBlock_doubleFast` | 4,509 | metadata !tbaa | call attribute memory | `cttz` 40, `lifetime.end` 4, `lifetime.start` 4, `memcpy` 4, `prefetch` 16 |
| zstd | `ZSTD_decompressSequences_bmi2` | 829 | metadata !tbaa | inline assembly | `ctlz` 2, `lifetime.end` 5, `lifetime.start` 3, `memcpy` 1, `memmove` 2, `smax` 1, `smin` 1, `umax` 3, `umin` 1 |
| zstd | `ZSTD_encodeSequences_bmi2` | 489 | metadata !tbaa | ok | None |
| zstd | `HIST_count_parallel_wksp` | 251 | metadata !tbaa | intrinsic llvm.memmove | `memmove` 1, `memset` 2, `umax` 3, `vector.reduce.umax` 1 |
| zstd | `ZSTD_btGetAllMatches_noDict_3` | 739 | metadata !tbaa | ok | `cttz` 10, `lifetime.end` 1, `lifetime.start` 1, `umax` 1, `umin` 2, `usub.sat` 1 |
| zstd | `ZSTD_compressBlock_opt2` | 1,720 | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | call to external functions in a function with a stack frame or promises about memory, which IRLean.World doesn't wrap yet | `assume` 2, `ctlz` 42, `lifetime.end` 12, `lifetime.start` 8, `memcpy` 9, `memmove` 2, `memset` 2, `umax` 1, `umin` 1 |
| zstd | `ZSTD_insertBt1` | 245 | metadata !tbaa | ok | `cttz` 2, `lifetime.end` 1, `lifetime.start` 1, `umax` 1, `umin` 2, `usub.sat` 1 |

## Policies on patches written with AI

Decision 10 puts patches upstream last. What each project's own files said, read from the default branch of each
repository, as `raw.githubusercontent.com` served them. LLVM's and llama.cpp's were read on 2026-11-09 at 18:53 PST,
and the rest on 2026-11-10 at 06:26 PST. For each repository these paths were asked for: `CONTRIBUTING.md`,
`CONTRIBUTING`, `AGENTS.md`, `.github/CONTRIBUTING.md`, `AI_POLICY.md`, the two pull request templates and `CLAUDE.md`.

| Project | What it says | Where |
| --- | --- | --- |
| LLVM | "contributors can use whatever tools they would like to craft their contributions, but there must be a human in the loop. Contributors must read and review all LLM-generated code or text before they ask other project members to review it." Contributions with substantial tool-generated content are to be labeled, such as with an `Assisted-by:` trailer. "it bans agents that take action in our digital spaces without human approval". AI tools must not be used on issues labeled good first issue. Its examples include a pull request that "contains a proof from Alive2, which is a strong signal of value and correctness" | [AI Tool Use Policy](https://llvm.org/docs/AIToolPolicy.html) |
| llama.cpp | "AI-generated code is allowed. You are 100% responsible for every line, however it was produced." "Undisclosed AI usage may result in your account being permanently banned from contributing to the project." It asks for disclosure, a manual review of "something like one hour per 200-400 LOC", and being able to explain every line. "It is strictly prohibited to use AI to write your posts for you (bug reports, feature requests, pull request descriptions, Github discussions, responding to humans, ...)". `AGENTS.md` adds that automated commits or pull requests may get a contributor banned | [`CONTRIBUTING.md`](https://github.com/ggml-org/llama.cpp/blob/master/CONTRIBUTING.md), [`AGENTS.md`](https://github.com/ggml-org/llama.cpp/blob/master/AGENTS.md) |
| zstd | "If AI or other automated tools were used to find the problem or write the change, say so in the pull request description." Its template has a box for it | [`CONTRIBUTING.md`](https://github.com/facebook/zstd/blob/dev/CONTRIBUTING.md) |
| XNNPACK | It has an `AGENTS.md`, "Guidelines for automated agents and developers contributing to XNNPACK", which `CONTRIBUTING.md` tells every contributor to read, and asks for "No verbose AI-generated PR descriptions or review essays". Google's CLA applies | [`AGENTS.md`](https://github.com/google/XNNPACK/blob/master/AGENTS.md) |
| xxHash | An `AGENTS.md`, "meant for automated contributors (coding agents, bots)", with technical rules only: hash values must not change, C90, pull requests go to `dev` | [`AGENTS.md`](https://github.com/Cyan4973/xxHash/blob/dev/AGENTS.md) |
| lz4 | An `AGENTS.md`, "Notes for coding agents", with technical rules only: speed changes "must be measured (`lz4 -b`, `tests/fullbench`), not estimated" | [`AGENTS.md`](https://github.com/lz4/lz4/blob/dev/AGENTS.md) |
| OpenSSL | "using an AI tool, you must declare which agent and model were used, by adding `Assisted-by: {agent}:{model}` below the commit message", and "Including AI-generated content in your contribution requires a signed CLA with the AI clauses (CLA v1.1 or later)" | [`CONTRIBUTING.md`](https://github.com/openssl/openssl/blob/master/CONTRIBUTING.md). Its separate policy page wasn't read |
| FLAC, libwebp, dav1d, BLAKE3 | Each has a `CONTRIBUTING.md` that doesn't mention AI, language models or generated code | Searched for those words. dav1d's is its GitHub mirror's |
| zlib-ng, libdeflate, Opus, libsodium, base64 | None of the paths exists, so no policy was found | A project can state one elsewhere, such as in a wiki or a mailing list, which wasn't searched |

The roadmap's note on llama.cpp, from a mirror, was wrong: it accepts AI-generated code, with disclosure and a human
who understands every line, and bans AI-written descriptions and automated submissions. Its note on LLVM matches the
live page. The roadmap has said what llama.cpp's live page does since #104
([below](#what-other-docs-should-change)), and the policies here are as read before that.

## Risks, by project

| Project | Risks |
| --- | --- |
| llama.cpp | Every kernel mixes integer SIMD with floating point, so a whole-function win needs the floating-point lane, and so far its wins are slices. It releases several times a day, so the pin ages fastest. Models are 1 GB and more, and aren't in CI |
| zlib-ng | `-mtune=cascadelake` on its AVX-512 files, on a Zen 5. Its baseline is `-O2`. gzip never reaches its Adler-32 kernels |
| xxHash | Its kernels are short and already tight, so wins may be scarce. `xxhsum -b` runs for a fixed time, not a fixed amount of work, so its own figure, MB/s, is the measure, not wall time |
| libsodium | No bulk benchmark of its own: [decision 7](#what-the-maintainer-decided-on-2026-11-10)'s driver, ours, is still to be written. A rewrite of cryptographic code can break constant-time behaviour, which `Refines` doesn't see: a win here needs that said beside it |
| FLAC | As built, every function is refused for its fast-math attributes. Its hottest kernel at level 8, the autocorrelation, is floating point with reassociation allowed, which the model refuses |
| libwebp | The scalar boolean decoder dominates lossy decoding. The 14 intrinsics the model lacked in the proposal's run are modeled since #107. `cwebp` in the dev shell has no libpng, so the encoder's input is the lossless images' pixels |
| zstd | Little SIMD. `ZSTD_decompressSequences_bmi2` holds an inline `.p2align` directive, which the emitter refuses as inline assembly |
| libdeflate | Its kernels are zlib-ng's problems again, with one compressor function at 83%. Its checksums, the SIMD it has, aren't reached by its benchmark |
| Opus | Floating point throughout, and flat |
| XNNPACK | Its build fetches dependencies outside Nix. No release tags. Its kernels are generated, so a patch upstream goes to a template, not to the file a win is in |

Common to all: z is shared, with a load average of 5 to 9 from other work while this was measured, so timings need
the [protocol](#the-benchmark-protocol)'s pairing. And every pin goes stale.

## The rules that fix the corpus

### The manifest

[`bench/kernels/manifest.toml`](../bench/kernels/manifest.toml) holds, for each project: its repository, tag, commit
and Nix hash, the units its kernels are compiled from, the flags the project builds each with, the kernels, and the
workload, with the SHA-256 of each input. `[corpus]` holds what every project is compiled with: the LLVM tag, the
target, `-O3`, and the machine.

The proposal had approving and fixing as one act. Decision 7 puts libsodium's driver between them, so they're two:

1. **Approved,** on 2026-11-10. `corpus.state` is `"approved"`, `corpus.approved` names the six, `corpus.approved_on`
   gives the date, and `corpus.decided_in` points to where the roadmap records the decisions. Nothing is locked, so an
   approved project's entry can still change, as the driver will change libsodium's workload.
2. **Fixed,** once the driver is written, in one pull request: `corpus.state` becomes `"fixed"`, and `[lock]` records
   the digest `bench/kernels/kernels.py digest` prints, the date, and the pull request. The search runs after that.

The digest is a SHA-256 over `[corpus]`'s settings and each approved project's whole entry: its pin, hash, units,
flags, kernels, workload and input hashes. So after that, a change to any of them, or to the pinned LLVM, changes the
digest.

### The test that fails when it changes

`tests/kernels_test.py`, the `kernels` test, in under a second, with no Lean or LLVM:

- The manifest meets every rule in [`bench/kernels/kernels.py`](../bench/kernels/kernels.py): each project pinned by
  a full commit and an SRI hash, in one of the five domains, under a listed license, with units, kernels, a workload
  and hashed inputs, or rejected with the criteria it fails.
- While it's proposed, nothing is approved and there's no lock, so approving can't happen by halves.
- While it's approved, it names at least 3 projects, none rejected, with the date and where it was decided, and has no
  lock or amendment, so fixing it is one act too. The list is the six of 2026-11-10.
- Once it's fixed, the digest has to be the lock's, or reached from it by `[[amendment]]`s, each with its date, its
  reason, the pull request, and the digest it starts from and ends on. So the corpus can change, and never quietly:
  the roadmap's rule for a gate.
- A fixed corpus has at least 3 projects, and `corpus.llvm_tag` is `tests/llvm/targets.toml`'s pin.
- Cases built to break each rule are refused: a pin, a hash, a flag, a kernel or an input changed under a lock, an
  amendment that starts from the wrong digest, an approved project that's rejected.
- This page names every project with its commit, and `bench/kernels/results/demand.json` is about the manifest's pins.

`kernels_demand` runs `bench/kernels/demand.py check --offline`: every unit compiles at the pin, and defines the
kernels the manifest names. It skips where the sources aren't in the Nix store, as in CI, and
`bench/kernels/demand.py check` fetches them.

### What the corpus doesn't fix

- **Where a win may be.** The kernels are where the time is. A win may be in any function of an approved project, as
  that project is built for its workload.
- **Flake inputs.** None are needed: the scripts fetch with `builtins.fetchTree` at the manifest's hashes. If CI is to
  run the workloads, or the plugin's certify mode over the corpus, a `nix/kernels.nix` with a `fetchFromGitHub` for
  each approved project, and a `devShells.kernels` beside `devShells.llama`, would do it, with a test that its hashes
  are the manifest's. That changes `flake.nix` and not `flake.lock`.

## The benchmark protocol

The precedent is [llama.cpp's Q5](llama-q5.md#performance-and-variance) and `tests/llama_bench.py`. This makes it the
rule for every win.

**What's compared.** Two builds of the project that differ only in the rewritten functions:

- **The baseline** is the project's own build, with the pinned clang, its own flags, and `-O3`.
- **The candidate** is that build with the rewritten unit's object replaced, and the library linked again by the
  build's own link command.
- **Checked before timing:** the two differ in the rewritten functions and nothing else, and `llc` on the unchanged
  IR gives the baseline's machine code, as `tests/llama_bench.py` checks.
- **The same output.** Where a workload's output is its result, a decompressed file, a hash or logits, every timed
  run's output is hashed, and has to be the baseline's, bit for bit. Where it's only timings, as for libsodium's
  Argon2id test in benchmark mode and `xxhsum -b`, the candidate's build first has to pass the project's own test of
  the same functions in its checking mode, which compares against known answers, and the timed runs' output is
  recorded and not compared. Each workload's check is written into the manifest when the list is fixed.

**What's measured.** Wall time of the workload's command, from start to exit, on z, pinned to cores of one CCD, with
the thread count the manifest gives, one unless the workload says otherwise. A run shorter than 2 seconds is repeated
inside one timed command until it isn't. Where a benchmark runs for a fixed time, as `xxhsum -b` does, its own figure
is the measure. The load average and the cores are recorded with each run.

**How variance is handled.**

- Runs come in pairs, baseline and candidate back to back, in an order drawn from a recorded seed.
- Each session warms both once, then runs its pairs. No pair is removed, outliers included.
- The statistic is the median of the paired ratios, with a 95% percentile bootstrap interval from 20,000 resamples of
  the pairs. A ratio is baseline time over candidate time, or, where the measure is a rate, as `xxhsum -b`'s MB/s is,
  candidate rate over baseline rate, so that above 1 is faster either way.
- A session that picks among candidates is exploratory. Only confirmation sessions count: run after the candidate, its
  workload, its thread count and its cores are written down, with a new seed.

### Measurably faster

A candidate is measurably faster when all of these hold:

1. **At least 30 pairs, in at least 2 confirmation sessions.**
2. **The pooled interval's lower end is at or above 1.005.** Half a percent, so that noise alone doesn't make a win.
3. **Every session's median is above 1.**
4. **No other workload of the project is slower:** each one's pooled interval reaches 1 or above.

Otherwise it's inconclusive, or slower, and the board says which. By this rule the Q5 rewrite, at 1.049 with an
interval of 1.029 to 1.057 over 30 pairs in 2 sessions, is measurably faster on one thread. Its eight-thread trial, at
1.004 with an interval of 0.979 to 1.351, isn't. The q4_K rewrite was measured in rounds, without pairs or an
interval, so it would be measured again.

## The harness

[`bench/kernels/harness.py`](../bench/kernels/harness.py) runs the protocol, and
[`bench/kernels/protocol.py`](../bench/kernels/protocol.py) holds its statistic and the rule. [The board](board.md)
reads what they write. Built on 2026-11-10, and checked on zlib-ng and on a project of its own, with no rewrite yet:
[its controls](#the-harnesss-controls) are below.

```console
nix develop -c bench/kernels/kernels.py inputs build/kernels/inputs zlib-ng
nix develop -c bench/kernels/harness.py build zlib-ng
nix develop -c bench/kernels/harness.py candidate zlib-ng NAME --unit deflate_medium.c --ir REWRITTEN.ll --functions deflate_medium
nix develop -c bench/kernels/harness.py plan zlib-ng --candidate NAME --workload compress --pairs 15 --out PLAN.json
nix develop -c bench/kernels/harness.py measure PLAN.json
nix develop -c bench/kernels/harness.py compare PLAN.session-1.json PLAN.session-2.json --other OTHER.session-1.json --other OTHER.session-2.json --out PLAN.comparison.json
```

Each step, and what it checks:

- **`build`** is the baseline: the project's own build, its CMake or its `Makefile`, with the dev shell's clang, the
  pinned 23.1.3, the manifest's flags and `-O3`, as [`profile.sh`](../bench/kernels/profile.sh) builds it. `--opt
  project` builds it at the project's own level instead, `-O2` for zlib-ng, which [decision 3](#what-the-maintainer-decided-on-2026-11-10)
  asks a win to beat too. It refuses a build where any compile isn't at the level asked for.
- **`candidate`** builds the same tree a second time and replaces the rewritten unit's object, and the build links
  the binaries again with its own commands: Ninja, after the object keeps its time and what's linked from it is
  removed, since its deps log would otherwise compile the object again, and make, after the object is made newer.
  The candidate is the unit's IR with the functions named by `--functions` rewritten, or an object. Before anything
  is timed it checks that `llc` on the unit's unchanged IR, emitted from the build's own compile command with its use
  lists, gives the build's machine code, function by function, as `tests/llama_bench.py` does; that the two builds
  differ in exactly the functions declared; that each workload's check passes on the candidate; and that each
  workload whose output is its result gives the baseline's output, bit for bit. A function's code is compared
  without addresses, and with what each instruction refers to: in the binaries, the named symbol a RIP-relative
  operand is in and the offset in it, and in the unit's objects, where each relocation points, a named symbol by its
  name and a constant by what it holds. Every named datum of the unit's object has to hold the same bytes, so a
  rewrite that also has another function load another table or constant, or changes a table's contents, is refused.
  A check that drives the build again takes the build's own arguments as `{build_args}`, and the candidate is
  refused if a check, a setup or a run changes either build's binaries or the candidate's objects: xxHash's
  `Makefile` keeps its objects under a hash of its flags, and `make check` without them built `xxhsum` again from
  the source, over the candidate, which would then have been timed. The record is `ir-lean.kernels.build/2`.
- **`plan`** writes down what's compared before it runs: both builds, by their records, which it copies beside
  itself, the workload, the threads, the cores, the pairs, and a new seed for each session. The cores are one per
  thread, one hardware thread a core, in one CCD, by default the first cores of the last: CPU 8 on z, as the Q5
  rewrite was measured on.
- **`measure`** runs a plan's sessions. Each pins itself to the plan's cores, checks both builds' binaries are the
  ones their records hash, warms each once, and repeats a run inside one timed command, as `sh` running it that
  many times, until it takes at least 2 s, with a tenth to spare, checked warm before any pair and recorded as the
  session's calibration. Then it runs its pairs, baseline and candidate back to back in an order drawn from its
  seed. Each run records its wall time from start to exit, its CPU time, the load average, the cores and the hash of
  everything it wrote. A run whose output isn't the baseline's stops the session, and no pair is removed. A session
  is run once: `measure` takes its file before it starts, as an `ir-lean.kernels.attempt/1` record, refuses a
  session whose file is there, and leaves one that fails or is stopped there as a failed or interrupted attempt,
  with what it had done. Another try is another plan, with new seeds.
- **`compare`** takes the ratios, their median and the 95% percentile bootstrap from 20,000 resamples, per session
  and pooled, with a seed taken from the sessions' own, and reads them by [the rule](#measurably-faster). The rule
  doesn't say when a candidate is slower, so the harness takes the mirror of a win: at least 30 pairs in at least 2
  confirmation sessions, the pooled interval at or under 1 / 1.005, and every session's median under 1. What it
  compares, its level and whether it's a control are its plan's, checked against the build records beside the
  plan, and the workloads condition 4 needs are the project's, from its configuration. Each ratio is worked out
  from its pair's runs, and the sessions are read in one order whatever order they're given in. A comparison also
  lists how its sessions fall short of the protocol: a session of its plan missing, or one given twice; a seed, an
  order, a kind or a ratio that isn't what the plan and the runs give; runs repeated to under 2 s, or any timed run
  under 2 s; cores not in one CCD; a plan written after a session started; a pair missing; or two sessions with one
  seed. Another workload's sessions count for condition 4 only if their plan is of the same builds, level, kind and
  control, and otherwise that workload is as good as unmeasured. Only a comparison with no problem, read by the
  protocol's own rule, can put a win on the board.

**What it reads.** The manifest gives each project's pin, flags, level and workload command. What the manifest
doesn't say is in [`bench/kernels/harness.toml`](../bench/kernels/harness.toml), apart so the digest that fixes the
corpus doesn't change: how to drive each project's build, which binaries its workloads run, and the workloads beyond
the manifest's one, such as zlib-ng's decompressing. "Each workload's check is written into the manifest when the list
is fixed", and another lane is writing them. The harness takes a workload's `check`, a command or a table with one,
and its `threads`, `measure` and `output`, from the manifest wherever the manifest gives them, and from
`harness.toml` until then, and every record says which each came from. Today `harness.toml` has them all: zlib-ng's
two workloads hash their output, and xxHash's `xxhsum -b`, whose output is only timings, runs `make check` first.

**What it can build.** zlib-ng, with CMake and Ninja, measured below. Its own `-O2` build too: with `--opt project`
it built, and a candidate the same as it passed every check, and no session was timed on it. xxHash, with make: its
baseline built, and a candidate the same as it, for each of its two units, passed every check, `make check`
included. One exploratory session of 3 pairs on `xxhsum -b` read the four MiB/s figures it prints, one a hash, whose
mean is the measure, and it hasn't been timed by the protocol. llama.cpp, FLAC and libwebp build with CMake too and
need only an entry in `harness.toml`. libsodium builds with autotools and libtool, whose objects the harness can't
replace yet.

**One thing `llc` can't read.** The pinned clang, asked for use lists, can write a `uselistorder` directive for an
inline `asm` value, and the pinned `llc` refuses it: "invalid type for inline asm constraint string". Each of
xxHash's units has one. The harness drops those directives, and only those, records how many, and
leaves it to the check that `llc` gives the build's machine code to say whether that changed anything. It didn't, for
either unit.

### The harness's controls

There's no win to measure yet, so the harness was checked on candidates whose answer is known. These are checks on
the harness, not on any rewrite, and none is a win. [The board](board.md#harness-controls) shows each, worked out again
from its sessions every time it's written.

**On zlib-ng,** on 2026-11-10 from 19:48 to 20:09 PST, on z, at `-O3`, compressing `silesia.tar` at level 6, the
manifest's workload. One run took about 1.8 s, so each timed run was two, about 3.7 s. Every session was pinned to
CPU 8, in the second CCD, with a one-minute load average of 1.3 to 6.1 from other lanes building and checking Lean
on the same machine. Each control was planned before it ran, as a confirmation would be, with 2 sessions of 20 pairs,
and the first session of each of the four plans ran, and then the second of each:

| Control | Baseline against candidate | Verdict | Ratio, median [95% interval] | Each session's median | Pairs above 1 | Load average |
| --- | --- | --- | --- | --- | --- | --- |
| The same | The baseline against `aa` | Inconclusive | 1.0001 [0.9994, 1.0009] | 1.0013, 0.9998 | 21 of 40 | 1.6 to 6.1 |
| Slower | The baseline against `o0` | Slower | 0.7745 [0.7734, 0.7755] | 0.7738, 0.7751 | 0 of 40 | 1.4 to 5.3 |
| Faster | `o0` against the baseline | Faster | 1.2897 [1.2884, 1.2910] | 1.2896, 1.2899 | 40 of 40 | 1.4 to 3.6 |
| Faster, decompressing, the project's other workload | `o0` against the baseline | Not slower: its interval reaches 1 | 1.0034 [1.0021, 1.0041] | 1.0037, 1.0031 | 30 of 40 | 1.3 to 3.6 |

- **The same:** `deflate_medium.c`'s object made again by `llc` from its unchanged IR, which the checks found the same
  as the baseline's in every function.
- **Slower:** `deflate_medium.c` compiled at `-O0`, 18% of compressing by the profile, which changes `deflate_medium`
  and the five helpers inlined into it at `-O3`.
- **Faster:** the same two builds the other way round, the `-O0` one as the baseline. It's a check that the harness
  calls a known gain faster, by every condition of the rule, decompressing included as the project's other workload.
  It isn't a win: nothing was rewritten.

What they say about the harness and z:

- **The same is inconclusive, and close to 1.** Its single pairs ranged from 0.983 to 1.029, and the median of 40 is
  within a tenth of a percent of 1, with the load average from 1.6 to 6.1.
- **Moving code shows.** Decompressing never runs `deflate_medium`, and the `-O3` build was 0.3% faster at it than the
  one with the `-O0` object, with an interval clear of 1. What changed for it is where code is: the `-O0` object is
  bigger, and what's linked after it moves. So relinking alone can move a workload by a few tenths of a percent, which
  the rule's 1.005 is above.
- **Every comparison is by the protocol,** with no problem listed: pinned to one CCD, runs of at least 2 s, the plan
  written first, no pair missing, and a new seed for each session. Their sessions and the build records beside
  their plans are as they were timed, by the harness before its review: the build records are
  `ir-lean.kernels.build/1`, from before it compared what each function refers to, so no win could rest on them,
  and the board reads them only for what they compared. Worked out again by the stricter `compare`, every number and
  verdict is the same, and only the faster comparison's record changed, to name its other workload's plan. The first five sessions' records give their CCD as
  CPU 8 alone, from a bug in how the harness read it that was fixed before the other three ran, which give CPUs 8 to
  15 and 24 to 31. CPU 8 is in that CCD in all eight.

**On a project of its own,** [`tests/kernels_bench`](../tests/kernels_bench), the `kernels_bench` test runs the same
three in about 30 s in CI, with the slower one a rewrite of its kernel with an extra loop, given as IR, and runs
repeated to 0.05 s instead of 2. Those aren't by the protocol, which the test checks the board says.

## What a win is

One win is one rewrite, proved, reviewed and measured:

- **One rewrite** is the smallest set of changed functions that was measured together. The q4_K rewrite changes two
  functions at 34 places, and was measured as one, so it's one win.
- **Proved:** a Lean theorem that the target refines the source, in decision 9's tiers, checked in CI.
- **Reviewed:** a second agent's review of the statement, and a must-break mutant, as decision 11 asks.
- **Measured:** [measurably faster](#measurably-faster) on a workload of its project.
- **On the fixed corpus:** in an approved project, at its pin, found after the lock.
- **Counted once:** a rewrite of code two projects share, as zstd's copy of xxHash is, counts for the project it was
  found in.

Each win carries four labels, and every combination counts toward the bar:

| Label | Values | From |
| --- | --- | --- |
| What's proved | A slice, with cutting it out and putting its result back trusted, or the whole function | Decision 9 |
| What the proof rests on | The standard three axioms, or those and `bv_decide`'s | Decision 9 |
| The source IR | As built, or relaxed with `-fno-strict-aliasing` | [Decision 4](#what-the-maintainer-decided-on-2026-11-10) here |
| How it was found | By the rule search from stored rules, by the search with a rule written for its site, or by an agent proposer | Decision 8: only the first meets the checkpoint, S7 |

## The two llama.cpp rewrites

On `main` are the q4_K rewrite ([llama.cpp](llama.md)) and the Q5 rewrite ([llama.cpp's Q5](llama-q5.md)). Neither
was found by a search. Decision 8 left open whether they count toward the ten.

**For counting them:**

- They're what the bar asks for: proved, on real code, and faster on a real workload.
- S3's wording doesn't say a search has to find a win, and S2 already credits them.
- llama.cpp is in the corpus on its own merits, so they're on the fixed corpus.
- Ten wins in three months is hard, and two are in hand.

**Against:**

- **They were chosen before the corpus was.** Decision 7 fixes the corpus first so that wins aren't picked after the
  fact, and these are the reason llama.cpp was the first project anyone thought of.
- **The bar is the engine's.** S3 is superoptimizer v2's exit criterion. With these, it's 8 wins from the engine.
- **Neither was measured by one rule.** The Q5 rewrite was timed against clang 23.1.5, not the pinned 23.1.3. The
  q4_K rewrite was timed in rounds, with no interval.
- **A reader of the board would discount them,** and then wonder about the rest.

**Recommendation: they don't count as they stand, and each can.** A rewrite counts when the rule search finds it on
the fixed corpus and it's measured by the protocol, as any other win is. If the search finds the q4_K sites again from
the rules `Vnni.lean` leaves in the store, that's a win, labeled as resting on a rule written for its site, which
can't meet the checkpoint. Until then the board shows both in a row of their own: proved and measured before the
corpus was fixed, found by hand.

**Decided on 2026-11-10, as recommended:** neither counts toward the ten yet.
[Decision 2](#what-the-maintainer-decided-on-2026-11-10) is the record, and the roadmap's S3 says it too.

What that costs: the two wins in hand have to be earned again, and the Q5 rewrite needs its matcher's pattern stated as
a rule.

## What isn't done, and what couldn't be found out

- **Little timing.** Every number in the sections before [the harness](#the-harness) is a share of cycles, or a count.
  Only zlib-ng's compressing and decompressing have been timed, for [the harness's controls](#the-harnesss-controls),
  so nothing yet says how noisy the other workloads are on z, which the protocol's 30 pairs assume is enough.
- **No bulk workload for libsodium yet.** [Decision 7](#what-the-maintainer-decided-on-2026-11-10)'s driver, over its
  `crypto_secretstream` example, isn't written, so the corpus is approved and not fixed.
- **Whether the translated kernels elaborate in Lean** wasn't checked. `tests/ir_features.py` checks that for its
  probes, not for these.
- **What's behind each first reason.** The emitter reports one reason per function.
- **How often each of chunk 1's rewrites fires on the corpus,** the gauge of the roadmap's decision 3 after #103. The list is approved now, and it
  still needs a way to tell which of INV-04's rewrites fired.
- **XNNPACK and llama.cpp weren't profiled here.** llama.cpp's shares are from 2026-11-07, on `main`.
- **Policies stated outside a repository's files** weren't searched, and OpenSSL's policy page wasn't read.
- **The whole-unit counts cover the units named,** 64 of them. A project's other files weren't compiled.
- **On another host.** Everything ran on z. A C unit is compiled with `PROOF_CFLAGS`, so its IR should be the same on
  a Mac, and that wasn't tried. A C++ unit takes the host's headers, as `tests/llama.py` does.

## What other docs should change

The proposal listed these for the lane that holds them. With the approval, this pull request makes them, and what was
done elsewhere first says where:

- **`docs/roadmap.md`, decision 10,** the sentences on llama.cpp's policy: `main` already says what llama.cpp's live
  page does, since #104.
- **`docs/roadmap.md`, decisions 7 and 8 after #103:** each links to
  [the kernel corpus, decided on 2026-11-10](roadmap.md#the-kernel-corpus-decided-on-2026-11-10), the seven decisions
  with a reason for each, and decision 8's open question says how it was decided. "Now, next, later", the dependency
  on the corpus, S3, S7, S8 and "How we measure" name the kernel corpus, approved and not yet fixed.
- **`docs/roadmap.md`, "The flywheel",** "the [corpus](corpus.md) of `opt`'s rewrites": unchanged.
- **`README.md`, the Docs table:** a row for the kernel corpus.
- **`docs/status.md`, [llama.cpp](llama.md) and [llama.cpp's Q5](llama-q5.md):** nothing. None of them says whether
  the two rewrites count toward S3's bar, so none needs decision 2. When the list is fixed, `docs/status.md` gets a
  line under "What's been built".
- **`docs/x86-intrinsics.md`:** its comparison with this page's demand calls the projects approved.
- **`docs/testing.md`:** two rows in its Tests table, `kernels` and `kernels_demand`.
- **`docs/chunks.md`:** nothing.
