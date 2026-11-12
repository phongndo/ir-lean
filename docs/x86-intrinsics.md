# x86 intrinsics

Which of x86's integer SIMD intrinsics real kernels need, ranked, and what the model has of them. This is decision 7
of the thirteen the [roadmap](roadmap.md) records for 2026-11-09: the corpus is hot numeric kernels with SIMD, on
x86-64 first, each intrinsic is written from Intel's pseudo-code and checked against the processor, and a rule may
use one only once it has been. For what a theorem that uses one rests on, read [trust](trust.md#trust-boundaries)
first. Facts here were checked on 2026-11-10, at LLVM `llvmorg-23.1.3`, on z, a Ryzen 9 9950X.

## Which intrinsics need a model

Clang's headers lower most of `<immintrin.h>` to generic IR: `_mm256_add_epi32` is an `add`, `_mm_shuffle_epi32` a
`shufflevector`, `_mm256_max_epu8` an `llvm.umax`. Only what reaches IR as a call to `llvm.x86.*` needs a model of its
own. The pin has 1,685 of those, and 519 compute on integers only: every type in a call
[the probe](ir-features.md#what-the-check-does) builds is an integer or a vector of integers, and LLVM marks the
intrinsic `memory(none)`. The rest are floating point, which [waits](#whats-next), take a pointer, or have an effect,
such as `llvm.x86.rdtsc`.

## The ranking

[`tools/x86_rank.py count`](../tools/x86_rank.py) fetches ten projects through nix, each at the release the flake's
nixpkgs pins, and llama.cpp at the release [`nix/llama.nix`](../nix/llama.nix) pins. It asks each project's own build
system which command compiles each file, runs each again with the pinned clang at `-O3`, to IR, and counts the calls
to each intrinsic. So each file is compiled with the flags its project gives it, such as `-mavx2` for zlib-ng's
`adler32_avx2.c`. It only counts: no rewrite runs on the IR, and none of it is kept. The counts are in
[`tests/x86_rank/ranking.json`](../tests/x86_rank/ranking.json). Counting takes some tens of minutes with 8 jobs,
most of it libaom and ncnn, and wasn't timed:

```console
nix develop -c tools/x86_rank.py count
nix develop -c tools/x86_rank.py table
```

The first writes the file, and the second prints the tables below from it and from
[the classification](ir-features.md), which says what's modeled. The `x86_rank` test fails unless they're what's here,
so modeling an intrinsic changes this page.

A **family** is an intrinsic's name without its instruction set and width, so `llvm.x86.sse2.packsswb.128`,
`llvm.x86.avx2.packsswb` and `llvm.x86.avx512.packsswb.512` are the three forms of PACKSSWB, and PSRAID is PSRAD by
an immediate count. A family's **share** is its part of a project's integer `llvm.x86.*` calls, averaged over the
projects that have any. The ranking is by share, so that libaom, with 71% of the calls, counts once.

<!-- x86_rank table: begin -->
| Project | Domain | Release | Files compiled | Not compiled | Integer `llvm.x86.*` calls |
| --- | --- | --- | ---: | ---: | ---: |
| llama.cpp | inference | b12189 | 17 | 0 | 4,642 |
| ncnn | inference | 20250503 | 362 | 0 | 5,890 |
| zlib-ng | compression | 2.3.3 | 98 | 0 | 1,090 |
| libdeflate | compression | 1.26 | 22 | 0 | 892 |
| zstd | compression | 1.5.7 | 74 | 0 | 0 |
| libwebp | codecs | 1.6.0 | 179 | 0 | 2,695 |
| libaom | codecs | 3.15.1 | 362 | 0 | 49,468 |
| xxHash | hashing | 0.8.3 | 2 | 0 | 10 |
| BLAKE3 | hashing | 1.8.7 | 7 | 0 | 0 |
| libsodium | crypto | 1.0.22-unstable-2026-09-28 | 270 | 0 | 5,240 |

519 integer intrinsics at the pin, forms of 308 families, 249 of them modeled. 55 families have a call in these projects, 69,923 calls in all. The 52 of those families modeled at every form have 69,548 of the calls, 99.5%, and 99.2% by share.

| Rank | Family | Share | Calls | Projects | Functions | Forms modeled | llama.cpp | ncnn | zlib-ng | libdeflate | zstd | libwebp | libaom | xxHash | BLAKE3 | libsodium |
| ---: | --- | ---: | ---: | ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | PCLMULQDQ | 17.86% | 2,198 | 3 | 46 | 3 of 3 |  |  | 608 | 610 |  |  |  |  |  | 980 |
| 2 | PTERNLOGD | 14.52% | 166 | 3 | 17 | 3 of 3 |  |  | 64 | 92 |  |  |  | 10 |  |  |
| 3 | PMADDWD | 10.38% | 15,774 | 6 | 792 | 3 of 3 | 413 | 1,442 | 56 | 16 |  | 420 | 13,427 |  |  |  |
| 4 | AESENC | 8.65% | 3,626 | 1 | 26 | 3 of 3 |  |  |  |  |  |  |  |  |  | 3,626 |
| 5 | VPDPBUSD | 6.87% | 2,116 | 4 | 135 | 3 of 3 | 1,457 | 521 | 36 | 102 |  |  |  |  |  |  |
| 6 | PMADDUBSW | 4.19% | 4,369 | 3 | 220 | 3 of 3 | 1,006 |  | 56 |  |  |  | 3,307 |  |  |  |
| 7 | PAVGB | 3.97% | 1,827 | 3 | 148 | 3 of 3 | 16 |  |  |  |  | 790 | 1,021 |  |  |  |
| 8 | PACKUSWB | 3.91% | 3,583 | 4 | 414 | 3 of 3 | 33 | 30 |  |  |  | 655 | 2,865 |  |  |  |
| 9 | PACKSSDW | 3.73% | 5,361 | 4 | 558 | 3 of 3 | 20 | 849 |  |  |  | 169 | 4,323 |  |  |  |
| 10 | PSHUFB | 3.39% | 645 | 4 | 93 | 3 of 3 | 330 |  | 162 | 44 |  |  | 109 |  |  |  |
| 11 | PSIGNB | 3.28% | 1,218 | 1 | 82 | 2 of 2 | 1,218 |  |  |  |  |  |  |  |  |  |
| 12 | PSRAID | 2.17% | 8,576 | 1 | 150 | 3 of 3 |  |  |  |  |  |  | 8,576 |  |  |  |
| 13 | PMULHUW | 2.02% | 478 | 2 | 49 | 3 of 3 |  |  |  |  |  | 432 | 46 |  |  |  |
| 14 | PACKSSWB | 2.01% | 902 | 4 | 142 | 3 of 3 | 10 | 730 |  |  |  | 90 | 72 |  |  |  |
| 15 | PSADBW | 1.85% | 1,799 | 4 | 207 | 3 of 3 |  |  | 92 | 8 |  | 58 | 1,641 |  |  |  |
| 16 | VPDPWSSD | 1.84% | 865 | 1 | 22 | 3 of 3 |  | 865 |  |  |  |  |  |  |  |  |
| 17 | PMULHW | 1.33% | 653 | 3 | 86 | 3 of 3 |  | 452 |  |  |  | 72 | 129 |  |  |  |
| 18 | MASKPMOVSDB | 0.87% | 408 | 1 | 28 | 3 of 3 |  | 408 |  |  |  |  |  |  |  |  |
| 19 | AESKEYGENASSIST | 0.83% | 346 | 1 | 18 | 1 of 1 |  |  |  |  |  |  |  |  |  | 346 |
| 20 | PAVGW | 0.81% | 3,217 | 1 | 155 | 3 of 3 |  |  |  |  |  |  | 3,217 |  |  |  |
| 21 | PSLLID | 0.74% | 2,946 | 1 | 48 | 3 of 3 |  |  |  |  |  |  | 2,946 |  |  |  |
| 22 | PHADDD | 0.69% | 1,237 | 4 | 411 | 2 of 2 | 50 | 132 |  |  |  | 1 | 1,054 |  |  |  |
| 23 | VPMADCSWD | 0.45% | 213 | 1 | 4 | 0 of 1 |  | 213 |  |  |  |  |  |  |  |  |
| 24 | AESENCLAST | 0.41% | 170 | 1 | 18 | 3 of 3 |  |  |  |  |  |  |  |  |  | 170 |
| 25 | PSLLIW | 0.40% | 1,598 | 1 | 103 | 3 of 3 |  |  |  |  |  |  | 1,598 |  |  |  |
| 26 | PBLENDVB | 0.34% | 241 | 2 | 41 | 2 of 2 |  |  |  | 20 |  |  | 221 |  |  |  |
| 27 | PSRAIW | 0.34% | 1,328 | 1 | 48 | 3 of 3 |  |  |  |  |  |  | 1,328 |  |  |  |
| 28 | PMULHRSW | 0.29% | 1,164 | 1 | 103 | 3 of 3 |  |  |  |  |  |  | 1,164 |  |  |  |
| 29 | PSIGNW | 0.24% | 817 | 2 | 54 | 2 of 2 |  |  |  |  |  | 8 | 809 |  |  |  |
| 30 | VGF2P8AFFINEQB | 0.22% | 82 | 1 | 2 | 3 of 3 | 82 |  |  |  |  |  |  |  |  |  |
| 31 | VPDPBSSD | 0.19% | 88 | 1 | 2 | 0 of 3 |  | 88 |  |  |  |  |  |  |  |  |
| 32 | BZHI32 | 0.16% | 14 | 1 | 4 | 1 of 1 |  |  | 14 |  |  |  |  |  |  |  |
| 33 | VPMACSWD | 0.16% | 74 | 1 | 4 | 0 of 1 |  | 74 |  |  |  |  |  |  |  |  |
| 34 | PSRLD | 0.14% | 75 | 2 | 17 | 3 of 3 |  | 67 |  |  |  |  | 8 |  |  |  |
| 35 | PHADDW | 0.14% | 471 | 2 | 45 | 2 of 2 | 7 |  |  |  |  |  | 464 |  |  |  |
| 36 | AESIMC | 0.13% | 56 | 1 | 6 | 1 of 1 |  |  |  |  |  |  |  |  |  | 56 |
| 37 | AESDEC | 0.13% | 54 | 1 | 6 | 3 of 3 |  |  |  |  |  |  |  |  |  | 54 |
| 38 | PACKUSDW | 0.12% | 337 | 2 | 56 | 3 of 3 |  | 19 |  |  |  |  | 318 |  |  |  |
| 39 | PSRLW | 0.08% | 300 | 1 | 14 | 3 of 3 |  |  |  |  |  |  | 300 |  |  |  |
| 40 | PSRAD | 0.07% | 296 | 1 | 43 | 3 of 3 |  |  |  |  |  |  | 296 |  |  |  |
| 41 | AESDECLAST | 0.01% | 6 | 1 | 6 | 3 of 3 |  |  |  |  |  |  |  |  |  | 6 |
| 42 | PSIGND | 0.01% | 44 | 1 | 8 | 2 of 2 |  |  |  |  |  |  | 44 |  |  |  |
| 43 | PSRLIW | 0.01% | 43 | 1 | 3 | 3 of 3 |  |  |  |  |  |  | 43 |  |  |  |
| 44 | PSRAW | 0.01% | 42 | 1 | 9 | 3 of 3 |  |  |  |  |  |  | 42 |  |  |  |
| 45 | PSLLD | 0.01% | 24 | 1 | 6 | 3 of 3 |  |  |  |  |  |  | 24 |  |  |  |
| 46 | PSRLIQ | 0.01% | 20 | 1 | 2 | 3 of 3 |  |  |  |  |  |  | 20 |  |  |  |
| 47 | PSLLW | 0.00% | 17 | 1 | 3 | 3 of 3 |  |  |  |  |  |  | 17 |  |  |  |
| 48 | PHADDSW | 0.00% | 10 | 1 | 5 | 2 of 2 |  |  |  |  |  |  | 10 |  |  |  |
| 49 | CRC32 of 64 bits | 0.00% | 9 | 1 | 1 | 1 of 1 |  |  |  |  |  |  | 9 |  |  |  |
| 50 | CRC32 of 8 bits | 0.00% | 9 | 1 | 1 | 1 of 1 |  |  |  |  |  |  | 9 |  |  |  |
| 51 | PTESTZ | 0.00% | 4 | 1 | 2 | 2 of 2 |  |  |  |  |  |  | 4 |  |  |  |
| 52 | PHMINPOSUW | 0.00% | 3 | 1 | 3 | 1 of 1 |  |  |  |  |  |  | 3 |  |  |  |
| 53 | PSRLQ | 0.00% | 2 | 1 | 1 | 3 of 3 |  |  |  |  |  |  | 2 |  |  |  |
| 54 | CRC32 of 16 bits | 0.00% | 1 | 1 | 1 | 1 of 1 |  |  |  |  |  |  | 1 |  |  |  |
| 55 | CRC32 of 32 bits | 0.00% | 1 | 1 | 1 | 1 of 1 |  |  |  |  |  |  | 1 |  |  |  |

No call in these projects: 253 families. 83 are forms on MMX's registers, none of them modeled. The other 170, with the forms modeled of each: ADDCARRY32 (0 of 1), ADDCARRY64 (0 of 1), BEXTR32 (1 of 1), BEXTR64 (1 of 1), BEXTRIU32 (0 of 1), BEXTRIU64 (0 of 1), BZHI64 (1 of 1), CONFLICTD (0 of 3), CONFLICTQ (0 of 3), DBPSADBW (0 of 3), EXTRQ (0 of 1), EXTRQI (0 of 1), INSERTQ (0 of 1), INSERTQI (0 of 1), KADDB (0 of 1), KADDD (0 of 1), KADDQ (0 of 1), KADDW (0 of 1), KTESTCB (0 of 1), KTESTCD (0 of 1), KTESTCQ (0 of 1), KTESTCW (0 of 1), KTESTZB (0 of 1), KTESTZD (0 of 1), KTESTZQ (0 of 1), KTESTZW (0 of 1), MASKCOMPRESS (0 of 1), MASKEXPAND (0 of 1), MASKPMOVDB (3 of 3), MASKPMOVDW (3 of 3), MASKPMOVQB (3 of 3), MASKPMOVQD (1 of 1), MASKPMOVQW (3 of 3), MASKPMOVSDW (3 of 3), MASKPMOVSQB (3 of 3), MASKPMOVSQD (3 of 3), MASKPMOVSQW (3 of 3), MASKPMOVSWB (3 of 3), MASKPMOVUSDB (3 of 3), MASKPMOVUSDW (3 of 3), MASKPMOVUSQB (3 of 3), MASKPMOVUSQD (3 of 3), MASKPMOVUSQW (3 of 3), MASKPMOVUSWB (3 of 3), MASKPMOVWB (1 of 1), MPSADBW (0 of 2), PCMPESTRI128 (0 of 1), PCMPESTRIA128 (0 of 1), PCMPESTRIC128 (0 of 1), PCMPESTRIO128 (0 of 1), PCMPESTRIS128 (0 of 1), PCMPESTRIZ128 (0 of 1), PCMPESTRM128 (0 of 1), PCMPISTRI128 (0 of 1), PCMPISTRIA128 (0 of 1), PCMPISTRIC128 (0 of 1), PCMPISTRIO128 (0 of 1), PCMPISTRIS128 (0 of 1), PCMPISTRIZ128 (0 of 1), PCMPISTRM128 (0 of 1), PHSUBD (2 of 2), PHSUBSW (2 of 2), PHSUBW (2 of 2), PMOVMSKB (0 of 2), PMULTISHIFTQB (0 of 3), PSLLIQ (3 of 3), PSLLQ (3 of 3), PSLLVD (3 of 3), PSLLVQ (3 of 3), PSLLVW (3 of 3), PSRAIQ (3 of 3), PSRAQ (3 of 3), PSRAVD (3 of 3), PSRAVQ (3 of 3), PSRAVW (3 of 3), PSRLID (3 of 3), PSRLVD (3 of 3), PSRLVQ (3 of 3), PSRLVW (3 of 3), PTERNLOGQ (3 of 3), PTESTC (2 of 2), PTESTNZC (2 of 2), SHA1MSG1 (0 of 1), SHA1MSG2 (0 of 1), SHA1NEXTE (0 of 1), SHA1RNDS4 (0 of 1), SHA256MSG1 (0 of 1), SHA256MSG2 (0 of 1), SHA256RNDS2 (0 of 1), SUBBORROW32 (0 of 1), SUBBORROW64 (0 of 1), VBMACORV16HI (0 of 1), VBMACORV32HI (0 of 1), VBMACXORV16HI (0 of 1), VBMACXORV32HI (0 of 1), VGF2P8AFFINEINVQB (3 of 3), VGF2P8MULB (3 of 3), VMPSADBW (0 of 1), VP2INTERSECTD (0 of 3), VP2INTERSECTQ (0 of 3), VPDPBSSDS (0 of 3), VPDPBSUD (0 of 3), VPDPBSUDS (0 of 3), VPDPBUSDS (3 of 3), VPDPBUUD (0 of 3), VPDPBUUDS (0 of 3), VPDPWSSDS (3 of 3), VPDPWSUD (0 of 3), VPDPWSUDS (0 of 3), VPDPWUSD (0 of 3), VPDPWUSDS (0 of 3), VPDPWUUD (0 of 3), VPDPWUUDS (0 of 3), VPERMB (0 of 3), VPERMD (0 of 2), VPERMI2VARD (0 of 3), VPERMI2VARHI (0 of 3), VPERMI2VARQ (0 of 3), VPERMI2VARQI (0 of 3), VPERMQ (0 of 2), VPERMW (0 of 3), VPHADDBD (0 of 1), VPHADDBQ (0 of 1), VPHADDBW (0 of 1), VPHADDDQ (0 of 1), VPHADDUBD (0 of 1), VPHADDUBQ (0 of 1), VPHADDUBW (0 of 1), VPHADDUDQ (0 of 1), VPHADDUWD (0 of 1), VPHADDUWQ (0 of 1), VPHADDWD (0 of 1), VPHADDWQ (0 of 1), VPHSUBBW (0 of 1), VPHSUBDQ (0 of 1), VPHSUBWD (0 of 1), VPMACSDD (0 of 1), VPMACSDQH (0 of 1), VPMACSDQL (0 of 1), VPMACSSDD (0 of 1), VPMACSSDQH (0 of 1), VPMACSSDQL (0 of 1), VPMACSSWD (0 of 1), VPMACSSWW (0 of 1), VPMACSWW (0 of 1), VPMADCSSWD (0 of 1), VPMADD52HUQ (0 of 3), VPMADD52LUQ (0 of 3), VPPERM (0 of 1), VPSHAB (0 of 1), VPSHAD (0 of 1), VPSHAQ (0 of 1), VPSHAW (0 of 1), VPSHLB (0 of 1), VPSHLD (0 of 1), VPSHLQ (0 of 1), VPSHLW (0 of 1), VPSHUFBITQMB (0 of 3), VSHA512MSG1 (0 of 1), VSHA512MSG2 (0 of 1), VSHA512RNDS2 (0 of 1), VSM3MSG1 (0 of 1), VSM3MSG2 (0 of 1), VSM3RNDS2 (0 of 1), VSM4KEY4128 (0 of 1), VSM4KEY4256 (0 of 1), VSM4KEY4512 (0 of 1), VSM4RNDS4128 (0 of 1), VSM4RNDS4256 (0 of 1), VSM4RNDS4512 (0 of 1).

| Other refused intrinsic these files call | Calls | Projects |
| --- | ---: | ---: |
| `llvm.x86.avx.max.ps.256` | 2,624 | 3 |
| `llvm.x86.sse.max.ps` | 2,421 | 3 |
| `llvm.x86.sse2.cvttps2dq` | 2,126 | 1 |
| `llvm.maxnum` | 1,925 | 3 |
| `llvm.vector.reduce.fadd` | 1,919 | 3 |
| `llvm.masked.scatter` | 1,758 | 2 |
| `llvm.x86.avx.min.ps.256` | 1,623 | 2 |
| `llvm.masked.gather` | 1,459 | 2 |
| `llvm.x86.avx.cvtt.ps2dq.256` | 1,318 | 2 |
| `llvm.x86.sse.min.ps` | 1,312 | 1 |
| `llvm.experimental.noalias.scope.decl` | 1,293 | 7 |
| `llvm.x86.avx.round.ps.256` | 1,148 | 2 |
| `llvm.x86.avx.cvt.ps2dq.256` | 1,120 | 2 |
| `llvm.x86.avx512.max.ps.512` | 1,078 | 1 |
| `llvm.masked.load` | 1,024 | 4 |
| `llvm.x86.avx.ldu.dq.256` | 993 | 2 |
| `llvm.minnum` | 912 | 2 |
| `llvm.x86.avx512bf16.dpbf16ps.512` | 874 | 1 |
| `llvm.floor` | 863 | 4 |
| `llvm.x86.avx512.mask.cvttps2dq.512` | 720 | 1 |
| `llvm.exp` | 702 | 1 |
| `llvm.x86.avx512.min.ps.512` | 634 | 1 |
| `llvm.x86.avx2.gather.d.d.256` | 531 | 2 |
| `llvm.x86.sse3.ldu.dq` | 531 | 2 |
| `llvm.round` | 528 | 3 |
| `llvm.x86.avx512.mask.rndscale.ps.512` | 388 | 1 |
| `llvm.pow` | 331 | 1 |
| `llvm.x86.vcvtps2ph.128` | 298 | 2 |
| `llvm.x86.avx512.mask.gather.dpi.512` | 294 | 1 |
| `llvm.x86.avx.blendv.ps.256` | 288 | 1 |
<!-- x86_rank table: end -->

### What it doesn't show

- **Assembly.** OpenSSL, BoringSSL, dav1d, x264, libjpeg-turbo and isa-l write their kernels in assembly, which never
  reaches IR, so nothing here can rewrite them. BLAKE3 defaults to assembly too: this is its build from C with
  intrinsics.
- **What `-O3` already rewrote.** PMOVMSKB has no call anywhere, because InstCombine turns it into an `icmp slt` and a
  `bitcast`. PSHUFB with a constant mask becomes a `shufflevector`, which is why BLAKE3 and zstd have no call at all.
  A count of 0 says clang leaves no call, not that the kernel doesn't use the instruction.
- **How often a call runs.** These are call sites in the IR, after inlining and unrolling, not executions.
- **Other builds.** Each project is built one way, its default for x86-64 with runtime dispatch where it has it.
- **Instructions this processor lacks.** ncnn's VPMADCSWD and VPMACSWD are AMD's XOP, which Zen 5 doesn't have, so
  z can't check them.

## What the model has

Each definition follows the pseudo-code under "Operation" for its instruction in Intel's Software Developer's Manual,
volume 2, and names the instruction. An intrinsic's forms at 128, 256 and 512 bits share one definition, on a vector
of any number of lanes.

| Instruction | Intrinsics | Definition | Alive2 | InstCombine | A lane of the result is poison when |
| --- | --- | --- | --- | --- | --- |
| PMADDUBSW | `pmadd.ub.sw`, 3 forms | `X86.pmaddubsw` in [`X86.lean`](../IRLean/X86.lean) | Knows it | Folds it | One of the two bytes of either operand it sums is |
| PMADDWD | `pmadd.wd`, 3 | `X86.pmaddwd` | Knows it | Folds it | One of the two words of either operand it sums is |
| VPDPBUSD | `vpdpbusd`, 3 | `X86.vpdpbusd` | No | No | That lane of the accumulator is, or one of the four bytes of either operand it sums |
| VPTERNLOGD, VPTERNLOGQ | `pternlog`, 6 | `X86.pternlog` in [`X86Bits.lean`](../IRLean/X86Bits.lean) | Knows it | Folds it | That lane of any operand is, even one the truth table ignores |
| PSHUFB | `pshuf.b`, 3 | `X86.pshufb` | Knows it | Folds it | Its index is, or the byte the index picks, even where bit 7 makes it 0 |
| PSLLW to PSRAQ, and VPSLLVW to VPSRAVQ | The shifts, 83 | `X86.shiftImm`, `X86.shiftVec`, `X86.shiftLanes` | Knows them | Folds them | That lane is, or the count: a count in a vector's low 64 bits is poison when a lane in them is |
| PCLMULQDQ | `pclmulqdq`, 3 | `X86.pclmulqdq` in [`X86Crypto.lean`](../IRLean/X86Crypto.lean) | No | Only drops the quadwords it doesn't read | A quadword the immediate picks, in its 128-bit block, is. The other isn't read |
| AESENC, AESENCLAST, AESDEC, AESDECLAST | `aesni.aesenc`, `aesni.aesenclast`, `aesni.aesdec`, `aesni.aesdeclast`, 3 each | `X86.aesenc`, `X86.aesenclast`, `X86.aesdec`, `X86.aesdeclast` | No | No | Either quadword of that 128-bit block of the state is, since a round moves bytes between them, or that quadword of the round key |
| AESIMC, AESKEYGENASSIST | `aesni.aesimc`, `aesni.aeskeygenassist` | `X86.aesimc`, `X86.aeskeygenassist` | No | No | That quadword of the operand is |
| PAVGB, PAVGW | `pavg.b`, `pavg.w`, 3 each | `X86.pavg` in [`X86Arith.lean`](../IRLean/X86Arith.lean) | Knows them | No | That lane of either operand is |
| PACKSSWB, PACKSSDW, PACKUSWB, PACKUSDW | `packsswb`, `packssdw`, `packuswb`, `packusdw`, 3 each | `X86.packss`, `X86.packus` | Knows them | Folds them | The one lane it's the saturation of is |
| PSIGNB, PSIGNW, PSIGND | `psign.b`, `psign.w`, `psign.d`, 2 each | `X86.psign` | Knows them | No | That lane of either operand is, even where the second's is 0 and the result is 0 whatever the first's is |
| PMULHW, PMULHUW | `pmulh.w`, `pmulhu.w`, 3 each | `X86.pmulhw`, `X86.pmulhuw` | Knows them | Folds them | That lane of either operand is |
| PMULHRSW | `pmul.hr.sw`, 3 | `X86.pmulhrsw` | No | Folds it | That lane of either operand is |
| PSADBW | `psad.bw`, 3 | `X86.psadbw` | Knows it | No | Any of the eight bytes of either operand it sums the differences of is |
| VPDPBUSDS | `vpdpbusds`, 3 | `X86.vpdpbusds` | No | No | That lane of the accumulator is, or one of the four bytes of either operand it sums |
| VPDPWSSD, VPDPWSSDS | `vpdpwssd`, `vpdpwssds`, 3 each | `X86.vpdpwssd`, `X86.vpdpwssds` | No | No | That lane of the accumulator is, or one of the two words of either operand it sums |
| PHADDW, PHADDD, PHADDSW, PHSUBW, PHSUBD, PHSUBSW | `phadd.w`, `phadd.d`, `phadd.sw`, `phsub.w`, `phsub.d`, `phsub.sw`, 2 each | `X86.horizontal`, with the model's own `add`, `sub` and saturating ones | Knows them | No | One of the two neighbouring lanes it combines is |
| PBLENDVB | `sse41.pblendvb`, `avx2.pblendvb` | `X86.pblendvb` | The 256-bit form | Folds it | That byte of the mask or of either operand is, even the one the mask doesn't pick |
| BZHI, BEXTR | `bmi.bzhi`, `bmi.bextr`, 2 each | `X86.bzhi`, `X86.bextr` | No | Folds them | Either operand is. The result is one number |
| VPMOVDB to VPMOVWB, VPMOVSDB to VPMOVSWB, VPMOVUSDB to VPMOVUSWB, with a mask | `avx512.mask.pmov.*`, `avx512.mask.pmovs.*`, `avx512.mask.pmovus.*`, 50 | `X86.pmov`, `X86.pmovs`, `X86.pmovus` | No | No | The lane the mask picks for it is, of the source or of what's kept. The mask is one number: if it's poison every lane is, the ones the instruction zeroes too |
| PTEST | `sse41.ptestz`, `sse41.ptestc`, `sse41.ptestnzc`, and `avx.ptestz.256` and the like, 6 | `X86.ptestz`, `X86.ptestc`, `X86.ptestnzc` | No | No | Any lane of either operand is. The result is one flag |
| CRC32 | `sse42.crc32.32.8`, `.32.16`, `.32.32`, `.64.64` | `X86.crc32` | No | No | Either operand is |
| PHMINPOSUW | `sse41.phminposuw` | `X86.phminposuw` | No | No | Lanes 0 and 1, the least word and its index, when any lane of the operand is. The other six are 0, and never poison |
| GF2P8AFFINEQB, GF2P8AFFINEINVQB | `vgf2p8affineqb`, `vgf2p8affineinvqb`, 3 each | `X86.gf2p8affineqb`, `X86.gf2p8affineinvqb` in [`X86Crypto.lean`](../IRLean/X86Crypto.lean) | No | No | That byte of the first operand is, or any of the eight bytes of the quadword of the second, the matrix, that it's in |
| GF2P8MULB | `vgf2p8mulb`, 3 | `X86.gf2p8mulb` | No | No | That byte of either operand is |
| VZEROUPPER | `avx.vzeroupper` | None: the emitter drops the call | No | No | It has no result, and changes no value: [below](#vzeroupper) |

LangRef doesn't say what poison does to a target intrinsic. The last column is the model's rule, and
[trust](trust.md#known-gaps-in-the-model) says where it's the more poisonous of two readings.

### How each is checked

| Check | Test | What it shows | What has to fail |
| --- | --- | --- | --- |
| The processor | `x86native` | Every intrinsic at every form, on random lanes, lanes at the extremes, and every operand a splat of an extreme, each against each, gives what the instruction gives, lane for lane. The call runs in a function compiled without optimization, so nothing folds it | A wrong version of each definition, in [`tests/x86/Wrong.lean`](../tests/x86/Wrong.lean), a misreading of the pseudo-code: the processor has to disagree with it on some input to each intrinsic. And a modeled x86 intrinsic with no operation here |
| Alive2 | `x86check`, and `vecopcheck` for the bit functions | Where Alive2 knows the intrinsic, a call on constants and what the model gives refine each other both ways, poison lanes included | A changed result, and the wrong version's result, each of which Alive2 has to find incorrect. An intrinsic listed as unknown to Alive2 that it knows |
| InstCombine | The same | Where it folds a call on constants, every lane the model gives a value folds to that value. Where it only replaces operands, the model keeps every value on the operands it leaves | The wrong version, which the fold has to differ from, or which has to lose a value on the operands LLVM leaves. An intrinsic listed as not folded that folds |

Where neither Alive2 nor InstCombine computes an intrinsic, only the processor checks its values, and `x86check` prints
which those are, 99 of the 250: every row above with "No" under both. Their poison rules rest on the model's reading, and
for PCLMULQDQ on InstCombine's, which treats a quadword the immediate doesn't pick as one it may replace with poison.
The AES S-box and its inverse are tables, FIPS 197's, and `x86native` runs each round on every byte value, so every
entry is checked.

The forms on MMX's registers, 83 families such as `llvm.x86.mmx.padd.b` and `llvm.x86.ssse3.pshuf.b`, aren't modeled:
no project here calls one.

### VZEROUPPER

`llvm.x86.avx.vzeroupper` takes nothing and returns nothing. The instruction zeroes the upper halves of YMM0 to YMM15,
so that SSE code after it doesn't pay for switching from AVX. LLVM marks the intrinsic as having a side effect, so its
passes keep it. But no IR value is in one of those registers across it: `X86InstrSSE.td` gives VZEROUPPER all sixteen
as definitions, so the register allocator saves a live value around it, or keeps it in YMM16 and up, which the
instruction leaves alone. So the model does nothing for it, as for `llvm.donothing`. `x86native` runs both: 256-bit
values computed before a VZEROUPPER and used after it, in code compiled for AVX2 alone, where they're saved, and for
AVX-512, where they stay in registers, and both come out as the model says.

This is a choice, and [trust](trust.md#known-gaps-in-the-model) lists it: a rewrite that adds or drops a VZEROUPPER
refines in the model. The other choice is to refuse it, which keeps FLAC's integer residual kernels out, or to make it
an effect in a run's trace, which needs the memory lane's `Refines`.

## What it measured

On 2026-11-10, on z, with the model at 250 intrinsics:

| Test | Result |
| --- | --- |
| `x86native` | 250 intrinsics as 319 operations: 674,668 lanes of 45,726 results agree with the processor, with no mismatch, each pack and saturating move tried at its destination's limits and the values just past them, and the processor refutes the wrong version for all 249 that have one. About 11 s |
| `x86check` | 223 operations, the intrinsics and 32 bitcasts, on 16,572 inputs. InstCombine's folds agree on 60,042 lanes, refine the model's poison on 3,033, and on 1,438 inputs replace operands whose values the model keeps. Alive2 proves 4,953 of 4,953 inputs exact both ways, refuses a changed result for each operation, and refutes the wrong version of the 52 intrinsics it knows, as the folds do for the 36 InstCombine folds or rewrites. About 14 s |
| `x86` | 22 functions: 8,800 results agree with the processor |

```console
nix develop -c ctest --test-dir build -R '^(x86|x86native|x86check|x86_rank)$' -V
```

Before this, on 2026-11-09, the model had 99 of the 519, in 18 of the 55 families the projects call, with 54.8% of
the calls and 43.3% by share. PSHUFB, VPTERNLOG and the shifts had Alive2 and InstCombine behind them, and no check
against a processor. Now it has 249 of the 519, and VZEROUPPER, which isn't one of them: 52 of the 55 families, with
99.5% of the calls and 99.2% by share.

Three mistakes the checks caught while this was written, none in a definition: a wrong version of BZHI that shifted
by a 64-bit count, which ran Lean out of memory, `x86check`'s inputs as Lean literals, which Lean couldn't elaborate
in time, and the CRC32 instruction, which LLVM selects only under its own `crc32` feature. Every definition agreed
with the processor on its first run.

## Against the corpus lane's demand

The corpus lane measured the same thing another way, on 2026-11-10, in [the kernel corpus](kernels.md) and
`bench/kernels/results/demand.json`: the intrinsics called by the units that hold each candidate project's hot
kernels, for twelve projects, six of which the maintainer approved that day. Its counts quoted here are from its
first run, at `df3e997`. Its run after this page's intrinsics landed finds every one of them modeled, and every
`llvm.x86.*` call left in the ten projects it didn't reject working on floating-point values
([kernel corpus](kernels.md#the-x86-intrinsics)). This page counts every file ten
projects build. Seven projects are in both: llama.cpp, zlib-ng, libdeflate, zstd, libwebp, xxHash and libsodium. It
has base64, BLAKE3 at its default build, FLAC, Opus and XNNPACK besides, and this has ncnn, libaom and BLAKE3 from C.

**Where they agree.** The top of its demand, by calls, is the top of this ranking's unmodeled families as it stood on
2026-11-09, and all of it is modeled now:

| Its demand, with its calls | Rank here, before | Now |
| --- | --- | --- |
| `aesni.aesenc` 988, `aesni.aesenclast` 76, `aesni.aeskeygenassist` 13 | 4, 24, 19 | Modeled |
| `pclmulqdq` 586, `pclmulqdq.512` 64 | 1 | Modeled |
| `avx2.psign.b` 454, `ssse3.psign.w.128` 8 | 11, 29 | Modeled |
| The saturating packs, 303 | 8, 9, 14 | Modeled |
| `pmulh.w` and `pmulhu.w`, 133 | 17, 13 | Modeled |
| `pavg.b` and `psad.bw`, 125 | 7, 15 | Modeled |
| `avx512.mask.pmovs.db.512` 14, XNNPACK's | 18, from ncnn | Modeled |
| `ssse3.phadd.w.128` 7, `ssse3.phadd.d.128` 2 | 35, 22 | Modeled |

**Where they differ,** and what each says:

- **BZHI.** 7 calls there and 14 here, rank 32, 0.16% by share. But it's in zlib-ng's `chunkmemset_avx512`, in front
  of `inflate_fast_avx512`, which is 90% of zlib-ng's decompressing. So calls aren't how much hot time an intrinsic
  unblocks, and a ranking by calls puts it far too low. It's modeled, with BEXTR.
- **VZEROUPPER.** 4 calls, the first refusal on FLAC's integer residual kernels, whose other intrinsics the model
  had. It isn't in this ranking at all: it computes nothing, so it isn't one of the 519, and FLAC isn't one of the
  ten projects. It's modeled, [as a choice](#vzeroupper).
- **base64,** its project and not this page's: `avx.ptestz.256`, 28 calls, is modeled now, and
  `avx512.permvar.qi.512`, VPERMB, and `avx512.pmultishift.qb.512`, VPMULTISHIFTQB, 10 calls each, aren't. Neither
  has a call in this page's ten projects.
- **libaom and ncnn,** this page's and not its: PMULHRSW, PACKUSDW, PAVGW, VPDPWSSD, PBLENDVB, CRC32 and
  PHMINPOSUW have calls only there. Neither project is in the approved list, so nothing in the corpus needs them yet.
- **`llvm.pdep`,** 36 calls in llama.cpp. At this pin PDEP and PEXT reach IR as generic intrinsics, not as
  `llvm.x86.*`, so they aren't in this ranking, and the model refuses them as an integer operation it lacks.

So the ranking by share was right about what to model first, and wrong, by a long way, about BZHI. What the corpus
lane measures, the functions each refusal stands in front of, is the better order, now that the projects are approved.

## What's next

By the ranking, and whatever the corpus turns out to need once it's [fixed](roadmap.md#now-next-later):

- **What the corpus lane's projects still call:** VPERMB, `llvm.x86.avx512.permvar.qi.512`, and VPMULTISHIFTQB,
  `llvm.x86.avx512.pmultishift.qb.512`, in base64's AVX-512 codec, and `llvm.pdep` in llama.cpp, a generic intrinsic
  that BMI2's PDEP computes. z has the instruction set for each.
- **Can't be checked on z:** ncnn's VPMADCSWD and VPMACSWD are XOP, and its VPDPBSSD is AVX-VNNI-INT8. Zen 5 has
  neither, so they stay refused until there's a processor to check them on. They're the three families of the 55
  that aren't modeled.
- **No call in these projects, and likely in others:** PMOVMSKB where InstCombine can't fold it, the permutes VPERMD,
  VPERMW and VPERMI2, VPMADD52 for big-number arithmetic, SHA-NI, the multi-word adds ADDCARRY and SUBBORROW, and
  VZEROALL, which is VZEROUPPER's argument again.
- **Floating point waits:** `llvm.fma` and the `max.ps` and `min.ps` forms lead the last table of the ranking.
- **AArch64's NEON waits** until the results board exists.
