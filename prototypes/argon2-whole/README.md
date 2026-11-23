# The Argon2 rotation proof

The patch changes which row rotates during the AVX-512 round in libsodium. The test fetches the source at
the kernel corpus's pin, configures it for the generated headers, and compiles the unit twice with the
corpus flags. Both runs use the same source path. Only the second uses the patched header.

For `fill_block_with_xor` and `argon2_fill_segment_avx512f`, Lean proves that a defined baseline return has
the same return and memory in the candidate. The statement also relates divergence through `Outcome.Sim`.
The proof uses the emitter and the project's LLVM semantics. It establishes refinement for the translated
functions. Performance requires a separate measurement.

LLVM reads the four changed regions and finds the operands entering each region and the values consumed
outside its pure instructions, including values written by stores. The 32 slice theorems prove lane equality.
The two whole-function proofs connect those equalities to each translated block and call. The test audits the
theorems' axioms, replays the proof modules with `leanchecker`, and checks four deliberately wrong candidates.

From the repository root on x86-64 Linux, in the development shell:

```sh
lake build
cmake -S . -B build -G Ninja
cmake --build build --target ir-lean argon2-slices
ctest --test-dir build -R '^argon2_whole$' --output-on-failure
```

The source and hash are in [the manifest](../../bench/kernels/manifest.toml). The header patch carries
[libsodium's license](LICENSE.libsodium).
