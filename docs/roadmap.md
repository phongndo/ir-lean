# Roadmap

The goal is to find faster code in real hot kernels and prove in Lean that it refines what the compiler produced.
The target is ten measured, proved wins across at least three projects in the fixed corpus.

## The engine, changed on 2026-11-22

1. **Propose** a change to a hot kernel. A person, an offline agent or an upstream patch can supply it.
2. **Refute** wrong candidates with native comparisons and the project's own correctness checks.
3. **Measure** the surviving candidate against the pinned baseline using the [benchmark protocol](kernels.md#the-benchmark-protocol).
4. **Prove** refinement of the changed IR and replay the proof. Record whether the theorem covers a slice or the whole function.

The existing rule search supplies proofs when a step matches one of its rules. The [trust model](trust.md)
describes the boundary between a theorem about translated IR and a result about the compiled program.

## Checkpoint

By about **2026-12-09**, obtain one new proposer-found, measured and proved win in the corpus outside llama.cpp.
The two [llama.cpp case studies](status.md#llamacpp) are existing results. The consequence of missing the
checkpoint and the conditions under which those earlier rewrites count toward the ten remain open.

## Near-term pull requests

- Reproduce the libsodium Argon2 whole-function proof from the corpus pin. [Proof successor](https://github.com/phongndo/ir-lean/pull/131)
- Build the baseline and candidate as pinned Nix derivations. Read and validate their recorded observations in a
  separate change. [Builds](https://github.com/phongndo/ir-lean/pull/132) and [checker](https://github.com/phongndo/ir-lean/pull/133)
- Measure a validated candidate by the corpus protocol. The previous [harness](https://github.com/phongndo/ir-lean/pull/126)
  and [pilot](https://github.com/phongndo/ir-lean/pull/127) closed. Their timing records do not establish a win.

## The kernel corpus, decided on 2026-11-10

The approved projects are **llama.cpp, zlib-ng, xxHash, libsodium, FLAC and libwebp**.
The original approved digest is `d58e280b3e19bf21a75927a9ca408a695f4a52fb8bdfdfc97db3d8c685be45eb`.
The [manifest](../bench/kernels/manifest.toml) names this section. Amendments record their date, reason and
predecessor digest. The [corpus documentation](kernels.md) specifies workloads, checks and the criteria for a win.

The earlier phases, waves, supporting tracks and dated decisions remain in the [roadmap history](roadmap-history.md).
