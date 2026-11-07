# Multi-IR prototype

**Prototype, for research only.** Nothing here is part of the `IRLean` library, the build or CI, and nothing here
is a claim in [status](../../docs/status.md). [Multi-IR](../../docs/multi-ir.md) says what it's for and what
it found.

| File | What it is |
| --- | --- |
| `example.c` | The minimal example: `popcount` and `pick` |
| `example.gimple` | GCC 16.2's `-fdump-tree-optimized-gimple` of it, which `MultiIR.lean` transcribes |
| `MultiIR.lean` | A small GIMPLE semantics, and seven theorems about both compilers' output |
| `check.sh` | Checks `MultiIR.lean` against fresh emitter output, and `example.gimple` against GCC |
| `mlir_roundtrip.sh` | Compares the emitter's Lean before and after a round trip through MLIR |
