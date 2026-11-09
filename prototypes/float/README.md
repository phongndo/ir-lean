# Floating point: the spike

The measurements behind [floating point's design](../../docs/float.md). Nothing here is the model, and nothing in
`IRLean` imports it.

| File | What it is |
| --- | --- |
| [`FloatSpike.lean`](FloatSpike.lean) | `fadd`, `fsub`, `fmul`, `fdiv` and `fcmp` as circuits on bit vectors, for every format, with LangRef's NaN results as a choice |
| [`SpikeCheck.lean`](SpikeCheck.lean) | Checks them against Lean's `Float.Model` on every pair of five small formats, and the processor on sampled pairs |
| [`spike.py`](spike.py) | Times `bv_decide` on nine theorems about them at each format, each in a capped process of its own |
| [`spike-results.jsonl`](spike-results.jsonl) | What `spike.py` recorded on y on 2026-11-09, which the design's table is |
| [`coverage.py`](coverage.py) | Runs an emitter again on the pairs stage 1 saved, and counts what it translates |

In `nix develop`, from the repository's root:

```sh
lean -o /tmp/f/FloatSpike.olean prototypes/float/FloatSpike.lean
LEAN_PATH=/tmp/f lean --run prototypes/float/SpikeCheck.lean 2000   # about 30 s
prototypes/float/spike.py /tmp/spike.jsonl --timeout 300 --memory 8000 --formats half float double
```
