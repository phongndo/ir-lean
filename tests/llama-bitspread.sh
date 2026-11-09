#!/usr/bin/env bash
# Checks the exact q5_0 integer slice without downloading or running a model.
# usage: tests/llama-bitspread.sh path/to/ir-lean
set -euo pipefail
tool=$(realpath "$1")
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work:$root/.lake/build/lib/lean"
lean() { command lean -M "${LEAN_MAX_MB:-4000}" "$@"; }
fixture=$root/tests/real/llama_q5_bitspread.ll
proof=$root/tests/proofs/LlamaBitspread.lean

opt -passes=verify -disable-output "$fixture"
"$tool" "$fixture" --namespace LlamaBitspreadIR --no-code -o "$work/LlamaBitspreadIR.lean"
lean -DwarningAsError=true -R "$work" -o "$work/LlamaBitspreadIR.olean" "$work/LlamaBitspreadIR.lean"
lean -DwarningAsError=true -R "$root/tests/proofs" -o "$work/LlamaBitspread.olean" "$proof"
# The axioms, reading the proof and what it imports as data, as tests/proofs.sh does, and that `same` is about
# both helpers as ir-lean generated them. Then the kernel replays it, since Lean code can add a declaration it
# never checked.
axioms=$(IRLEAN_CHECK_MODULE=LlamaBitspread IRLEAN_CHECK_GENERATED=LlamaBitspreadIR \
  IRLEAN_CHECK_THEOREMS=$'same LlamaBitspreadIR.src\nsame LlamaBitspreadIR.tgt' \
  lean "$root/tests/check_axioms.lean")
leanchecker LlamaBitspread
printf 'ok    exact q5_0 slice: same successful result, with defined bytes for every defined input (axioms: %s)\n' \
  "$axioms"

# A valid but wrong replacement: output lane zero reads input bit one instead of bit zero.
# Keep the source unchanged, and check the same proof against newly generated mutant Lean.
mkdir "$work/mutant"
python3 - "$fixture" "$work/mutant/input.ll" "$proof" "$work/mutant/LlamaBitspread.lean" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text()
head, tail = source.split("define <32 x i8> @tgt", 1)
mask = ", ".join(f"i32 {1 if i == 0 else i}" for i in range(32))
wrong = (
    "  %wrong = shufflevector <32 x i1> %mask, <32 x i1> poison, "
    f"<32 x i32> <{mask}>\n"
)
assert tail.count("  %out = select") == 1
assert tail.count("select <32 x i1> %mask,") == 1
tail = tail.replace("  %out = select", wrong + "  %out = select")
tail = tail.replace("select <32 x i1> %mask,", "select <32 x i1> %wrong,")
Path(sys.argv[2]).write_text(head + "define <32 x i8> @tgt" + tail)

# Check the unchanged equivalence proof. The later target-specific simplification lemmas do not
# need to be rechecked after the prover has already exhibited a wrong result.
proof = Path(sys.argv[3]).read_text()
prefix, _ = proof.split("\nprivate theorem select_byte", 1)
Path(sys.argv[4]).write_text(prefix + "\nend LlamaBitspread\n")
PY
opt -passes=verify -disable-output "$work/mutant/input.ll"
"$tool" "$work/mutant/input.ll" --namespace LlamaBitspreadIR --no-code -o "$work/mutant/LlamaBitspreadIR.lean"
export LEAN_PATH="$work/mutant:$root/.lake/build/lib/lean"
lean -DwarningAsError=true -R "$work/mutant" -o "$work/mutant/LlamaBitspreadIR.olean" \
  "$work/mutant/LlamaBitspreadIR.lean"
if lean -DwarningAsError=true "$work/mutant/LlamaBitspread.lean" >"$work/mutant/rejection.log" 2>&1; then
  printf 'FAIL  the wrong-bit replacement proved\n'
  exit 1
fi
if ! grep -q 'The prover found a counterexample' "$work/mutant/rejection.log" ||
  grep -Eq 'timeout|maximum number of heartbeats' "$work/mutant/rejection.log"; then
  cat "$work/mutant/rejection.log"
  printf 'FAIL  the mutant failed for a reason other than its wrong result\n'
  exit 1
fi
printf 'ok    wrong-bit replacement rejected with a counterexample\n'
