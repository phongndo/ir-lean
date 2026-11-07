#!/usr/bin/env bash
# PROTOTYPE, research only. Not part of CI, the build, or any claim in docs/status.md. See docs/multi-ir.md.
#
# Checks MultiIR.lean against freshly generated Lean for example.c, the way tests/proofs.sh does, without
# touching lakefile.toml. With GCC set, it also checks that GCC still prints the GIMPLE the Lean was
# transcribed from.
#
# usage, inside `nix develop`, after `lake build IRLean`:
#   [GCC=/path/to/gcc-16.2] prototypes/multi-ir/check.sh build/ir-lean
set -euo pipefail
tool=$(realpath "$1")
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

if [ -n "${GCC:-}" ]; then
  (cd "$work" && "$GCC" -O2 -fno-strict-aliasing -S -fdump-tree-optimized-gimple=example.gimple \
    "$here/example.c" -o /dev/null)
  if ! diff -u "$here/example.gimple" "$work/example.gimple"; then
    echo "FAIL  GCC's GIMPLE changed, so the transcription in MultiIR.lean is out of date"
    exit 1
  fi
  echo "ok    GIMPLE from $("$GCC" --version | head -1) matches example.gimple"
fi

# shellcheck disable=SC2086
clang $PROOF_CFLAGS -O2 -fno-strict-aliasing -S -emit-llvm -fno-discard-value-names -o "$work/example.ll" \
  "$here/example.c"
"$tool" "$work/example.ll" --namespace MultiIRExample -o "$work/MultiIRExample.lean"
export LEAN_PATH="$work:$root/.lake/build/lib/lean"
lean -R "$work" -o "$work/MultiIRExample.olean" "$work/MultiIRExample.lean"
lean "$here/MultiIR.lean" | tee "$work/out.txt"
if grep -q -E 'sorryAx|error' "$work/out.txt"; then
  echo "FAIL  MultiIR.lean"
  exit 1
fi
echo "ok    MultiIR.lean"
