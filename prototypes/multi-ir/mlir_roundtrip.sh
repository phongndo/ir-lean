#!/usr/bin/env bash
# PROTOTYPE, research only. Not part of CI, the build, or any claim in docs/status.md.
#
# Asks: if LLVM IR goes through MLIR's LLVM dialect and back (mlir-translate --import-llvm, then
# --mlir-to-llvmir), does ir-lean emit the same Lean? If not, a theorem about one isn't about the other.
# See docs/multi-ir.md.
#
# usage, inside `nix develop`:
#   prototypes/multi-ir/mlir_roundtrip.sh build/ir-lean OUT_DIR MLIR_BIN_DIR FILE.c...
#
# MLIR_BIN_DIR must hold an mlir-translate from the same LLVM release as the shell's clang. For LLVM 23.1.3:
#   nix build --no-link --print-out-paths github:NixOS/nixpkgs/<flake.lock rev>#llvmPackages_latest.mlir
set -euo pipefail
tool=$(realpath "$1")
out=$2
mlir=$3
shift 3
mkdir -p "$out"

for src in "$@"; do
  name=$(basename "${src%.c}")
  # No -fno-discard-value-names, since MLIR doesn't keep value names, and names would hide real differences.
  # shellcheck disable=SC2086
  clang $PROOF_CFLAGS -O2 -fno-strict-aliasing -S -emit-llvm -D_LARGEFILE64_SOURCE=1 -o "$out/$name.ll" "$src"
  if ! "$mlir/mlir-translate" --import-llvm "$out/$name.ll" -o "$out/$name.mlir" 2>"$out/$name.import.err"; then
    printf '%s\timport-failed\t%s\n' "$name" "$(head -1 "$out/$name.import.err")"
    continue
  fi
  "$mlir/mlir-translate" --mlir-to-llvmir "$out/$name.mlir" -o "$out/$name.rt.ll"
  for v in "$name" "$name.rt"; do
    "$tool" "$out/$v.ll" --report >"$out/$v.report" 2>/dev/null || true
    "$tool" "$out/$v.ll" --namespace "$name" --split "$out/$v.split" >/dev/null 2>&1 || true
  done
  # One line per function: its status on each side, and whether the emitted Lean is identical.
  while IFS=$'\t' read -r status llvm_name lean_name _; do
    case $status in translated*) continue ;; esac
    # For a function left out, the third field is the reason, so there's no Lean to compare.
    [ "$status" = ok ] || lean_name=
    rt_status=$(awk -F'\t' -v n="$llvm_name" '$2 == n { print $1 }' "$out/$name.rt.report")
    a="$out/$name.split/$name/$lean_name.lean"
    b="$out/$name.rt.split/$name/$lean_name.lean"
    if [ ! -e "$a" ] || [ ! -e "$b" ]; then
      same=n/a
    elif cmp -s "$a" "$b"; then
      same=identical
    else
      same="differs:$({ diff "$a" "$b" || true; } | grep -c '^[<>]')"
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$llvm_name" "$status" "${rt_status:-missing}" "$same"
  done <"$out/$name.report"
done
