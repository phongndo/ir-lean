#!/usr/bin/env bash
# Translates all of real zlib, checks how much translates, and compares it against native code.
# usage: tests/zlib.sh path/to/llvm-lean [differential.py arguments]
# The arguments choose what to run. `--only harness_` is the harness, which can call zlib's functions
# with real pointers, and `harness_slow` is the part of it that takes minutes per call.
set -euo pipefail
tool=$(realpath "$1")
shift
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

zlib_src=${ZLIB_SRC:-$(nix build --inputs-from "$root" --no-link --print-out-paths nixpkgs#zlib.src)}
mkdir "$work/zlib"
tar -xf "$zlib_src" -C "$work/zlib" --strip-components=1

# The library itself. The gz* files are left out: they're a layer over file descriptors.
for f in adler32 compress crc32 deflate infback inffast inflate inftrees trees uncompr zutil; do
  clang -O2 -S -emit-llvm -fno-discard-value-names -D_LARGEFILE64_SOURCE=1 -I"$work/zlib" \
    -o "$work/$f.ll" "$work/zlib/$f.c"
done
clang -O2 -S -emit-llvm -fno-discard-value-names -I"$work/zlib" \
  -o "$work/harness.ll" "$root/tests/real/zlib_harness.c"
llvm-link -S -o "$work/zlib.ll" "$work"/*.ll

"$tool" "$work/zlib.ll" --report > "$work/report"
tail -1 "$work/report"
grep '^unsupported' "$work/report" || true
ok=$(grep -c '^ok' "$work/report")
total=$(($(wc -l < "$work/report") - 1))
if [ $((ok * 10)) -lt $((total * 9)) ]; then
  printf 'FAIL  under 90%% of zlib translates\n'
  exit 1
fi

"$root/tests/differential.py" "$tool" "$work/zlib.ll" --split --strict "$@"
