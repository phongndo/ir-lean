#!/usr/bin/env bash
# What ir-lean makes of LLVM's own pass code today: compiles 18 files of the pinned llvm-project, InstCombine's 15 and
# the three InstSimplify leans on most, with tests/llvm/targets.toml's flags for LLVM, runs `ir-lean --report` on each
# and on all of them linked, and counts the first reason each refused function gives. See docs/binding-approach.md.
#
# usage: prototypes/binding/census.sh IR_LEAN WORK_DIR
# Needs `nix develop`. Runs 4 clang processes at once, each up to about 2 GB, so it's a heavy run:
#   tools/measure.py run --label census --heavy --max-tree-rss-mb 12000 -- prototypes/binding/census.sh ...
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
irlean=$(realpath "$1")
work=$(mkdir -p "$2/census" && realpath "$2/census")
src=${LLVM_PROJECT_SRC:?run inside nix develop}

# The flags tests/llvm.py uses for LLVM's C++, so the two can't drift apart.
mapfile -t flags < <(python3 -I -c '
import sys, tomllib
f = tomllib.load(open(sys.argv[1], "rb"))["flags"]["llvm"]
print("\n".join(f["args"]))' "$root/tests/llvm/targets.toml")
pc=()
# shellcheck disable=SC2086 # PROOF_CFLAGS is several flags.
for f in $PROOF_CFLAGS; do [ "$f" = -isystem ] && pc+=(-idirafter) || pc+=("$f"); done
export work src root
compile() {
  clang "${pc[@]}" "${flags[@]}" -I"$src/llvm/include" -I"$(dirname "$1")" -I"$root/tests/llvm/include" \
    -I"$(llvm-config --includedir)" -S -emit-llvm -fno-discard-value-names -o "$work/$(basename "$1" .cpp).ll" "$1"
}
files=("$src"/llvm/lib/Transforms/InstCombine/*.cpp "$src/llvm/lib/Analysis/InstructionSimplify.cpp"
  "$src/llvm/lib/Analysis/ValueTracking.cpp" "$src/llvm/lib/Transforms/Scalar/InstSimplifyPass.cpp")
pids=()
for f in "${files[@]}"; do
  compile "$f" &
  pids+=($!)
  if [ ${#pids[@]} -ge 4 ]; then
    wait "${pids[0]}"
    pids=("${pids[@]:1}")
  fi
done
for p in "${pids[@]}"; do wait "$p"; done
llvm-link -S -o "$work/linked.ll" "$work"/[A-Z]*.ll

# One line per definition: its instructions, and whether it's a linkonce_odr copy.
sizes() {
  awk '/^define /{n=0; odr=($0 ~ / (linkonce|weak)_odr /); inside=1; next}
       inside && /^}/{print n, odr; inside=0; next}
       inside && /^  / && $1 !~ /^;/{n++}' "$1"
}
category() {
  sed 's/^in a cycle with a function that has //' | while IFS= read -r r; do
    case "$r" in
    "call to external @"*) echo "a call to a function outside the module" ;;
    *"whose definition may not be the one that runs"*) echo "a call to a linkonce_odr copy" ;;
    *"which isn't translated"*) echo "a call to a function itself refused" ;;
    "call attribute memory"*) echo "memory(...) on a call" ;;
    "metadata !nonnull"* | "metadata !range"*) echo "!nonnull or !range on a load" ;;
    "metadata !alias.scope"* | "metadata !noalias"*) echo "!alias.scope or !noalias" ;;
    "type "*) echo "a type" ;;
    "recursive function with more than"*) echo "a recursive function of more than 200 blocks" ;;
    "instruction "*) echo "an instruction" ;;
    *) echo "a global, intrinsic, vtable constant, attribute or undef" ;;
    esac
  done
}

total=0
ok=0
for f in "$work"/[A-Z]*.ll; do
  "$irlean" "$f" --report >"${f%.ll}.report" 2>/dev/null || [ $? -eq 3 ]
  total=$((total + $(grep -c -E '^(ok|unsupported)' "${f%.ll}.report")))
  ok=$((ok + $(grep -c '^ok' "${f%.ll}.report" || true)))
done
"$irlean" "$work/linked.ll" --report >"$work/linked.report" 2>/dev/null || [ $? -eq 3 ]

echo "C++ lines: InstCombine's .cpp files $(cat "$src"/llvm/lib/Transforms/InstCombine/*.cpp | wc -l)," \
  "with InstCombineInternal.h $(cat "$src"/llvm/lib/Transforms/InstCombine/*.{cpp,h} | wc -l)"
sizes "$work/linked.ll" | awk '{n++; i+=$1; odr+=$2; if ($1 > 1000) big++; if ($1 > max) max=$1}
  END {print "linked:", n, "functions,", odr, "linkonce_odr,", i, "IR instructions,", big+0,
    "over 1000, the largest", max}'
echo "translated file by file: $ok of $total"
echo "translated linked: $(grep -c '^ok' "$work/linked.report" || true) of $(grep -c -E '^(ok|unsupported)' "$work/linked.report")"
echo "distinct functions called outside the 18 files:" \
  "$(grep '^unsupported' "$work/linked.report" | cut -f3 | sed 's/^in a cycle with a function that has //' |
    sed -n 's/^call to external @//p' | sort -u | wc -l)"
echo "first refusals, linked:"
grep '^unsupported' "$work/linked.report" | cut -f3 | category | sort | uniq -c | sort -rn
