#!/usr/bin/env bash
# Gate B1, BIND-04 for reading IR: IRLean/LLVMHeap.lean builds with warnings as errors, a heap built byte by byte
# meets its view and keeps it through ConstantInt::get, every theorem rests on the standard axioms, leanchecker
# replays both, and the layout probe, built with the numbers Lean prints from IRLean.LLVMHeap, agrees with objects
# the pinned libLLVM builds. See docs/llvm-heap.md.
#
# usage: tests/llvm_heap.sh
# Needs `nix develop`. Each Lean process is capped by its -M.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$root/build"
# Under the repo, so elan finds its toolchain from any directory in it.
work=$(mktemp -d "$root/build/llvm-heap.XXXXXX")
trap 'rm -rf "$work"' EXIT
memory=${LEAN_MEMORY_MB:-2000}
cd "$root"

lake build --wfail IRLean.LLVMHeap
export LEAN_PATH="$root/.lake/build/lib/lean:$work"
cp tests/llvm_heap/ViewExample.lean "$work/"
(cd "$work" && lean -j1 -M "$memory" -DwarningAsError=true -R . -o ViewExample.olean ViewExample.lean)
echo "ok   lean: IRLean.LLVMHeap and the example check with warnings as errors, on the standard axioms"
(cd "$work" && leanchecker IRLean.LLVMHeap ViewExample)
echo "ok   leanchecker replays IRLean.LLVMHeap and the example"

read -r -a facts < <(lean -M "$memory" tests/llvm_heap/Facts.lean)
[ "${#facts[@]}" -gt 20 ] || {
  echo "FAIL the layout Lean printed: ${facts[*]}" >&2
  exit 1
}
mapfile -t llvm < <(llvm-config --cxxflags --ldflags --libs core | tr ' ' '\n' | grep -v '^$')
clang++ tests/llvm_heap/layout_probe.cpp "${facts[@]}" "${llvm[@]}" -o "$work/layout_probe"
"$work/layout_probe" | tee "$work/probe.log" | grep -v '^ok' || true
grep -q '^0 failed$' "$work/probe.log" || exit 1
echo "ok   layout: $(grep -c '^ok' "$work/probe.log") facts hold on the pinned libLLVM"

# The probe has to catch a wrong number: the same build, with the ConstantInt's word one field off.
wrong=("${facts[@]/#-DLAYOUT_CONST_WORD=*/-DLAYOUT_CONST_WORD=16}")
clang++ tests/llvm_heap/layout_probe.cpp "${wrong[@]}" "${llvm[@]}" -o "$work/wrong_probe"
if "$work/wrong_probe" >"$work/wrong.log"; then
  echo "FAIL the probe passes with a ConstantInt's word at offset 16" >&2
  exit 1
fi
grep -q '^FAIL .*ConstantInt::get makes ID 5' "$work/wrong.log" || {
  echo "FAIL the probe with a wrong offset didn't fail where it should" >&2
  exit 1
}
echo "ok   the probe fails with a ConstantInt's word one field off"
