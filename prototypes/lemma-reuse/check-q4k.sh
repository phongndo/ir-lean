#!/usr/bin/env bash
# PROTOTYPE, research only. Not part of CI, the build, or any claim in docs/status.md. See docs/lemma-reuse.md.
#
# Proves the 34 places of llama.cpp's q4_K kernels from an empty store, in order, so later places can reuse what
# earlier ones saved, and then again from the store that leaves, checking each saved lemma afresh. Fails if a place
# isn't proved, if a slice differs from the branch's manifest, or if what's saved differs from q4k/store and
# q4k/proofs.
#
# The q4_K proof is on feat/prove-llvm-optimization-1, which isn't merged. Run this in a built checkout of it, in
# its dev shell:
#   git worktree add --detach ../q4k origin/feat/prove-llvm-optimization-1
#   cd ../q4k && nix develop -c bash -c 'lake build && cmake -S . -B build -G Ninja && ninja -C build'
#   nix develop -c /path/to/prototypes/lemma-reuse/check-q4k.sh . [--write]
# `--write` replaces q4k/store, q4k/proofs and q4k/report.json with what this run saved, instead of comparing.
set -euo pipefail
repo=$(realpath "$1")
here=$(cd "$(dirname "$0")" && pwd)
work=$repo/build/lemma-reuse-q4k/check
rm -rf "$work"
mkdir -p "$work"

echo "From an empty store:"
python3 "$here/q4k.py" --repo "$repo" --store "$work/store" --proofs "$work/proofs" --fresh \
  --report "$work/empty.json"
echo
echo "Again, from what that saved:"
python3 "$here/q4k.py" --repo "$repo" --store "$work/store" --proofs "$work/proofs-again" --fresh \
  --report "$work/again.json"
if ! diff -r "$work/proofs" "$work/proofs-again"; then
  echo "FAIL  the proofs from the store differ from the ones that filled it"
  exit 1
fi
if ! grep -q '"slices_matching_manifest": "68 of 68"' "$work/empty.json"; then
  echo "FAIL  the slices aren't the ones the branch's manifest records"
  exit 1
fi

if [ "${2:-}" = --write ]; then
  rm -rf "$here/q4k/store" "$here/q4k/proofs"
  mkdir -p "$here/q4k"
  cp -r "$work/store" "$here/q4k/store"
  cp -r "$work/proofs" "$here/q4k/proofs"
  cp "$work/empty.json" "$here/q4k/report.json"
  echo "ok    wrote q4k/store, q4k/proofs and q4k/report.json"
elif ! diff -r -x index.json "$here/q4k/store" "$work/store" || ! diff -r "$here/q4k/proofs" "$work/proofs"; then
  echo "FAIL  this run saved other lemmas or proofs than q4k/store and q4k/proofs have"
  exit 1
else
  echo "ok    the same lemmas and proofs as q4k/store and q4k/proofs"
fi
