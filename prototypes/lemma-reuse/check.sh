#!/usr/bin/env bash
# PROTOTYPE, research only. Not part of CI, the build, or any claim in docs/status.md. See docs/lemma-reuse.md.
#
# Proves each goal in goals.toml from an empty store, in order, so later goals can reuse what earlier ones saved, and
# then again from the store that leaves, checking each saved lemma afresh, as a new checkout would. Fails if a goal
# isn't proved, if the search finds other rewrites than rewrites/ has, or if what's saved differs from store/ and
# proofs/.
#
# usage, inside `nix develop`, after `lake build` and building build/ir-lean:
#   prototypes/lemma-reuse/check.sh build/ir-lean [--write]
# `--write` replaces store/ and proofs/ with what this run saved, instead of comparing.
set -euo pipefail
tool=$(realpath "$1")
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=$root/build/lemma-reuse/check
rm -rf "$work"
mkdir -p "$work"
cd "$root"

for goal in popcountdi2_same popcountti2_same; do
  python3 "$here/lemmas.py" rewrite "$goal" --tool "$tool"
done

echo "From an empty store:"
python3 "$here/lemmas.py" prove --tool "$tool" --store "$work/store" --proofs "$work/proofs" --fresh --baseline \
  --alive 10000 --report "$work/empty.json"
echo
echo "Again, from what that saved:"
python3 "$here/lemmas.py" prove --tool "$tool" --store "$work/store" --proofs "$work/proofs-again" --fresh \
  --report "$work/again.json"
if ! diff -r "$work/proofs" "$work/proofs-again"; then
  echo "FAIL  the proofs from the store differ from the ones that filled it"
  exit 1
fi

# The store isn't trusted. A saved lemma that rests on an axiom of its own, rather than its proof, still checks,
# and has to stop the goal that uses it when its axioms are checked.
cp -r "$work/store" "$work/tampered"
python3 - "$work/tampered/Lemma_step_6934d83747.lean" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
text = path.read_text()
assert "  bv_decide (config := { timeout := 60 })" in text
text = text.replace("namespace LemmaReuse.Store\n", "namespace LemmaReuse.Store\n\naxiom trust_me {p : Prop} : p\n")
path.write_text(text.replace("  bv_decide (config := { timeout := 60 })", "  exact trust_me"))
PY
echo
echo "With a lemma in the store proved by an axiom:"
if python3 "$here/lemmas.py" prove popcountdi2_same --tool "$tool" --store "$work/tampered" \
  --proofs "$work/proofs-tampered" --fresh >"$work/tampered.log" 2>&1; then
  echo "FAIL  a goal resting on a lemma proved by an axiom passed"
  exit 1
elif ! grep -q "trust_me" "$work/tampered.log"; then
  echo "FAIL  a goal resting on a lemma proved by an axiom failed, but not because of the axiom:"
  cat "$work/tampered.log"
  exit 1
fi
echo "ok    the axiom stops the goal: $(grep -o "not an allowed axiom: .*" "$work/tampered.log" | head -1)"
echo

if [ "${2:-}" = --write ]; then
  rm -rf "$here/store" "$here/proofs"
  cp -r "$work/store" "$here/store"
  cp -r "$work/proofs" "$here/proofs"
  cp "$work/empty.json" "$here/report.json"
  echo "ok    wrote store/, proofs/ and report.json"
elif ! diff -r -x index.json "$here/store" "$work/store" || ! diff -r "$here/proofs" "$work/proofs"; then
  echo "FAIL  this run saved other lemmas or proofs than store/ and proofs/ have"
  exit 1
else
  echo "ok    the same lemmas and proofs as store/ and proofs/"
fi
