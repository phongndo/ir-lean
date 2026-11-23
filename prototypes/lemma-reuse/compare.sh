#!/usr/bin/env bash
# Replay the retirement audit against the archived inputs and original store in a temporary checkout.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
mkdir "$out/source"
git -C "$here/../.." archive b0b8b1d4158dec7afd4e578d35da97d915edc245 | tar -x -C "$out/source"
cd "$out/source"
lake build IRLean LemmaStore StoreTool Peephole
export LEAN_PATH="$PWD/.lake/build/lib/lean"

# usage: compile ROOT FILE...
compile() {
  local dir=$1 f
  shift
  for f in "$@"; do
    lean -M 3000 -R "$dir" -o "$LEAN_PATH/$(basename "$f" .lean).olean" "$f"
  done
}
compile tests/llvm tests/llvm/Bits.lean
compile prototypes/lemma-reuse prototypes/lemma-reuse/Count.lean
compile prototypes/lemma-reuse/store prototypes/lemma-reuse/store/Lemma_*.lean
compile tests/llama tests/llama/Vnni.lean
compile prototypes/lemma-reuse/q4k/store prototypes/lemma-reuse/q4k/store/Lemma_*.lean

# usage: group NAME NAMESPACE FILE... : judges the theorems the files declare, under NAMESPACE, and writes
# $out/NAME.json. A refusal exits 2, which is what's expected here; anything else but 0 is an error.
group() {
  local name=$1 ns=$2 f lemmas=() imports=() status=0
  shift 2
  for f in "$@"; do
    imports+=(--import "$(basename "$f" .lean)")
    while read -r t; do lemmas+=("$ns.$t"); done < <(sed -nE 's/^theorem ([^ ]+).*/\1/p' "$f")
  done
  tools/store/store.py add --existing "${lemmas[@]}" "${imports[@]}" --family lemma-reuse \
    --provenance "prototypes/lemma-reuse, $name" --dry-run --json >"$out/$name.json" || status=$?
  if [ "$status" != 0 ] && [ "$status" != 2 ]; then
    echo "FAIL  $name: store.py add exited $status"
    cat "$out/$name.json"
    exit 1
  fi
}
group population-counts LemmaReuse.Store prototypes/lemma-reuse/store/Lemma_*.lean
group seed-lemmas LemmaReuse prototypes/lemma-reuse/Count.lean
group bits Llvm.Bits tests/llvm/Bits.lean
group q4k LemmaReuse.Store prototypes/lemma-reuse/q4k/store/Lemma_*.lean

python3 - "$out" >"$out/against-store.json" <<'PY'
import json
import sys
from pathlib import Path

out = Path(sys.argv[1])
groups = {}
for name in ("population-counts", "seed-lemmas", "bits", "q4k"):
    result = json.loads((out / f"{name}.json").read_text())
    lemmas = {
        lemma["name"]: {"status": lemma["status"], "reasons": sorted({r["code"] for r in lemma["reasons"]})}
        for lemma in result["lemmas"]
    }
    counts = {}
    for lemma in lemmas.values():
        counts[lemma["status"]] = counts.get(lemma["status"], 0) + 1
        for code in lemma["reasons"]:
            counts[code] = counts.get(code, 0) + 1
    groups[name] = {"counts": dict(sorted(counts.items())), "lemmas": dict(sorted(lemmas.items()))}
print(json.dumps({"schema": "ir-lean.lemma-reuse.against-store/1", "groups": groups}, indent=2))
PY

diff -u "$here/against-store.json" "$out/against-store.json"
