#!/usr/bin/env bash
# Every identifier-like token in Lean's table has to be reserved, or a value named after one (zlib has
# a `matches`) produces Lean that doesn't parse.
# usage: tests/names.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cat >"$work/tokens.lean" <<'LEAN'
import IRLean
import Lean
open Lean Parser
#eval show CoreM Unit from do
  let toks := (getTokenTable (← getEnv)).values.filter fun s =>
    !s.isEmpty && (s.front.isAlpha || s.front == '_') && s.all (fun c => c.isAlphanum || c == '_')
  IO.println (" ".intercalate toks.toList)
LEAN
missing=0
for token in $(LEAN_PATH="$root/.lake/build/lib/lean" lean "$work/tokens.lean"); do
  if ! grep -q "\"$token\"" "$root/src/Emitter.cpp"; then
    printf 'not reserved: %s\n' "$token"
    missing=1
  fi
done
exit $missing
