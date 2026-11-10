#!/usr/bin/env bash
# Calls outside the module, on what ir-lean emits. Each rewrite in tests/calls is translated, and
# tests/calls/CallsModel.lean proves the case's verdict about it: it builds with warnings as errors, rests on the
# standard axioms, and replays in the kernel. A proof that a wrong rewrite refines has to fail with an error of its own.
# Alive2 gives each case the verdict the case says, through tests/calls_alive.py. See docs/calls.md.
# Bounded: one Lean or Alive2 process at a time, each Lean process with a memory cap and a time limit, writing only to
# a temporary directory. Needs `lake build`.
# usage: tests/calls.sh path/to/ir-lean
set -euo pipefail
tool=$(realpath "$1")
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mb=${LEAN_MAX_MB:-2000}
secs=${CALLS_TIMEOUT:-300}
export LEAN_PATH="$work:$root/.lake/build/lib/lean"
lean_bin=$(command -v lean)
lean() { timeout "$secs" "$lean_bin" -M "$mb" "$@"; }
failed=0
fail() {
  printf 'FAIL  %s\n' "$1"
  [ -n "${2:-}" ] && printf '%s\n' "${2:0:4000}"
  failed=1
}
# Resource limits say a proof might check with more, so they never count as a failure of its own.
limit='maximum number of heartbeats|deterministic\)? timeout|maximum recursion depth|deep recursion|stack overflow|'
limit+='excessive memory|out of memory|maximum number of steps'

# Each case, as the module CASE_ir.
cases=(tests/calls/*.ll)
translated=1
for file in "${cases[@]}"; do
  name=$(basename "$file" .ll)
  if ! out=$("$tool" "$file" -o "$work/${name}_ir.lean" --namespace "${name}_ir" --no-code 2>&1) ||
    ! out=$(lean -R "$work" -o "$work/${name}_ir.olean" "$work/${name}_ir.lean" 2>&1); then
    fail "$file doesn't translate and compile" "$out"
    translated=0
  fi
done
[ "$translated" = 1 ] && printf 'ok    %s cases translated\n' "${#cases[@]}"

# Every case has its theorem, and is LLVM IR.
for file in "${cases[@]}"; do
  name=$(basename "$file" .ll)
  grep -q "^theorem $name :" tests/calls/CallsModel.lean || fail "tests/calls/CallsModel.lean has no theorem $name"
  out=$(opt -passes=verify -disable-output "$file" 2>&1) || fail "$file isn't valid LLVM IR" "$out"
done

# The theorems, with warnings as errors, on the standard axioms, replayed in the kernel.
built=0
if out=$(lean -DwarningAsError=true -R tests/calls -o "$work/CallsModel.olean" tests/calls/CallsModel.lean 2>&1); then
  printf 'ok    tests/calls/CallsModel.lean\n'
  built=1
else
  fail 'tests/calls/CallsModel.lean' "$out"
fi
if [ "$built" = 1 ]; then
  if out=$(IRLEAN_CHECK_MODULE=CallsModel lean tests/check_axioms.lean 2>&1) &&
    replay=$(timeout "$secs" leanchecker CallsModel 2>&1); then
    printf 'ok    CallsModel: %s, and leanchecker replays it\n' "$out"
  else
    fail 'CallsModel: axioms and replay' "$out ${replay:-}"
  fi
fi

# A proof of a wrong rewrite has to fail to check, with an error of its own. An error at 1:0 is about its imports.
file=tests/calls/must_fail/PureDuplicatedRefines.lean
status=0
out=$(lean -R tests/calls/must_fail "$file" 2>&1) || status=$?
errors=$(grep -E "^$file:[0-9]+:[0-9]+: error" <<<"$out" | grep -v "^$file:1:0:" || true)
if [ "$translated" = 0 ]; then
  fail "$file can't be checked, since what it imports didn't compile"
elif [ "$status" = 0 ]; then
  fail "$file checks, so a wrong rewrite was certified" "$out"
elif [ -z "$errors" ] || ! grep -qvE "$limit" <<<"$errors"; then
  fail "$file stops only at a resource limit or never says why, which isn't a failure of its own" "$out"
elif grep -qiE 'unknown (identifier|constant|tactic|namespace)|unexpected (token|identifier)' <<<"$errors"; then
  fail "$file fails because the proof text can't be read (a renamed or removed name), not because the rewrite is wrong" "$out"
else
  printf 'ok    %s fails: %s\n' "$file" "$(head -1 <<<"$errors" | cut -c1-200)"
fi

# Alive2 gives each case the verdict the case says it does.
if ! tests/calls_alive.py; then
  failed=1
fi

exit "$failed"
