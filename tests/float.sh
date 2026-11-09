#!/usr/bin/env bash
# SEM-05's first slice, floating point's bit-level operations, on what ir-lean emits. Each rewrite in tests/float is
# translated, and tests/float/FloatModel.lean proves the case's verdict about it: it builds with warnings as errors,
# rests on the standard axioms and what `bv_decide` adds, and replays in the kernel. A proof that a wrong rewrite
# refines has to fail with an error of its own. Alive2 gives each case the same verdict. See docs/float.md.
# Bounded: one Lean or Alive2 process at a time, each Lean process with a memory cap and a time limit, writing only to
# a temporary directory. Needs `lake build`.
# usage: tests/float.sh path/to/ir-lean
set -euo pipefail
tool=$(realpath "$1")
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mb=${LEAN_MAX_MB:-2000}
secs=${FLOAT_TIMEOUT:-300}
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
limit='maximum number of heartbeats|\(deterministic\) timeout|maximum recursion depth|deep recursion|stack overflow|'
limit+='excessive memory|out of memory|maximum number of steps|The SAT solver timed out'

# Each case, as the module CASE_ir.
cases=(tests/float/*.ll)
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

# Every case has its theorem, and says its verdict in its name.
for file in "${cases[@]}"; do
  name=$(basename "$file" .ll)
  grep -q "^theorem $name :" tests/float/FloatModel.lean || fail "tests/float/FloatModel.lean has no theorem $name"
  case "$name" in
  *_right) head -1 "$file" | grep -qx '; correct' || fail "$file is named right but doesn't say correct" ;;
  *_wrong) head -1 "$file" | grep -qx '; incorrect' || fail "$file is named wrong but doesn't say incorrect" ;;
  *) fail "$file is named neither _right nor _wrong" ;;
  esac
done

# The theorems, with warnings as errors, on the standard axioms and bv_decide's, replayed in the kernel. A wrong
# case's theorem is a negation, `¬ Refines`.
built=0
if out=$(lean -DwarningAsError=true -R tests/float -o "$work/FloatModel.olean" tests/float/FloatModel.lean 2>&1); then
  printf 'ok    tests/float/FloatModel.lean\n'
  built=1
else
  fail 'tests/float/FloatModel.lean' "$out"
fi
for file in "${cases[@]}"; do
  name=$(basename "$file" .ll)
  case "$name" in
  *_wrong) grep -q "^theorem $name : ¬ Refines" tests/float/FloatModel.lean || fail "$name doesn't state ¬ Refines" ;;
  *_right) grep -q "^theorem $name : Refines" tests/float/FloatModel.lean || fail "$name doesn't state Refines" ;;
  esac
done
if [ "$built" = 1 ]; then
  if out=$(IRLEAN_CHECK_MODULE=FloatModel lean tests/check_axioms.lean 2>&1) &&
    replay=$(timeout "$secs" leanchecker FloatModel 2>&1); then
    printf 'ok    FloatModel: %s, and leanchecker replays it\n' "$out"
  else
    fail 'FloatModel: axioms and replay' "$out ${replay:-}"
  fi
fi

# A proof of a wrong rewrite has to fail to check, with an error of its own. An error at 1:0 is about its imports.
file=tests/float/must_fail/SelectZeroRefines.lean
status=0
out=$(lean -R tests/float/must_fail "$file" 2>&1) || status=$?
errors=$(grep -E "^$file:[0-9]+:[0-9]+: error" <<<"$out" | grep -v "^$file:1:0:" || true)
if [ "$translated" = 0 ]; then
  fail "$file can't be checked, since what it imports didn't compile"
elif [ "$status" = 0 ]; then
  fail "$file checks, so a wrong rewrite was certified" "$out"
elif [ -z "$errors" ] || ! grep -qvE "$limit" <<<"$errors"; then
  fail "$file stops only at a resource limit or never says why, which isn't a failure of its own" "$out"
else
  printf 'ok    %s fails: %s\n' "$file" "$(head -1 <<<"$errors" | cut -c1-200)"
fi

# Each case is LLVM IR, and Alive2's verdict on it is the theorem's: a proof for a right one and a counterexample for
# a wrong one.
for file in "${cases[@]}"; do
  if ! out=$(opt -passes=verify -disable-output "$file" 2>&1); then
    fail "$file isn't valid LLVM IR" "$out"
  fi
done
if ! tests/float_alive.py "${cases[@]}"; then
  failed=1
fi

exit "$failed"
