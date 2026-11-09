#!/usr/bin/env bash
# Checks the generic-width rewrites in IRLean/Generic against the model, and that their tests can fail.
# Bounded: one Lean process at a time, each with a memory cap and a time limit, writing only to a temporary directory.
# The rewrites and the model modules they import are compiled there from copies, so Lake and .lake aren't used.
# usage: tests/generic_rewrites.sh   (in the dev shell, after nothing more than a checkout)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mb=${LEAN_MAX_MB:-2000}
secs=${GENERIC_REWRITES_TIMEOUT:-300}
export LEAN_PATH="$work"
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
limit+='excessive memory|out of memory|maximum number of steps'
model=(Attr Basic Int Refine)
rewrites=(Generic/BitVec Generic/Arith Generic/Bitwise)

# Copies the model's modules and the rewrites into DIR, with Int.lean from INT, and compiles the model and the rewrites
# named after INT, in order. Lean finds every IRLean module in the first directory on its path that has one, so DIR has
# its own.
# usage: build DIR INT [MODULE...] -- [LEAN_OPTION...]
build() {
  local dir=$1 int=$2 module out modules=()
  shift 2
  while [ "$#" -gt 0 ] && [ "$1" != -- ]; do
    modules+=("$1")
    shift
  done
  [ "$#" -gt 0 ] && shift
  mkdir -p "$dir/IRLean/Generic"
  for module in "${model[@]}" "${rewrites[@]}"; do
    cp "IRLean/$module.lean" "$dir/IRLean/$module.lean"
  done
  cp "$int" "$dir/IRLean/Int.lean"
  for module in "${model[@]}" "${modules[@]}"; do
    if ! out=$(LEAN_PATH="$dir" lean "$@" -R "$dir" -o "$dir/IRLean/$module.olean" "$dir/IRLean/$module.lean" 2>&1); then
      printf '%s\n' "$out"
      return 1
    fi
  done
}

# The rewrites themselves, with warnings as errors.
if out=$(build "$work" IRLean/Int.lean "${rewrites[@]}" -- -DwarningAsError=true 2>&1); then
  printf 'ok    IRLean.Generic builds\n'
else
  fail 'IRLean.Generic builds' "$out"
fi

# The tests, compiled to the temporary directory, with warnings as errors. The must-fail checks import the rewrites.
tests_built=1
for test in RewriteUse RewriteCounter; do
  if out=$(lean -DwarningAsError=true -R tests/generic_rewrites -o "$work/$test.olean" \
    "tests/generic_rewrites/$test.lean" 2>&1); then
    printf 'ok    tests/generic_rewrites/%s.lean\n' "$test"
  else
    fail "tests/generic_rewrites/$test.lean" "$out"
    tests_built=0
  fi
done

# Each rests on the standard axioms only, read as data by the checker tests/proofs.sh uses, and replays in the kernel.
for module in IRLean.Generic.Arith IRLean.Generic.Bitwise RewriteUse RewriteCounter; do
  if out=$(IRLEAN_CHECK_MODULE=$module lean tests/check_axioms.lean 2>&1) &&
    replay=$(timeout "$secs" leanchecker "$module" 2>&1); then
    printf 'ok    %s: %s, and leanchecker replays it\n' "$module" "$out"
  else
    fail "$module: axioms and replay" "$out ${replay:-}"
  fi
done

# A false rewrite has to fail to check, with an error of its own. An error at 1:0 is about its imports.
for file in tests/generic_rewrites/must_fail/AddSelfAnyWidth.lean tests/generic_rewrites/must_fail/MulTwoPowKeepsNsw.lean; do
  status=0
  out=$(lean -R tests/generic_rewrites/must_fail -o "$work/$(basename "$file" .lean).olean" "$file" 2>&1) || status=$?
  errors=$(grep -E "^$file:[0-9]+:[0-9]+: error" <<<"$out" | grep -v "^$file:1:0:" || true)
  if [ "$tests_built" = 0 ]; then
    fail "$file can't be checked, since what it imports didn't compile"
  elif [ "$status" = 0 ]; then
    fail "$file checks, so a false rewrite went through" "$out"
  elif [ -z "$errors" ] || ! grep -qvE "$limit" <<<"$errors"; then
    fail "$file stops only at a resource limit or never says why, which isn't a failure of its own" "$out"
  else
    printf 'ok    %s fails: %s\n' "$file" "$(head -1 <<<"$errors" | cut -c1-200)"
  fi
done

# A sorried rewrite compiles, and the axiom check has to refuse it.
file=tests/generic_rewrites/must_fail/SorriedRewrite.lean
if [ "$tests_built" = 0 ]; then
  fail "$file can't be checked, since what it imports didn't compile"
elif ! out=$(lean -R tests/generic_rewrites/must_fail -o "$work/SorriedRewrite.olean" "$file" 2>&1); then
  fail "$file doesn't compile, so the axiom check isn't what stops it" "$out"
elif out=$(IRLEAN_CHECK_MODULE=SorriedRewrite lean tests/check_axioms.lean 2>&1); then
  fail "$file passes the axiom check" "$out"
elif grep -q 'not an allowed axiom' <<<"$out"; then
  printf 'ok    %s is refused: %s\n' "$file" "$(grep -m1 'not an allowed axiom' <<<"$out" | cut -c1-200)"
else
  fail "$file fails the axiom check for another reason" "$out"
fi

# The declarations that the errors on standard input are in, one per line.
# usage: theorems_with_errors FILE
theorems_with_errors() {
  sed -nE 's/^.*:([0-9]+):[0-9]+: error.*$/\1/p' | sort -un | while read -r line; do
    awk -v n="$line" 'NR <= n && /^(private )?(theorem|def) / { t = $0 } NR == n { print t; exit }' "$1" |
      sed -E 's/^(private )?(theorem|def) ([^ ]+).*/\3/'
  done | sort -u
}

# Each mutant changes the model's own `IRLean/Int.lean` in a copy, the way a plausible edit could, and the rewrite module
# MODULE has to stop on it with an error of its own in THEOREM. This ties the rewrites to the definitions emitted code
# uses.
# usage: model_mutant NAME SED_EXPRESSION MODULE THEOREM
model_mutant() {
  local dir status=0 out errors hit
  dir=$(mktemp -d -p "$work")
  sed "$2" IRLean/Int.lean >"$dir/Int.lean"
  if cmp -s IRLean/Int.lean "$dir/Int.lean"; then
    fail "model mutant $1 doesn't change IRLean/Int.lean"
    return
  fi
  if ! out=$(build "$dir" "$dir/Int.lean" Generic/BitVec -- 2>&1); then
    fail "model mutant $1 doesn't compile, so it can't show anything" "$out"
    return
  fi
  out=$(LEAN_PATH="$dir" lean -R "$dir" "$dir/IRLean/Generic/$3.lean" 2>&1) || status=$?
  # Only errors that aren't resource limits count, so a theorem that only ran out of something isn't stopped.
  errors=$(grep -E "Generic/$3.lean:[0-9]+:[0-9]+: error" <<<"$out" | grep -vE "$limit" || true)
  if [ "$status" = 0 ]; then
    fail "model mutant $1 still meets every rewrite in $3"
  elif [ -z "$errors" ]; then
    fail "model mutant $1 stops $3 only at a resource limit, or never says why" "$out"
  elif ! hit=$(theorems_with_errors "$dir/IRLean/Generic/$3.lean" <<<"$errors" | grep -xF "$4"); then
    fail "model mutant $1 doesn't stop $4 with an error of its own, only $(theorems_with_errors \
      "$dir/IRLean/Generic/$3.lean" <<<"$errors" | tr '\n' ' ')" "$out"
  else
    printf 'ok    model mutant %s stops %s: %s\n' "$1" "$hit" "$(head -1 <<<"$errors" | sed "s|$dir/||" | cut -c1-120)"
  fi
}
# `or disjoint` never gives poison, so it can't be `add nuw nsw` where its operands share a bit.
model_mutant 'or ignores disjoint' \
  's/if disjoint \&\& x \&\&\& y != 0#w then none else some (x ||| y)/some (x ||| y)/' Arith or_disjoint_refines_add
# `mul nsw` checks unsigned overflow, a copy of the line above it.
model_mutant 'mul nsw checks unsigned' '/def mul /,/some (x \* y)/s/x\.smulOverflow y/x.umulOverflow y/' Arith mul_twoPow
# `udiv exact` is poison when the division is exact, the test the wrong way round.
model_mutant 'udiv exact inverted' 's/if exact \&\& x % y != 0#w/if exact \&\& x % y == 0#w/' Arith udiv_one
# `ashr` shifts in zeros, like `lshr`.
model_mutant 'ashr is logical' "/def ashr /,/else some/s/else some (x.sshiftRight' y)/else some (x >>> y)/" Bitwise \
  ashr_shl_nsw_refines
# `shl` by an amount out of range gives a value instead of poison.
model_mutant 'shl out of range' '/def shl /,/some (x <<< y)/s/if !shiftOk y then none/if false then none/' Bitwise shl_lshr

exit "$failed"
