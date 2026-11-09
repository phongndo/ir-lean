#!/usr/bin/env bash
# Checks the experimental undef and freeze semantics in IRLean/Experimental, its tests, that they can fail, and that
# Alive2 gives the same verdict on the rewrites they judge. See docs/undef-freeze.md.
# Bounded: one Lean or Alive2 process at a time, each Lean process with a memory cap and a time limit, writing only to
# a temporary directory. The module and the model modules it imports are compiled there from copies, so Lake and
# .lake aren't used.
# usage: tests/undef_freeze.sh   (in the dev shell, after nothing more than a checkout)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mb=${LEAN_MAX_MB:-2000}
secs=${UNDEF_FREEZE_TIMEOUT:-300}
export LEAN_PATH="$work"
lean_bin=$(command -v lean)
lean() { timeout "$secs" "$lean_bin" -M "$mb" "$@"; }
module=IRLean/Experimental/UndefFreeze.lean
tests=tests/undef_freeze/UndefFreezeTests.lean
failed=0
fail() {
  printf 'FAIL  %s\n' "$1"
  [ -n "${2:-}" ] && printf '%s\n' "${2:0:4000}"
  failed=1
}
# Resource limits say a proof might check with more, so they never count as a failure of its own.
limit='maximum number of heartbeats|\(deterministic\) timeout|maximum recursion depth|deep recursion|stack overflow|'
limit+='excessive memory|out of memory|maximum number of steps'

# Copies the model's modules the prototype imports into DIR, with the prototype from SOURCE, and compiles them there.
# Lean finds every IRLean module in the first directory on its path that has one, so DIR has its own. The prototype's
# errors, if any, are left in DIR/module.out.
# usage: build DIR SOURCE [LEAN_OPTION...]
build() {
  local dir=$1 source=$2 m out
  shift 2
  mkdir -p "$dir/IRLean/Experimental"
  cp IRLean/Attr.lean IRLean/Basic.lean IRLean/Int.lean "$dir/IRLean/"
  cp "$source" "$dir/$module"
  for m in Attr Basic Int; do
    if ! out=$(LEAN_PATH="$dir" lean "$@" -R "$dir" -o "$dir/IRLean/$m.olean" "$dir/IRLean/$m.lean" 2>&1); then
      printf '%s\n' "$out"
      return 1
    fi
  done
  LEAN_PATH="$dir" lean "$@" -R "$dir" -o "$dir/IRLean/Experimental/UndefFreeze.olean" "$dir/$module" \
    >"$dir/module.out" 2>&1
}

# The declarations that the errors on standard input are in, one per line.
# usage: theorems_with_errors FILE
theorems_with_errors() {
  sed -nE 's/^.*:([0-9]+):[0-9]+: error.*$/\1/p' | sort -un | while read -r line; do
    awk -v n="$line" 'NR <= n && /^(private )?(theorem|def) / { t = $0 } NR == n { print t; exit }' "$1" |
      sed -E 's/^(private )?(theorem|def) ([^ ]+).*/\3/'
  done | sort -u
}

# The prototype, with warnings as errors.
if build "$work" "$module" -DwarningAsError=true; then
  printf 'ok    IRLean.Experimental.UndefFreeze builds\n'
else
  fail 'IRLean.Experimental.UndefFreeze builds' "$(cat "$work/module.out" 2>/dev/null)"
fi

# Its tests, compiled to the temporary directory, with warnings as errors. The must-fail checks import them.
tests_built=0
if out=$(lean -DwarningAsError=true -R tests/undef_freeze -o "$work/UndefFreezeTests.olean" "$tests" 2>&1); then
  printf 'ok    %s\n' "$tests"
  tests_built=1
else
  fail "$tests" "$out"
fi

# Both rest on the standard axioms, and on bv_decide's, which the checker reruns, and both replay in the kernel.
for m in IRLean.Experimental.UndefFreeze UndefFreezeTests; do
  if out=$(IRLEAN_CHECK_MODULE=$m lean tests/check_axioms.lean 2>&1) &&
    replay=$(timeout "$secs" leanchecker "$m" 2>&1); then
    printf 'ok    %s: %s, and leanchecker replays it\n' "$m" "$out"
  else
    fail "$m: axioms and replay" "$out ${replay:-}"
  fi
done

# Each false claim has to fail to check, with an error of its own. An error at 1:0 is about its imports.
for file in tests/undef_freeze/must_fail/{FreezeDuplicatedRight,Mul2ToAddSelfRight}.lean; do
  status=0
  out=$(lean -R tests/undef_freeze/must_fail "$file" 2>&1) || status=$?
  errors=$(grep -E "^$file:[0-9]+:[0-9]+: error" <<<"$out" | grep -v "^$file:1:0:" || true)
  if [ "$tests_built" = 0 ]; then
    fail "$file can't be checked, since what it imports didn't compile"
  elif [ "$status" = 0 ]; then
    fail "$file checks, so a false claim went through" "$out"
  elif [ -z "$errors" ] || ! grep -qvE "$limit" <<<"$errors"; then
    fail "$file stops only at a resource limit or never says why, which isn't a failure of its own" "$out"
  else
    printf 'ok    %s fails: %s\n' "$file" "$(head -1 <<<"$errors" | cut -c1-200)"
  fi
done

# A sorried claim compiles, and the axiom check has to refuse it.
file=tests/undef_freeze/must_fail/SorriedClaim.lean
if [ "$tests_built" = 0 ]; then
  fail "$file can't be checked, since what it imports didn't compile"
elif ! out=$(lean -R tests/undef_freeze/must_fail -o "$work/SorriedClaim.olean" "$file" 2>&1); then
  fail "$file doesn't compile, so the axiom check isn't what stops it" "$out"
elif out=$(IRLEAN_CHECK_MODULE=SorriedClaim lean tests/check_axioms.lean 2>&1); then
  fail "$file passes the axiom check" "$out"
elif grep -q 'not an allowed axiom' <<<"$out"; then
  printf 'ok    %s is refused: %s\n' "$file" "$(grep -m1 'not an allowed axiom' <<<"$out" | cut -c1-200)"
else
  fail "$file fails the axiom check for another reason" "$out"
fi

# Each mutant changes a copy of the prototype into a semantics LangRef rules out, and THEOREM, which is false under
# it, has to stop with an error of its own. THEOREM is in the prototype, or in its tests if the mutant still builds.
# usage: mutant NAME SED_EXPRESSION THEOREM
mutant() {
  local dir status=0 out errors file=$module hit
  dir=$(mktemp -d -p "$work")
  sed "$2" "$module" >"$dir/mutant.lean"
  if cmp -s "$module" "$dir/mutant.lean"; then
    fail "mutant $1 doesn't change $module"
    return
  fi
  if ! out=$(build "$dir" "$dir/mutant.lean" 2>&1); then
    if [ ! -f "$dir/module.out" ]; then
      fail "mutant $1: the model didn't compile" "$out"
      return
    fi
    status=1
    out=$(cat "$dir/module.out")
  else
    file=$tests
    out=$(LEAN_PATH="$dir" lean -R tests/undef_freeze "$tests" 2>&1) || status=$?
  fi
  # Only errors that aren't resource limits count, so a theorem that only ran out of something isn't stopped.
  errors=$(grep -E "^[^:]*${file##*/}:[0-9]+:[0-9]+: error" <<<"$out" | grep -vE "$limit" || true)
  if [ "$status" = 0 ]; then
    fail "mutant $1 still passes every test"
  elif [ -z "$errors" ]; then
    fail "mutant $1 stops only at a resource limit, or never says why" "$out"
  elif ! hit=$(error_in "$file" "$3" <<<"$errors"); then
    fail "mutant $1 doesn't stop $3 with an error of its own, only $(theorems_with_errors "$file" <<<"$errors" |
      tr '\n' ' ')" "$out"
  else
    hit=${hit//"$dir/"/}
    printf 'ok    mutant %s stops %s: %s\n' "$1" "$3" "${hit:0:140}"
  fi
}

# The first error on standard input that's in the declaration NAME of FILE, or a failure if there's none.
# usage: error_in FILE NAME
error_in() {
  local line
  while IFS= read -r line; do
    if [ "$(theorems_with_errors "$1" <<<"$line")" = "$2" ]; then
      printf '%s\n' "$line"
      return 0
    fi
  done
  return 1
}
undef_line='^def undef : UVal w := fun e => ∃ x, e = some x$'
# `undef` that can be poison: then poison would be a correct replacement for it.
mutant 'undef includes poison' "s/$undef_line/def undef : UVal w := fun _ => True/" undef_to_poison_wrong
# `undef` as one value, 0, the same at every use: then `add %w, %w` would never be odd.
mutant 'undef is zero' "s/$undef_line/def undef : UVal w := fun e => e = some 0/" langref_freeze_y_odd
# `freeze` of poison with no result, as the model's stop was until F3: then a target that freezes poison would refine
# anything.
mutant 'freeze of poison stops' 's/(a (some x) ∨ a none) ∧ r = UVal.const x/a (some x) ∧ r = UVal.const x/' \
  freeze_total
# `freeze` drawn again at each use, so it fixes nothing: then a frozen poison would still differ between uses.
mutant 'freeze per use' \
  's/∃ x, (a (some x) ∨ a none) ∧ r = UVal.const x/r = fun e => ∃ x, (a (some x) ∨ a none) ∧ e = some x/' \
  freeze_of_none
# A value that allows poison: then refinement wouldn't be transitive.
mutant 'value allows poison' 's/^  | some x, b => b = some x$/  | some x, b => b = some x ∨ b = none/' ValLe.trans

# Each rewrite that's LLVM IR passes LLVM's verifier, and Alive2's verdict on it is the theorem's.
for file in tests/undef_freeze/alive2/*.ll; do
  if ! out=$(opt -passes=verify -disable-output "$file" 2>&1); then
    fail "$file isn't valid LLVM IR" "$out"
  fi
done
if ! tests/undef_freeze_alive.py; then
  failed=1
fi

exit "$failed"
