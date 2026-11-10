#!/usr/bin/env bash
# Checks the semantic contracts in IRLean/Contract against the model, and that their tests can fail.
# Bounded: one Lean process at a time, each with a memory cap and a time limit, writing only to a temporary directory.
# The contracts and the model modules they import are compiled there from copies, so Lake and .lake aren't used.
# usage: tests/contracts.sh   (in the dev shell, after nothing more than a checkout)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mb=${LEAN_MAX_MB:-2000}
secs=${CONTRACTS_TIMEOUT:-300}
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
limit='maximum number of heartbeats|deterministic\)? timeout|maximum recursion depth|deep recursion|stack overflow|'
limit+='excessive memory|out of memory|maximum number of steps'

# Copies the model's modules the contracts import into DIR, with Int.lean from INT, and compiles them there. Lean finds
# every IRLean module in the first directory on its path that has one, so DIR has its own.
# usage: build_model DIR INT [LEAN_OPTION...]
build_model() {
  local dir=$1 int=$2 module out
  shift 2
  mkdir -p "$dir/IRLean/Contract"
  cp IRLean/Attr.lean IRLean/Basic.lean "$dir/IRLean/"
  cp "$int" "$dir/IRLean/Int.lean"
  cp IRLean/Contract/Poison.lean "$dir/IRLean/Contract/Poison.lean"
  for module in Attr Basic Int; do
    if ! out=$(LEAN_PATH="$dir" lean "$@" -R "$dir" -o "$dir/IRLean/$module.olean" "$dir/IRLean/$module.lean" 2>&1); then
      printf '%s\n' "$out"
      return 1
    fi
  done
}

# The contracts themselves, with warnings as errors.
if out=$(build_model "$work" IRLean/Int.lean -DwarningAsError=true 2>&1) &&
  out=$(lean -DwarningAsError=true -R "$work" -o "$work/IRLean/Contract/Poison.olean" \
    "$work/IRLean/Contract/Poison.lean" 2>&1); then
  printf 'ok    IRLean.Contract.Poison builds\n'
else
  fail 'IRLean.Contract.Poison builds' "$out"
fi

# The tests, compiled to the temporary directory, with warnings as errors. The must-fail checks import them.
tests_built=0
if out=$(lean -DwarningAsError=true -R tests/contracts -o "$work/ContractPoison.olean" \
  tests/contracts/ContractPoison.lean 2>&1); then
  printf 'ok    tests/contracts/ContractPoison.lean\n'
  tests_built=1
else
  fail 'tests/contracts/ContractPoison.lean' "$out"
fi

# Both rest on the standard axioms only, read as data by the checker tests/proofs.sh uses, and replay in the kernel.
for module in IRLean.Contract.Poison ContractPoison; do
  if out=$(IRLEAN_CHECK_MODULE=$module lean tests/check_axioms.lean 2>&1) &&
    replay=$(timeout "$secs" leanchecker "$module" 2>&1); then
    printf 'ok    %s: %s, and leanchecker replays it\n' "$module" "$out"
  else
    fail "$module: axioms and replay" "$out ${replay:-}"
  fi
done

# A false contract has to fail to check, with an error of its own. An error at 1:0 is about its imports.
file=tests/contracts/must_fail/LaxSdivProof.lean
status=0
out=$(lean -R tests/contracts/must_fail -o "$work/LaxSdivProof.olean" "$file" 2>&1) || status=$?
errors=$(grep -E "^$file:[0-9]+:[0-9]+: error" <<<"$out" | grep -v "^$file:1:0:" || true)
if [ "$tests_built" = 0 ]; then
  fail "$file can't be checked, since what it imports didn't compile"
elif [ "$status" = 0 ]; then
  fail "$file checks, so a false contract went through" "$out"
elif [ -z "$errors" ] || ! grep -qvE "$limit" <<<"$errors"; then
  fail "$file stops only at a resource limit or never says why, which isn't a failure of its own" "$out"
elif grep -qiE 'unknown (identifier|constant|tactic|namespace)|unexpected (token|identifier)' <<<"$errors"; then
  fail "$file fails because the proof text can't be read (a renamed or removed name), not because the contract is wrong" "$out"
else
  printf 'ok    %s fails: %s\n' "$file" "$(head -1 <<<"$errors" | cut -c1-200)"
fi

# A sorried contract compiles, and the axiom check has to refuse it.
file=tests/contracts/must_fail/SorriedContract.lean
if [ "$tests_built" = 0 ]; then
  fail "$file can't be checked, since what it imports didn't compile"
elif ! out=$(lean -R tests/contracts/must_fail -o "$work/SorriedContract.olean" "$file" 2>&1); then
  fail "$file doesn't compile, so the axiom check isn't what stops it" "$out"
elif out=$(IRLEAN_CHECK_MODULE=SorriedContract lean tests/check_axioms.lean 2>&1); then
  fail "$file passes the axiom check" "$out"
elif grep -q 'not an allowed axiom' <<<"$out"; then
  printf 'ok    %s is refused: %s\n' "$file" "$(grep -m1 'not an allowed axiom' <<<"$out" | cut -c1-200)"
else
  fail "$file fails the axiom check for another reason" "$out"
fi

# Each mutant changes the model's own `IRLean/Int.lean` in a copy, the way a plausible edit could, and the contract module
# has to stop on it with an error of its own. This ties the contracts to the definitions emitted code uses.
# usage: model_mutant NAME SED_EXPRESSION THEOREM
model_mutant() {
  local dir status=0 out errors
  dir=$(mktemp -d -p "$work")
  sed "$2" IRLean/Int.lean >"$dir/Int.lean"
  if cmp -s IRLean/Int.lean "$dir/Int.lean"; then
    fail "model mutant $1 doesn't change IRLean/Int.lean"
    return
  fi
  if ! out=$(build_model "$dir" "$dir/Int.lean" 2>&1); then
    fail "model mutant $1 doesn't compile, so it can't show anything" "$out"
    return
  fi
  out=$(LEAN_PATH="$dir" lean -R "$dir" "$dir/IRLean/Contract/Poison.lean" 2>&1) || status=$?
  # Only errors that aren't resource limits count, so a theorem that only ran out of something isn't stopped.
  errors=$(grep -E "Contract/Poison.lean:[0-9]+:[0-9]+: error" <<<"$out" | grep -vE "$limit" || true)
  if [ "$status" = 0 ]; then
    fail "model mutant $1 still meets every contract"
  elif [ -z "$errors" ]; then
    fail "model mutant $1 stops the contracts only at a resource limit, or never says why" "$out"
  elif ! hit=$(theorems_with_errors "$dir/IRLean/Contract/Poison.lean" <<<"$errors" | grep -xF "$3"); then
    fail "model mutant $1 doesn't stop $3 with an error of its own, only $(theorems_with_errors \
      "$dir/IRLean/Contract/Poison.lean" <<<"$errors" | tr '\n' ' ')" "$out"
  else
    printf 'ok    model mutant %s stops %s: %s\n' "$1" "$hit" "$(head -1 <<<"$errors" | sed "s|$dir/||" | cut -c1-120)"
  fi
}

# The declarations that the errors on standard input are in, one per line.
# usage: theorems_with_errors FILE
theorems_with_errors() {
  sed -nE 's/^.*:([0-9]+):[0-9]+: error.*$/\1/p' | sort -un | while read -r line; do
    awk -v n="$line" 'NR <= n && /^(private )?(theorem|def) / { t = $0 } NR == n { print t; exit }' "$1" |
      sed -E 's/^(private )?(theorem|def) ([^ ]+).*/\3/'
  done | sort -u
}
# Less undefined behavior than LangRef: a poison dividend of a signed division by -1 isn't undefined.
model_mutant 'lax poison dividend' 's/^  | none => y == BitVec.allOnes w$/  | none => false/' sdiv_poisonUB
# A poison divisor of `udiv` gives poison, where LangRef lists it as undefined.
model_mutant 'udiv poison divisor' '/def udiv/,/divByPoison/s/Outcome.ub .divByPoison/Outcome.ok none/' udiv_poisonUB
# `add`'s flags give 0 instead of poison, changing a value.
model_mutant 'add flag gives zero' '/def add /,/some (x + y)/s/then none else some (x + y)/then some 0#w else some (x + y)/' add_onlyPoisons
# `add` without flags gives poison on unsigned overflow, as if `nuw` were always there.
model_mutant 'add always nuw' '/def add /,/some (x + y)/s/if (nuw \&\& x.uaddOverflow y)/if (x.uaddOverflow y)/' add_noPoison
# `and` with zero absorbs poison.
model_mutant 'and absorbs poison' 's/^@\[llvm\] def and : Val w → Val w → Val w := map₂ (· \&\&\& ·)$/@[llvm] def and (a b : Val w) : Val w := if b == some 0#w then some 0#w else map₂ (· \&\&\& ·) a b/' and_strict

exit "$failed"
