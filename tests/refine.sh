#!/usr/bin/env bash
# Checks the refinement contract, IRLean/Refine.lean: its cases in tests/refine, and that those can fail.
# Bounded: one Lean process at a time, each with a memory cap and a time limit, writing only to a temporary directory.
# The model modules the cases import are compiled there from copies, so Lake and .lake aren't used.
# usage: tests/refine.sh   (in the dev shell, after nothing more than a checkout)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mb=${LEAN_MAX_MB:-2000}
secs=${REFINE_TIMEOUT:-300}
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
model=(Attr Basic Promise Int Mem Vec Lemmas Refine)

# Copies the modules the cases import into DIR, with MODULE.lean from FILE, and compiles them there. Lean finds every
# IRLean module in the first directory on its path that has one, so DIR has its own.
# usage: build_model DIR MODULE FILE [LEAN_OPTION...]
build_model() {
  local dir=$1 replaced=$2 file=$3 module out
  shift 3
  mkdir -p "$dir/IRLean"
  for module in "${model[@]}"; do
    cp "IRLean/$module.lean" "$dir/IRLean/"
  done
  cp "$file" "$dir/IRLean/$replaced.lean"
  for module in "${model[@]}"; do
    if ! out=$(LEAN_PATH="$dir" lean "$@" -R "$dir" -o "$dir/IRLean/$module.olean" "$dir/IRLean/$module.lean" 2>&1); then
      printf '%s\n' "$out"
      return 1
    fi
  done
}

# The contract and the modules it's used with, with warnings as errors.
if out=$(build_model "$work" Int IRLean/Int.lean -DwarningAsError=true 2>&1); then
  printf 'ok    IRLean.Refine builds\n'
else
  fail 'IRLean.Refine builds' "$out"
fi

# The cases, and what has a claim, with warnings as errors. The must-fail checks import the cases.
tests_built=0
if out=$(lean -DwarningAsError=true -R tests/refine -o "$work/RefineCases.olean" tests/refine/RefineCases.lean 2>&1) &&
  out=$(lean -DwarningAsError=true -R tests/refine -o "$work/RefineClaims.olean" \
    tests/refine/RefineClaims.lean 2>&1); then
  printf 'ok    tests/refine/RefineCases.lean and RefineClaims.lean\n'
  tests_built=1
else
  fail 'tests/refine' "$out"
fi

# Each rests on the standard axioms only, read as data by the checker tests/proofs.sh uses, and replays in the kernel.
for module in IRLean.Refine IRLean.Promise RefineCases; do
  if out=$(IRLEAN_CHECK_MODULE=$module lean tests/check_axioms.lean 2>&1) &&
    replay=$(timeout "$secs" leanchecker "$module" 2>&1); then
    printf 'ok    %s: %s, and leanchecker replays it\n' "$module" "$out"
  else
    fail "$module: axioms and replay" "$out ${replay:-}"
  fi
done

# A proof of a wrong rewrite has to fail to check, with an error of its own. An error at 1:0 is about its imports.
file=tests/refine/must_fail/WrongConstantProof.lean
status=0
out=$(lean -R tests/refine/must_fail -o "$work/WrongConstantProof.olean" "$file" 2>&1) || status=$?
errors=$(grep -E "^$file:[0-9]+:[0-9]+: error" <<<"$out" | grep -v "^$file:1:0:" || true)
if [ "$tests_built" = 0 ]; then
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

# The declarations that the errors on standard input are in, one per line.
# usage: theorems_with_errors FILE
theorems_with_errors() {
  sed -nE 's/^.*:([0-9]+):[0-9]+: error.*$/\1/p' | sort -un | while read -r line; do
    awk -v n="$line" 'NR <= n && /^(private )?(theorem|def) / { t = $0 } NR == n { print t; exit }' "$1" |
      sed -E 's/^(private )?(theorem|def) ([^ ]+).*/\3/'
  done | sort -u
}

# Each mutant changes one of the model's own modules in a copy, the way a plausible edit could, so that a wrong rewrite
# would refine, or a right one wouldn't. The cases have to stop on it, at the theorem guarding that rewrite, with an
# error of its own.
# usage: model_mutant NAME MODULE SED_EXPRESSION THEOREM
model_mutant() {
  local name=$1 module=$2 edit=$3 theorem=$4 dir status=0 out errors hit
  dir=$(mktemp -d -p "$work")
  sed "$edit" "IRLean/$module.lean" >"$dir/$module.lean"
  if cmp -s "IRLean/$module.lean" "$dir/$module.lean"; then
    fail "model mutant $name doesn't change IRLean/$module.lean"
    return
  fi
  if ! out=$(build_model "$dir" "$module" "$dir/$module.lean" 2>&1); then
    fail "model mutant $name doesn't compile, so it can't show anything" "$out"
    return
  fi
  cp tests/refine/RefineCases.lean "$dir/"
  out=$(LEAN_PATH="$dir" lean -R "$dir" "$dir/RefineCases.lean" 2>&1) || status=$?
  errors=$(grep -E "RefineCases.lean:[0-9]+:[0-9]+: error" <<<"$out" | grep -vE "$limit" || true)
  if [ "$status" = 0 ]; then
    fail "model mutant $name still meets every case"
  elif [ -z "$errors" ]; then
    fail "model mutant $name stops the cases only at a resource limit, or never says why" "$out"
  elif ! hit=$(theorems_with_errors "$dir/RefineCases.lean" <<<"$errors" | grep -xF "$theorem"); then
    fail "model mutant $name doesn't stop $theorem with an error of its own, only $(theorems_with_errors \
      "$dir/RefineCases.lean" <<<"$errors" | tr '\n' ' ')" "$out"
  else
    printf 'ok    model mutant %s stops %s: %s\n' "$name" "$hit" "$(head -1 <<<"$errors" | sed "s|$dir/||" | cut -c1-120)"
  fi
}
# `freeze` of poison gives poison instead of a value, so removing a `freeze` would refine.
model_mutant 'freeze keeps poison' Int 's/^  | none => some (BitVec.ofNat w pick)$/  | none => none/' freezeRemoved
# `freeze` of poison is always 0, as VeIR has it, instead of a value the run chooses. Freezing once and twice would
# then agree, though LLVM may freeze poison to two different values.
model_mutant 'freeze always picks 0' Int 's/^  | none => some (BitVec.ofNat w pick)$/  | none => some 0#w/' \
  freezeDuplicated
# `add` ignores `nuw`, so adding the flag would change nothing.
model_mutant 'add ignores nuw' Int '/def add /,/some (x + y)/s/if (nuw \&\& x.uaddOverflow y) || /if /' addedNuw
# A run that stays in a promised loop for good never finishes, as it did before SEM-07, instead of being undefined, so
# deleting the loop would be wrong. The laws that pin this choice in IRLean/Promise.lean would fail first, so the copy
# leaves them out.
model_mutant 'a broken promise never finishes' Promise \
  's/^  | none => Outcome.ub .noProgress$/  | none => none/; /^section Laws$/,/^end Laws$/d' countPromised_odd

exit "$failed"
