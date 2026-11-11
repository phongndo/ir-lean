#!/usr/bin/env bash
# `Refines` for functions with memory, SEM-06, on what ir-lean emits. Each rewrite in tests/memory_refine is
# translated, and tests/memory_refine/MemoryRefine.lean proves the case's verdict about it: it builds with warnings as
# errors, rests on the standard axioms, and replays in the kernel. A proof that a wrong rewrite refines has to fail
# with an error of its own, and so does each of the relation's rules, changed in a copy of IRLean/MemRefine.lean.
# Alive2 gives each case the verdict the case says, through tests/calls_alive.py. See docs/refinement.md.
# Bounded: one Lean or Alive2 process at a time, each Lean process with a memory cap and a time limit, writing only to
# a temporary directory. Needs `lake build`.
# usage: tests/memory_refine.sh path/to/ir-lean
set -euo pipefail
tool=$(realpath "$1")
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mb=${LEAN_MAX_MB:-2000}
secs=${MEMORY_REFINE_TIMEOUT:-300}
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
limit+='excessive memory|out of memory|maximum number of steps'

# The relation and what keeps it: on the standard axioms alone, replayed in the kernel.
if out=$(IRLEAN_CHECK_MODULE=IRLean.MemRefine lean tests/check_axioms.lean 2>&1) &&
  grep -q 'and 0 from bv_decide' <<<"$out" && replay=$(timeout "$secs" leanchecker IRLean.MemRefine 2>&1); then
  printf 'ok    IRLean.MemRefine: %s, and leanchecker replays it\n' "$out"
else
  fail 'IRLean.MemRefine: axioms and replay' "$out ${replay:-}"
fi

# Each case, as the module CASE_ir.
cases=(tests/memory_refine/*.ll)
translated=1
theorems=
generated=
for file in "${cases[@]}"; do
  name=$(basename "$file" .ll)
  if ! out=$("$tool" "$file" -o "$work/${name}_ir.lean" --namespace "${name}_ir" --no-code 2>&1) ||
    ! out=$(lean -R "$work" -o "$work/${name}_ir.olean" "$work/${name}_ir.lean" 2>&1); then
    fail "$file doesn't translate and compile" "$out"
    translated=0
  fi
  generated+="${name}_ir "
  theorems+="$name ${name}_ir.src"$'\n'"$name ${name}_ir.tgt"$'\n'
done
[ "$translated" = 1 ] && printf 'ok    %s cases translated\n' "${#cases[@]}"

# Every case has its theorem, and is LLVM IR.
for file in "${cases[@]}"; do
  name=$(basename "$file" .ll)
  grep -q "^theorem $name :" tests/memory_refine/MemoryRefine.lean ||
    fail "tests/memory_refine/MemoryRefine.lean has no theorem $name"
  out=$(opt -passes=verify -disable-output "$file" 2>&1) || fail "$file isn't valid LLVM IR" "$out"
done

# The theorems, with warnings as errors, each about its case's two functions as ir-lean emitted them, on the standard
# axioms, replayed in the kernel.
built=0
if out=$(lean -DwarningAsError=true -R tests/memory_refine -o "$work/MemoryRefine.olean" \
  tests/memory_refine/MemoryRefine.lean 2>&1); then
  printf 'ok    tests/memory_refine/MemoryRefine.lean\n'
  built=1
else
  fail 'tests/memory_refine/MemoryRefine.lean' "$out"
fi
if [ "$built" = 1 ]; then
  if out=$(IRLEAN_CHECK_MODULE=MemoryRefine IRLEAN_CHECK_GENERATED=${generated% } IRLEAN_CHECK_THEOREMS=${theorems%$'\n'} \
    lean tests/check_axioms.lean 2>&1) && grep -q 'and 0 from bv_decide' <<<"$out" &&
    replay=$(timeout "$secs" leanchecker MemoryRefine 2>&1); then
    printf 'ok    MemoryRefine: %s, and leanchecker replays it\n' "$out"
  else
    fail 'MemoryRefine: axioms and replay' "$out ${replay:-}"
  fi
fi

# What the errors on standard input are in, one declaration per line.
# usage: theorems_with_errors FILE
theorems_with_errors() {
  sed -nE 's/^.*:([0-9]+):[0-9]+: error.*$/\1/p' | sort -un | while read -r line; do
    awk -v n="$line" 'NR <= n && /^(private )?(theorem|def) / { t = $0 } NR == n { print t; exit }' "$1" |
      sed -E 's/^(private )?(theorem|def) ([^ ]+).*/\3/'
  done | sort -u
}

# FILE has to fail to check, at THEOREM, with an error that isn't a resource limit. An error at 1:0 is about its
# imports.
# usage: must_fail WHAT FILE THEOREM
must_fail() {
  local what=$1 file=$2 theorem=$3 status=0 out errors hit
  out=$(lean -R "$(dirname "$file")" "$file" 2>&1) || status=$?
  errors=$(grep -E "^$file:[0-9]+:[0-9]+: error" <<<"$out" | grep -v "^$file:1:0:" | grep -vE "$limit" || true)
  if [ "$status" = 0 ]; then
    fail "$what checks, so something wrong was certified" "$out"
  elif [ -z "$errors" ]; then
    fail "$what stops only at a resource limit, at its imports, or never says why" "$out"
  elif ! hit=$(theorems_with_errors "$file" <<<"$errors" | grep -xF "$theorem"); then
    fail "$what doesn't stop $theorem with an error of its own, only $(theorems_with_errors "$file" <<<"$errors" |
      tr '\n' ' ')" "$out"
  else
    printf 'ok    %s stops %s: %s\n' "$what" "$hit" "$(head -1 <<<"$errors" | sed "s|$work/||" | cut -c1-140)"
  fi
}

# A proof that a wrong rewrite refines: the forwarding proof, about a store that's removed.
if [ "$built" = 1 ]; then
  must_fail 'a proof that removing a store a load reads refines' \
    tests/memory_refine/must_fail/StoreRemovedRefines.lean store_removed_refines
else
  fail "the false proof can't be checked, since what it imports didn't build"
fi

# A wrong relation. Each mutant changes one of its rules in a copy of IRLean/MemRefine.lean, so that something wrong
# would be allowed, and the law that pins the rule has to stop on it.
# usage: relation_mutant NAME SED_EXPRESSION THEOREM
relation_mutant() {
  local dir
  dir=$(mktemp -d -p "$work")
  sed "$2" IRLean/MemRefine.lean >"$dir/MemRefine.lean"
  if cmp -s IRLean/MemRefine.lean "$dir/MemRefine.lean"; then
    fail "relation mutant $1 doesn't change IRLean/MemRefine.lean"
    return
  fi
  must_fail "relation mutant $1" "$dir/MemRefine.lean" "$3"
}
# LLVM reads an uninitialized byte as `undef`, which poison doesn't refine.
relation_mutant 'an uninitialized byte allows poison' 's/^  | .uninit, b => b ≠ .poison$/  | .uninit, _ => True/' \
  not_uninit_le_poison
# A target could then leave any byte where the source left a value.
relation_mutant 'a byte of a value allows any byte' 's/^  | .val x, b => b = .val x$/  | .val _, _ => True/' val_le_iff
# A target could then return a pointer into another allocation.
relation_mutant 'a pointer allows any pointer' 's/^    | some p => b = some p$/    | some _ => True/' ptr_some
# The two sides could then number their allocations differently, which nothing here relates.
relation_mutant 'memories need not agree on the next allocation' '/^  next : m'"'"'.next = m.next$/d' next_eq

# Alive2 gives each case the verdict the case says it does.
if ! tests/calls_alive.py tests/memory_refine tests/memory_refine/MemoryRefine.lean; then
  failed=1
fi

exit "$failed"
