#!/usr/bin/env bash
# E2, the memory tests run on: IRLean/ExecMem.lean. Each operation on it is proved to agree with `Mem`'s, on the
# standard axioms, with no `implemented_by` or `extern`, and the module replays in the kernel. A wrong version of each
# operation has to stop the proof of that operation's own theorem. Every operation on memory the emitter prints has
# an `ExecMem` version, and `ir-lean --executable-memory` prints the Lean proofs are about with only `Mem` renamed,
# which checks. docs/memory.md#executable-memory says why that makes a test on `ExecMem` a test of `Mem`.
# Bounded: one Lean process at a time, each with a memory cap and a time limit, writing only to a temporary
# directory. Needs `lake build`.
# usage: tests/exec_memory.sh path/to/ir-lean
set -uo pipefail
tool=$(realpath "$1")
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root" || exit 1
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mb=${LEAN_MAX_MB:-2000}
secs=${EXEC_MEMORY_TIMEOUT:-300}
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
file=IRLean/ExecMem.lean

# The module, on the standard axioms, with nothing compiled that the kernel didn't check, replayed in the kernel.
if out=$(IRLEAN_CHECK_MODULE=IRLean.ExecMem lean tests/check_axioms.lean 2>&1) &&
  grep -q 'and 0 from bv_decide' <<<"$out" && replay=$(timeout "$secs" leanchecker IRLean.ExecMem 2>&1); then
  printf 'ok    IRLean.ExecMem: %s, and leanchecker replays it\n' "$out"
else
  fail 'IRLean.ExecMem: axioms and replay' "$out ${replay:-}"
fi

# Every operation on memory the emitter prints, as `ExecMem`'s, so `--executable-memory` output refers to nothing
# that isn't there.
missing=()
while read -r op; do
  grep -qP "^(@\[inline\] )?def $op\b" "$file" || missing+=("$op")
done < <(grep -oP '"[^"]*\bMem\.\K\w+' src/Emitter.cpp | sort -u)
if [ ${#missing[@]} = 0 ]; then
  printf 'ok    ExecMem has every operation the emitter prints\n'
else
  fail "ExecMem has no ${missing[*]}, which the emitter prints as Mem's"
fi

# usage: mutant WHAT THEOREM OLD NEW
# `file` with OLD, which has to be there once, replaced by NEW has to fail in THEOREM, and not only at a resource
# limit or because a name went missing.
mutant() {
  local what=$1 theorem=$2 status=0 out errors line found
  if ! python3 -c '
import sys
text, old, new = open(sys.argv[1]).read(), sys.argv[2], sys.argv[3]
if text.count(old) != 1:
    sys.exit(f"{text.count(old)} occurrences of: {old}")
open(sys.argv[4], "w").write(text.replace(old, new))
' "$file" "$3" "$4" "$work/Mutant.lean"; then
    fail "$what: the mutant doesn't apply"
    return
  fi
  out=$(lean "$work/Mutant.lean" 2>&1) || status=$?
  errors=$(grep -E "^$work/Mutant.lean:[0-9]+:[0-9]+: error" <<<"$out" || true)
  line=$(head -1 <<<"$errors" | cut -d: -f2)
  found=$(awk -v n="${line:-0}" 'NR <= n && match($0, /^(private )?(theorem|def) [^ ]+/) {
    split(substr($0, RSTART, RLENGTH), w, " "); name = w[length(w)] } END { print name }' "$work/Mutant.lean")
  if [ "$status" = 0 ]; then
    fail "$what: the proofs still check, so they don't pin $theorem down" "$out"
  elif [ -z "$errors" ] || ! grep -qvE "$limit" <<<"$errors"; then
    fail "$what: stops only at a resource limit or never says why" "$out"
  elif grep -qiE 'unknown (identifier|constant|tactic|namespace)|unexpected (token|identifier)' <<<"$errors"; then
    fail "$what: fails because the text can't be read, not because the operation is wrong" "$out"
  elif [ "$found" != "$theorem" ]; then
    fail "$what: fails first in $found, not in $theorem" "$errors"
  else
    printf 'ok    %s stops %s\n' "$what" "$theorem"
  fi
}

# The unchanged module checks the same way, so a mutant's failure is its own.
if out=$(lean "$file" 2>&1); then
  printf 'ok    %s checks\n' "$file"
else
  fail "$file doesn't check" "$out"
fi
mutant 'a store one byte short' storeInt_agrees \
  'Outcome.ok <| x.write q (w / 8) fun i =>' 'Outcome.ok <| x.write q (w / 8 - 1) fun i =>'
mutant 'a pointer stored one byte short' storePtr_agrees \
  'Outcome.ok <| x.write q 8 fun i =>' 'Outcome.ok <| x.write q 7 fun i =>'
mutant 'a memset of the wrong value' memset_agrees \
  'x.write q k.toNat fun _ =>
          match v with
          | none => .poison
          | some x => .val x' 'x.write q k.toNat fun _ =>
          match v with
          | none => .poison
          | some x => .val (x + 1#8)'
mutant 'a memcpy from a byte further on' memcpy_agrees \
  'x.toMem.visible s sa (sOff + i)' 'x.toMem.visible s sa (sOff + i + 1)'
mutant 'a free that leaves the allocation' free_agrees \
  '| none, none => Outcome.ok ((), x.setAlloc q.block none)' '| none, none => Outcome.ok ((), x)'
mutant 'a malloc that never fails' malloc_agrees \
  'if x.failAlloc block then Outcome.ok' 'if false then Outcome.ok'
mutant 'an alloca writable outside its lifetime' alloca_agrees \
  'readonly := dead, bytes := ExecBytes.uninit n.toNat' 'readonly := false, bytes := ExecBytes.uninit n.toNat'
mutant 'a lifetime that keeps the bytes' lifetime_agrees \
  'bytes := ExecBytes.uninit a.size' 'bytes := a.bytes'
mutant 'a frame that is never freed' withFrame_agrees \
  '⟨clearFrame allocs frame, next, base, saved,' '⟨allocs, next, base, saved,'
mutant 'a call that leaves what initializes covers' call_agrees \
  '⟨if c.ranges.isEmpty then allocs else clearRanges c allocs (c.ranges.map (·.1)),' '⟨allocs,'
mutant 'poison stored as uninitialized' get_set \
  '.poison => ⟨data.set! (2 * i) 2, ptrs, rest⟩' '.poison => ⟨data.set! (2 * i) 0, ptrs, rest⟩'
mutant 'a write the running calls never see' toMem_write \
  'let calls := noteWrite x.calls q n' 'let calls := x.calls'
mutant 'a global with the wrong contents' toMem_addGlobal \
  'bytes := ExecBytes.ofFn size (Mem.globalBytes init)' 'bytes := ExecBytes.uninit size'

# `--executable-memory` prints the Lean proofs are about with `ExecMem` for `Mem` and nothing else changed, whole or
# split, and that checks.
for ll in heap gep promises memory_errors stops ub; do
  if ! "$tool" "tests/real/$ll.ll" --namespace X -o "$work/model.lean" 2>/dev/null &&
    [ ! -s "$work/model.lean" ]; then
    fail "tests/real/$ll.ll doesn't translate"
    continue
  fi
  "$tool" "tests/real/$ll.ll" --namespace X --executable-memory -o "$work/X.lean" 2>/dev/null
  if ! grep -q '\bExecMem\.' "$work/X.lean"; then
    fail "tests/real/$ll.ll: --executable-memory printed no ExecMem"
  elif ! cmp -s <(sed 's/\bExecMem\b/Mem/g' "$work/X.lean") "$work/model.lean"; then
    fail "tests/real/$ll.ll: --executable-memory changed more than Mem" \
      "$(diff <(sed 's/\bExecMem\b/Mem/g' "$work/X.lean") "$work/model.lean" | head -20)"
  elif ! out=$(lean "$work/X.lean" 2>&1); then
    fail "tests/real/$ll.ll: --executable-memory output doesn't check" "$out"
  else
    printf 'ok    tests/real/%s.ll on ExecMem is the same Lean, and checks\n' "$ll"
  fi
done
# A namespace the rename would change is refused, whole or split, with or without a dot around it.
refused=1
for ns in Mem ExecMem A.Mem Mem.B '«A-Mem-B»'; do
  for split in "" "--split $work/refused"; do
    # shellcheck disable=SC2086 # $split is a flag and its value, or nothing.
    "$tool" tests/real/heap.ll --namespace "$ns" --executable-memory -o "$work/refused.lean" $split 2>/dev/null
    code=$?
    if [ "$code" != 2 ]; then
      fail "--namespace $ns --executable-memory ${split:+with --split }exits $code, not 2"
      refused=0
    fi
  done
done
[ "$refused" = 1 ] && printf 'ok    --executable-memory refuses a namespace that names Mem or ExecMem\n'
"$tool" tests/real/heap.ll --namespace X --split "$work/model" 2>/dev/null
"$tool" tests/real/heap.ll --namespace X --split "$work/exec" --executable-memory 2>/dev/null
same=1
for f in "$work"/model/X.lean "$work"/model/X/*.lean; do
  g=$work/exec/${f#"$work"/model/}
  cmp -s <(sed 's/\bExecMem\b/Mem/g' "$g") "$f" || same=0
done
if [ "$same" = 1 ] && grep -rq '\bExecMem\b' "$work/exec"; then
  printf 'ok    split, the same Lean with ExecMem\n'
else
  fail 'split, --executable-memory changed more than Mem'
fi

# Two functions of memory.c agree whole with their copies, by tests/exec_memory/Link.lean, on the standard axioms and
# replayed in the kernel. A copy with a branch swapped in one block has to stop that block's equation.
clang -O2 -fno-strict-aliasing -S -emit-llvm -fno-discard-value-names tests/real/memory.c -o "$work/memory.ll"
"$tool" "$work/memory.ll" --namespace MemoryC -o "$work/MemoryC.lean" 2>/dev/null
"$tool" "$work/memory.ll" --namespace MemoryCExec --executable-memory -o "$work/MemoryCExec.lean" 2>/dev/null
linked=0
if ! out=$(lean -R "$work" -o "$work/MemoryC.olean" "$work/MemoryC.lean" 2>&1) ||
  ! out=$(lean -R "$work" -o "$work/MemoryCExec.olean" "$work/MemoryCExec.lean" 2>&1); then
  fail 'memory.c, both ways, compiled' "$out"
elif ! out=$(lean -DwarningAsError=true -R tests/exec_memory -o "$work/Link.olean" tests/exec_memory/Link.lean 2>&1); then
  fail 'tests/exec_memory/Link.lean' "$out"
elif out=$(IRLEAN_CHECK_MODULE=Link lean tests/check_axioms.lean 2>&1) &&
  grep -q 'and 0 from bv_decide' <<<"$out" && replay=$(timeout "$secs" leanchecker Link 2>&1); then
  printf 'ok    sum_bytes and fill agree whole with their copies: %s, and leanchecker replays it\n' "$out"
  linked=1
else
  fail 'Link: axioms and replay' "$out ${replay:-}"
fi
if [ "$linked" = 1 ]; then
  old='br epil_iter_cmp_not (.for_cond_cleanup m) (.for_body_epil m inc_epil add_epil epil_iter_next p xtraiter)'
  new='br epil_iter_cmp_not (.for_body_epil m inc_epil add_epil epil_iter_next p xtraiter) (.for_cond_cleanup m)'
  mkdir "$work/mutant"
  if ! python3 -c '
import sys
text, old, new = open(sys.argv[1]).read(), sys.argv[2], sys.argv[3]
if text.count(old) != 1:
    sys.exit(f"{text.count(old)} occurrences of: {old}")
open(sys.argv[4], "w").write(text.replace(old, new))
' "$work/MemoryCExec.lean" "$old" "$new" "$work/mutant/MemoryCExec.lean"; then
    fail 'a branch swapped in the copy: the mutant does not apply'
  else
    cp "$work/MemoryC.olean" "$work/mutant/"
    status=0
    if ! out=$(LEAN_PATH="$work/mutant:$LEAN_PATH" lean -R "$work/mutant" -o "$work/mutant/MemoryCExec.olean" \
      "$work/mutant/MemoryCExec.lean" 2>&1); then
      fail 'a branch swapped in the copy does not compile' "$out"
    else
      out=$(LEAN_PATH="$work/mutant:$LEAN_PATH" lean -R tests/exec_memory tests/exec_memory/Link.lean 2>&1) || status=$?
      errors=$(grep -E ':[0-9]+:[0-9]+: error' <<<"$out" || true)
      line=$(head -1 <<<"$errors" | sed -E 's/^.*Link\.lean:([0-9]+):.*$/\1/')
      found=$(awk -v n="${line:-0}" 'NR <= n && match($0, /^theorem [^ ]+/) { name = $2 } END { print name }' \
        tests/exec_memory/Link.lean)
      if [ "$status" = 0 ]; then
        fail 'a branch swapped in the copy: Link.lean still checks'
      elif ! grep -qvE "$limit" <<<"$errors"; then
        fail 'a branch swapped in the copy: stops only at a resource limit' "$out"
      elif [ "$found" != fill_step ]; then
        fail "a branch swapped in the copy: fails first in $found, not in fill_step" "$errors"
      else
        printf 'ok    a branch swapped in the copy stops fill_step\n'
      fi
    fi
  fi
fi

exit "$failed"
