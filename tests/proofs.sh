#!/usr/bin/env bash
# shellcheck disable=SC2329 # `start` and `in_dir` call these functions.
# Regenerates Lean from real compiler output, then checks the proofs against it. A proof fails if it
# relies on any axiom outside `check_axioms`' list, which rules out `sorry`, if `leanchecker` rejects it, if
# its theorem doesn't name the function ir-lean generated, or if the regenerated code no longer satisfies it.
# A bug put in the C has to stop the proof with an error of its own, and not by running out of resources.
# usage: tests/proofs.sh path/to/ir-lean [--generate DIR]
# `--generate` only writes the modules the proofs import to DIR, where `lake build Proofs` and the
# language server look for them.
set -euo pipefail
tool=$(realpath "$1")
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
# At a time. What limits this is memory: a proof can take a few GB.
jobs=${LEAN_JOBS:-4}
# A runaway proof fails with Lean's own error instead of taking the machine's memory.
lean() { command lean -M "${LEAN_MAX_MB:-4000}" "$@"; }
# Modules from `dir` come first, in case `lake build Proofs` left older ones in the library's directory.
in_dir() {
  local dir=$1
  shift
  LEAN_PATH="$dir:$root/.lake/build/lib/lean" "$@"
}

# zlib's own source, at the version the flake pins.
zlib_src=${ZLIB_SRC:-$(nix build --inputs-from "$root" --no-link --print-out-paths nixpkgs#zlib.src)}
mkdir "$work/zlib"
tar -xf "$zlib_src" -C "$work/zlib" --strip-components=1

# What's been compiled and what has passed, named after everything that went into it, so only what changed runs
# again. CI doesn't keep build/, so it checks everything every time. To do that here, delete the directory.
cache=$root/build/proof-cache
mkdir -p "$cache"
library=$({
  command lean --version
  cat "$0" "$root/tests/check_axioms.lean" "$root/.lake/build/lib/lean/IRLean.olean" "$root"/.lake/build/lib/lean/IRLean/*.olean
} | sha256sum | cut -d' ' -f1)

# What's in the cache stays until enough newer entries push it out.
known() {
  [ -e "$cache/$1" ] && touch "$cache/$1"
}

# Stores what's on standard input under a name, all at once, so nothing can read half of it.
remember() {
  local partial
  partial=$(mktemp "$cache/partial.XXXXXX")
  cat >"$partial"
  mv "$partial" "$cache/$1"
}

# The hash of the file $2 and of what it imports from directory $1.
# usage: module_key DIR FILE
module_key() {
  local import
  {
    printf '%s\n' "$library"
    cat "$2"
    while IFS= read -r import; do
      cat "$1/${import//.//}.key" 2>/dev/null || true
    done < <(sed -n 's/^import //p' "$2")
  } | sha256sum | cut -d' ' -f1
}

# Compiles FILE to OLEAN, looking for what it imports in DIR, unless that's been done before.
# usage: compile DIR MODULE_ROOT OLEAN FILE
compile() {
  local key
  key=$(module_key "$1" "$4")
  if known "$key.olean"; then
    cp "$cache/$key.olean" "$3"
  else
    in_dir "$1" lean -R "$2" -o "$3" "$4" || return 1
    remember "$key.olean" <"$3"
  fi
  printf '%s\n' "$key" >"${3%.olean}.key"
}

# Compiles the modules of a split translation, each after what it imports, as many at a time as are ready.
# usage: compile_split DIR NAMESPACE
compile_split() {
  local dir=$1 ns=$2 f import ready waiting compiling pid failed=0
  local pending=("$dir/$ns"/*.lean)
  while [ "${#pending[@]}" -gt 0 ]; do
    waiting=()
    compiling=()
    for f in "${pending[@]}"; do
      ready=1
      while IFS= read -r import; do
        [ -e "$dir/$ns/$import.olean" ] || ready=0
      done < <(sed -n "s/^import $ns\.//p" "$f")
      if [ "$ready" = 0 ]; then
        waiting+=("$f")
      else
        compile "$dir" "$dir" "${f%.lean}.olean" "$f" &
        compiling+=("$!")
        if [ "${#compiling[@]}" -ge "$jobs" ]; then
          wait "${compiling[0]}" || failed=1
          compiling=("${compiling[@]:1}")
        fi
      fi
    done
    for pid in "${compiling[@]+"${compiling[@]}"}"; do
      wait "$pid" || failed=1
    done
    [ "$failed" = 0 ] || return 1
    if [ "${#waiting[@]}" = "${#pending[@]}" ]; then
      printf 'FAIL  modules in %s import each other\n' "$dir/$ns"
      return 1
    fi
    pending=("${waiting[@]+"${waiting[@]}"}")
  done
  compile "$dir" "$dir" "$dir/$ns.olean" "$dir/$ns.lean"
}

# Compiles a C file with stock clang and translates it to the Lean module `$2`, with a module per function, in
# the directory `$3`.
# Proofs never run the code, so Lean doesn't have to generate any. PROOF_CFLAGS comes from the dev shell
# and fixes the target, so a proof checks the same IR on every host. -fno-strict-aliasing leaves out `tbaa`,
# which the emitter refuses.
translate() {
  local status=0 left
  # shellcheck disable=SC2086 # PROOF_CFLAGS is several flags.
  clang $PROOF_CFLAGS -O2 -fno-strict-aliasing -S -emit-llvm -fno-discard-value-names -D_LARGEFILE64_SOURCE=1 -o "$3/$2.ll" "$1"
  left=$("$tool" "$3/$2.ll" --split "$3" --namespace "$2" --no-code 2>&1 >/dev/null) || status=$?
  # Exit 3 means some functions were left out, which is fine only if they're exactly the ones expected.
  if [ "$status" = 3 ] && [ "$(sed -n 's/^ir-lean: left out @\([^:]*\):.*/\1/p' <<<"$left" | tr '\n' ' ')" = "$(may_leave_out "$2")" ]; then
    status=0
  fi
  [ "$status" = 0 ] || printf '%s\n' "$left" >&2
  return "$status"
}

# The functions a module may leave out: in `Inflate`, the two that call `crc32` and `adler32`, from other files.
may_leave_out() {
  if [ "$1" = Inflate ]; then printf 'inflate inflateSetDictionary '; fi
}

gen() {
  translate "$@"
  compile_split "$3" "$2"
}

# Waits for a free slot, then runs a command in the background.
pids=()
start() {
  while [ "$(jobs -rp | wc -l)" -ge "$jobs" ]; do
    wait -n || true
  done
  "$@" &
  pids+=("$!")
}

# Prints the axioms of everything in a compiled proof module, or fails naming any that aren't allowed.
# This reads the module and what it imports as data, rather than trusting its `#print axioms`, which a proof
# could leave out, or running any of its code. The standard three are allowed, and so is what `bv_decide` adds
# for each call, an axiom that a Bool it worked out natively is true. A name is easy to fake, so each of those
# gets worked out again here, and `implemented_by` and `extern` are refused. Then `leanchecker` replays the
# module's declarations through the kernel, since Lean code can add one the kernel never checked.
# With a namespace, a theorem and a function, it also checks that the theorem is about that function, as ir-lean
# generated it.
# usage: check_axioms MODULE [NAMESPACE THEOREM FUNCTION]
check_axioms() {
  local replay
  IRLEAN_CHECK_MODULE=$1 IRLEAN_CHECK_GENERATED=${2:-} IRLEAN_CHECK_THEOREMS=${3:+$3 $2.$4} \
    in_dir "$work" lean "$root/tests/check_axioms.lean" || return 1
  if ! replay=$(in_dir "$work" leanchecker "$1" 2>&1); then
    printf 'leanchecker rejects %s: %s\n' "$1" "${replay:0:2000}"
    return 1
  fi
}

# usage: check_proof FILE [NAMESPACE THEOREM FUNCTION]
check_proof() {
  local name=${1##*/} module axioms key
  module=${name%.lean}
  if ! compile "$work" "$(dirname "$1")" "$work/$module.olean" "$1" >"$work/$name.out" 2>&1; then
    printf 'FAIL  %s\n' "$name"
    head -c 4000 "$work/$name.out"
    return 1
  fi
  key=$(printf '%s\n' "$(<"$work/$module.key")" "$@" | sha256sum | cut -d' ' -f1)
  if known "$key.axioms"; then
    axioms=$(<"$cache/$key.axioms")
  elif axioms=$(check_axioms "$module" "${@:2}" 2>&1); then
    printf '%s' "$axioms" | remember "$key.axioms"
  else
    printf 'FAIL  %s\n%s\n' "$name" "${axioms:0:4000}"
    return 1
  fi
  printf 'ok    %s (axioms: %s)\n' "$name" "$axioms"
}

# Each of these has to fail in the axiom check itself, and not for some other reason. With a namespace, a theorem and
# a function, it's checked that the theorem is about that function, and that can fail too.
# usage: must_reject NAME LEAN_SOURCE [NAMESPACE THEOREM FUNCTION]
about="isn't in what ir-lean generated|doesn't mention"
must_reject() {
  local dir output key
  key=$(printf '%s\n' "$library" "$@" | sha256sum | cut -d' ' -f1)
  if ! known "$key.rejected"; then
    dir=$(mktemp -d -p "$work")
    printf '%s\n' "$2" >"$dir/Bad${1//[^a-z]/}.lean"
    output=$(check_proof "$dir/Bad${1//[^a-z]/}.lean" "${@:3}" 2>&1 || true)
    if ! grep -qE "not an allowed axiom|not what bv_decide would add|uses implemented_by|uses extern|leanchecker rejects|$about" <<<"$output"; then
      printf 'FAIL  a proof with %s still passes\n%s\n' "$1" "$output"
      return 1
    fi
    remember "$key.rejected" </dev/null
  fi
  printf 'ok    a proof with %s fails\n' "$1"
}

# Lean's errors for running out of time, memory or stack, in a tactic or the kernel. A proof that stops at one of
# these might check with more, so it says nothing about whether the code it's about changed.
limit='maximum number of heartbeats|\(deterministic\) timeout|maximum recursion depth|deep recursion|stack overflow|'
limit+='excessive memory|out of memory|SAT solver timed out|maximum number of steps'

# Whether a proof fails with an error of its own, which is all a broken proof needs to show, so this doesn't
# wait for the rest of it. An error at 1:0 is about the file's imports, and says nothing about the proof. A resource
# limit isn't an error of its own, and Lean goes on to the next declaration after one, with the one that failed
# still there for the rest to use. Returns 0 if it fails, 1 if it checks, and 2 if that's unknown: its only errors
# are resource limits, or Lean stopped with no error at all.
# usage: stops_checking DIR PROOF
stops_checking() {
  local line output pid status=0 limited=
  exec {output}< <(LEAN_PATH="$1:$root/.lake/build/lib/lean" exec lean -M "${LEAN_MAX_MB:-4000}" "$2" 2>&1)
  pid=$!
  while IFS= read -r line <&"$output"; do
    if [[ $line == "$2:"*": error"* && $line != "$2:1:0:"* ]]; then
      if grep -qE "$limit" <<<"$line"; then
        limited=${limited:-$line}
        continue
      fi
      kill "$pid" 2>/dev/null
      wait "$pid" 2>/dev/null
      exec {output}<&-
      return 0
    fi
    [[ $line == "$2:1:0:"* ]] && printf '%s\n' "$line"
  done
  wait "$pid" || status=$?
  exec {output}<&-
  if [ -n "$limited" ]; then
    printf 'its only errors are resource limits, such as %s\n' "${limited:0:500}"
    return 2
  elif [ "$status" != 0 ]; then
    printf 'exit %s, with no error in %s\n' "$status" "$2"
    return 2
  fi
  return 1
}

# A proof has to depend on the code. Break the C, and the same proof must stop checking.
# usage: must_break NAME MODULE DIR C_FILE FILE_TO_EDIT PROOF SED
must_break() {
  local broken module key why stopped proofs=("$6")
  broken=$(mktemp -d -p "$work")
  cp -r "$3" "$broken/src"
  sed -i "$7" "$broken/src/$5"
  if cmp -s "$3/$5" "$broken/src/$5"; then
    printf 'FAIL  %s changed nothing in the C\n' "$1"
    return 1
  fi
  translate "$broken/src/$4" "$2" "$broken"
  [ "$2" = Crc ] && proofs+=("$root/tests/proofs/CrcTables.lean" "$root/tests/proofs/CrcSpec.lean")
  key=$({
    printf '%s\n' "$library"
    cat "$broken/$2.lean" "$broken/$2"/*.lean "${proofs[@]}"
  } | sha256sum | cut -d' ' -f1)
  if known "$key.broke"; then
    printf 'ok    %s: the proof stops checking\n' "$1"
    return 0
  fi
  compile_split "$broken" "$2"
  # These two only depend on the globals. If those changed, they may be what stops checking.
  if [ "$2" = Crc ]; then
    for module in CrcTables CrcSpec; do
      if ! known "$(module_key "$broken" "$root/tests/proofs/$module.lean").olean"; then
        stopped=0
        why=$(stops_checking "$broken" "$root/tests/proofs/$module.lean") || stopped=$?
        if [ "$stopped" = 0 ]; then
          remember "$key.broke" </dev/null
          printf 'ok    %s: the proof stops checking\n' "$1"
          return 0
        elif [ "$stopped" = 2 ]; then
          printf 'FAIL  %s: unknown whether %s stops checking: %s\n' "$1" "$module" "$why"
          return 1
        fi
      fi
      compile "$broken" "$root/tests/proofs" "$broken/$module.olean" "$root/tests/proofs/$module.lean" >/dev/null
    done
  fi
  stopped=0
  why=$(stops_checking "$broken" "$6") || stopped=$?
  if [ "$stopped" = 1 ]; then
    printf 'FAIL  %s: the proof still checks\n%s' "$1" "${why:+$why$'\n'}"
    return 1
  elif [ "$stopped" = 2 ]; then
    # More time or memory might let the proof check, so the bug isn't shown to break it.
    printf 'FAIL  %s: unknown whether the proof stops checking: %s\n' "$1" "$why"
    return 1
  fi
  remember "$key.broke" </dev/null
  printf 'ok    %s: the proof stops checking\n' "$1"
}

if [ "${2:-}" = --generate ]; then
  translate "$root/tests/real/bi_reverse.c" Real "$work"
  translate "$work/zlib/adler32.c" Zlib "$work"
  translate "$work/zlib/crc32.c" Crc "$work"
  translate "$work/zlib/inflate.c" Inflate "$work"
  for module in Real Zlib Crc Inflate; do
    mkdir -p "$3/$module"
    cp "$work/$module.lean" "$3"
    cp "$work/$module"/*.lean "$3/$module"
  done
  exit 0
fi

gen "$root/tests/real/bi_reverse.c" Real "$work" &
real=$!
gen "$work/zlib/adler32.c" Zlib "$work" &
adler=$!
gen "$work/zlib/crc32.c" Crc "$work" &
crc=$!
gen "$work/zlib/inflate.c" Inflate "$work" &
inflate=$!
# Each runs to the end, so that nothing is left using the directory the exit deletes.
failed=0
wait "$real" || failed=1
wait "$adler" || failed=1
wait "$crc" || failed=1
wait "$inflate" || failed=1
[ "$failed" = 0 ] || exit 1

# Each theorem has to be about the function ir-lean generated, in the module the proof imports.
start check_proof "$root/tests/proofs/Adler32.lean" Zlib adler32_z_correct adler32_z
start check_proof "$root/tests/proofs/MemoryModel.lean"
start check_proof "$root/tests/proofs/Popcount.lean" Real popcount_correct popcount
start check_proof "$root/tests/proofs/UpdateWindow.lean" Inflate updatewindow_safe updatewindow

start must_reject 'its own axiom' 'axiom cheat : 1 = 2
theorem wrong : 1 = 2 := cheat
#print axioms wrong'
start must_reject 'an axiom it never prints' 'axiom cheat : 1 = 2
theorem wrong : 1 = 2 := cheat'
start must_reject 'an axiom nothing uses' 'axiom cheat : 1 = 2'
start must_reject 'sorry' 'theorem wrong : 1 = 2 := sorry'
start must_reject 'native_decide' 'theorem right : 1 = 1 := by native_decide'
start must_reject 'an axiom named like bv_decide' 'axiom t._native.bv_decide.ax_1_1 : 1 = 2
theorem wrong : 1 = 2 := t._native.bv_decide.ax_1_1'
start must_reject 'a false axiom shaped like bv_decide' 'axiom t._native.bv_decide.ax_1_1 : false = true
theorem wrong : 1 = 2 := by have := t._native.bv_decide.ax_1_1; contradiction'
# Compiled code runs `truth` for `lie`, so rerunning the axiom natively says it holds.
start must_reject 'a bv_decide axiom that implemented_by makes true' 'def truth : Bool := true
@[implemented_by truth] def lie : Bool := false
axiom t._native.bv_decide.ax_1_1 : lie = true
theorem wrong : 1 = 2 := by have h : lie = true := t._native.bv_decide.ax_1_1; simp [lie] at h'
# A theorem about something of its own, named like a function ir-lean left out, or about nothing it generated.
start must_reject 'a theorem about a lookalike of the function' 'import Real
def Real.left_out (x : Nat) : Nat := x
theorem lookalike : Real.left_out 1 = 1 := rfl' Real lookalike left_out
start must_reject 'a theorem that is not about the function' 'import Real
theorem unrelated : 1 + 1 = 2 := rfl' Real unrelated popcount
start must_reject 'extern' '@[extern "lean_nat_add"] def add (a b : Nat) : Nat := a * b
theorem right : add 2 2 = 4 := rfl'
# The kernel never sees `oops`, so only replaying the module's declarations catches it.
# shellcheck disable=SC2016 # Backquotes are Lean's names here, not the shell's.
start must_reject 'a declaration the kernel skipped' 'import Lean
open Lean Elab Command
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl {
  name := `oops, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
theorem wrong : 1 = 2 := oops.elim'

# A proof that only runs out of heartbeats might check with more, so it can't count as stopped.
limit_is_unknown() {
  local dir status=0
  dir=$(mktemp -d -p "$work")
  printf 'set_option maxHeartbeats 1 in\ntheorem slow : 2 ^ 20 = 1048576 := by decide\n' >"$dir/Slow.lean"
  stops_checking "$dir" "$dir/Slow.lean" >/dev/null || status=$?
  if [ "$status" != 2 ]; then
    printf 'FAIL  a proof that only runs out of heartbeats counts as stopping, with %s\n' "$status"
    return 1
  fi
  printf 'ok    a proof that only runs out of heartbeats is unknown, not stopped\n'
}
start limit_is_unknown

breaks_popcount() { must_break "popcount $1" Real "$root/tests/real" bi_reverse.c bi_reverse.c "$root/tests/proofs/Popcount.lean" "$2"; }
breaks_adler() { must_break "adler32 $1" Zlib "$work/zlib" adler32.c adler32.c "$root/tests/proofs/Adler32.lean" "$2"; }
breaks_crc() { must_break "crc32 $1" Crc "$work/zlib" crc32.c "$2" "$root/tests/proofs/Crc32.lean" "$3"; }
breaks_window() { must_break "updatewindow $1" Inflate "$work/zlib" inflate.c inflate.c "$root/tests/proofs/UpdateWindow.lean" "$2"; }

start breaks_popcount 'shifts by 2' 's/x >>= 1;/x >>= 2;/'

start breaks_adler 'wrong modulus' 's/#define BASE 65521U/#define BASE 65519U/'
start breaks_adler 'reads past the end' 's/while (len >= 16) {/while (len >= 15) {/'
start breaks_adler 'wrong sum' 's/#define DO1(buf,i)  {adler += (buf)\[i\]; sum2 += adler;}/#define DO1(buf,i)  {adler += (buf)[i]; sum2 += adler + 1;}/'
start breaks_adler 'skips a byte per block' 's/len -= NMAX;/len -= NMAX - 1;/'
start breaks_adler 'single-byte path forgets the modulus' '/^    if (len == 1) {/,/^    }/ s/if (adler >= BASE)/if (adler > BASE)/'

# Each of these is a memory bug: the first reads past the end of the output, and the others write past the window.
start breaks_window 'copies past what the output has' 's/        if (dist > copy) dist = copy;//'
start breaks_window 'thinks the window is twice its size' 's/state->wsize = 1U << state->wbits;/state->wsize = 2U << state->wbits;/'
start breaks_window 'copies one byte too many' 's/zmemcpy(state->window + state->wnext, end - copy, dist);/zmemcpy(state->window + state->wnext, end - copy, dist + 1);/'

# Crc32 and the mutants of crc32.c need these two.
if check_proof "$root/tests/proofs/CrcTables.lean" && check_proof "$root/tests/proofs/CrcSpec.lean"; then
  start check_proof "$root/tests/proofs/Crc32.lean" Crc crc32_z_correct crc32_z

  start breaks_crc 'wrong table entry' crc32.h 's/0x77073096/0x77073097/'
  start breaks_crc 'wrong braid table entry' crc32.h 's/0xaf449247/0xaf449246/'
  start breaks_crc 'reads past the end' crc32.c 's/while (len >= 8) {/while (len >= 7) {/'
  start breaks_crc 'no preconditioning' crc32.c 's/crc = (~crc) \& 0xffffffff;/crc = crc \& 0xffffffff;/'
  start breaks_crc 'no final inversion' crc32.c 's/return crc ^ 0xffffffff;/return crc;/'
  start breaks_crc 'skips a word' crc32.c '0,/words += N;/s//words += N + 1;/'
  start breaks_crc 'starts braid too soon' crc32.c 's/if (len >= N \* W + W - 1) {/if (len >= N * W - 2) {/'
else
  failed=1
fi

for pid in "${pids[@]}"; do
  wait "$pid" || failed=1
done
# Enough for a few versions of everything.
find "$cache" -type f -printf '%T@ %p\n' | sort -rn | tail -n +5001 | cut -d' ' -f2- | xargs -r rm -f
exit $failed
