#!/usr/bin/env bash
# shellcheck disable=SC2329 # `start` and `in_dir` call these functions.
# Regenerates Lean from real compiler output, then checks the proofs against it. A proof fails if it
# relies on any axiom outside `check_axioms`' list, which rules out `sorry`, or if the regenerated code
# no longer satisfies it.
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

# Compiles the modules of a split translation, each after what it imports, as many at a time as are ready. A
# module whose text and imports match the same module under `reuse` is copied from there, since compiling it
# would give the same result.
# usage: compile_split DIR NAMESPACE [REUSE]
compile_split() {
  local dir=$1 ns=$2 reuse=${3:-} f name import ready same waiting compiling pid failed=0
  local -A copied=()
  local pending=("$dir/$ns"/*.lean)
  while [ "${#pending[@]}" -gt 0 ]; do
    waiting=()
    compiling=()
    for f in "${pending[@]}"; do
      name=$(basename "$f" .lean)
      ready=1
      same=1
      while IFS= read -r import; do
        [ -e "$dir/$ns/$import.olean" ] || ready=0
        [ -n "${copied[$import]:-}" ] || same=0
      done < <(sed -n "s/^import $ns\.//p" "$f")
      if [ "$ready" = 0 ]; then
        waiting+=("$f")
      elif [ -n "$reuse" ] && [ "$same" = 1 ] && cmp -s "$f" "$reuse/$ns/$name.lean"; then
        cp "$reuse/$ns/$name.olean" "$dir/$ns/$name.olean"
        copied[$name]=1
      else
        in_dir "$dir" lean -R "$dir" -o "${f%.lean}.olean" "$f" &
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
  in_dir "$dir" lean -R "$dir" -o "$dir/$ns.olean" "$dir/$ns.lean"
}

# Compiles a C file with stock clang and translates it to the Lean module `$2`, with a module per function, in
# the directory `$3`. `$4` is an earlier translation to reuse what hasn't changed from.
# Proofs never run the code, so Lean doesn't have to generate any. PROOF_CFLAGS comes from the dev shell
# and fixes the target, so a proof checks the same IR on every host. -fno-strict-aliasing leaves out `tbaa`,
# which the emitter refuses.
gen() {
  # shellcheck disable=SC2086 # PROOF_CFLAGS is several flags.
  clang $PROOF_CFLAGS -O2 -fno-strict-aliasing -S -emit-llvm -fno-discard-value-names -D_LARGEFILE64_SOURCE=1 -o "$3/$2.ll" "$1"
  "$tool" "$3/$2.ll" --split "$3" --namespace "$2" --no-code >/dev/null
  compile_split "$3" "$2" "${4:-}"
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
# This looks at the module rather than trusting its `#print axioms`, which a proof could leave out. The
# standard three are allowed, and so is what `bv_decide` adds for each call, an axiom that a Bool it
# worked out natively is true. A name is easy to fake, so each of those gets worked out again here.
check_axioms() {
  in_dir "$work" lean --stdin <<LEAN
import Lean
import $1
open Lean Meta

def bvDecideResult? (env : Environment) : Name → Option Expr
  | n@(.str (.str (.str _ "_native") "bv_decide") ax) =>
    if ax.startsWith "ax_" then
      match env.find? n with
      | some (.axiomInfo info) =>
        if info.type.isAppOfArity \`\`Eq 3 && info.type.appArg! == mkConst \`\`Bool.true then
          some info.type.appFn!.appArg!
        else none
      | _ => none
    else none
  | _ => none

run_meta do
  let env ← getEnv
  let some index := env.getModuleIdx? \`$1 | throwError "no module $1"
  let mut axioms : NameSet := {}
  for declaration in env.header.moduleData[index.toNat]!.constNames do
    for axiom' in ← collectAxioms declaration do
      axioms := axioms.insert axiom'
  let mut count : Nat := 0
  for axiom' in axioms do
    if [\`\`propext, \`\`Classical.choice, \`\`Quot.sound].contains axiom' then continue
    let some result := bvDecideResult? env axiom' | throwError "not an allowed axiom: {axiom'}"
    match ← nativeEqTrue \`bv_decide result with
    | .success _ => count := count + 1
    | .notTrue => throwError "not what bv_decide would add: {axiom'}"
  IO.println s!"at most the standard three, and {count} from bv_decide"
LEAN
}

check_proof() {
  local name=${1##*/} module axioms
  module=${name%.lean}
  if ! in_dir "$work" lean -R "$(dirname "$1")" -o "$work/$module.olean" "$1" >"$work/$name.out" 2>&1; then
    printf 'FAIL  %s\n' "$name"
    head -c 4000 "$work/$name.out"
    return 1
  elif ! axioms=$(check_axioms "$module" 2>&1); then
    printf 'FAIL  %s\n%s\n' "$name" "${axioms:0:4000}"
    return 1
  fi
  printf 'ok    %s (axioms: %s)\n' "$name" "$axioms"
}

# Each of these has to fail in the axiom check itself, and not for some other reason.
# usage: must_reject NAME LEAN_SOURCE
must_reject() {
  local dir output
  dir=$(mktemp -d -p "$work")
  printf '%s\n' "$2" >"$dir/Bad${1//[^a-z]/}.lean"
  output=$(check_proof "$dir/Bad${1//[^a-z]/}.lean" 2>&1 || true)
  if ! grep -qE 'not an allowed axiom|not what bv_decide would add' <<<"$output"; then
    printf 'FAIL  a proof with %s still passes\n%s\n' "$1" "$output"
    return 1
  fi
  printf 'ok    a proof with %s fails\n' "$1"
}

# Whether a proof fails with an error of its own, which is all a broken proof needs to show, so this doesn't
# wait for the rest of it. An error at 1:0 is about the file's imports, and says nothing about the proof.
# usage: stops_checking DIR PROOF
stops_checking() {
  local line output pid status=0
  exec {output}< <(LEAN_PATH="$1:$root/.lake/build/lib/lean" exec lean -M "${LEAN_MAX_MB:-4000}" "$2" 2>&1)
  pid=$!
  while IFS= read -r line <&"$output"; do
    if [[ $line == "$2:"*": error"* && $line != "$2:1:0:"* ]]; then
      kill "$pid" 2>/dev/null
      wait "$pid" 2>/dev/null
      exec {output}<&-
      return 0
    fi
    [[ $line == "$2:1:0:"* ]] && printf '%s\n' "$line"
  done
  wait "$pid" || status=$?
  exec {output}<&-
  [ "$status" != 0 ] && printf 'exit %s, with no error in %s\n' "$status" "$2"
  return 1
}

# A proof has to depend on the code. Break the C, and the same proof must stop checking.
# usage: must_break NAME MODULE DIR C_FILE FILE_TO_EDIT PROOF SED
must_break() {
  local broken module
  broken=$(mktemp -d -p "$work")
  cp -r "$3" "$broken/src"
  sed -i "$7" "$broken/src/$5"
  if cmp -s "$3/$5" "$broken/src/$5"; then
    printf 'FAIL  %s changed nothing in the C\n' "$1"
    return 1
  fi
  gen "$broken/src/$4" "$2" "$broken" "$work"
  # These two only depend on the globals. If those changed, they may be what stops checking.
  if [ "$2" = Crc ]; then
    if cmp -s "$broken/Crc/Globals.lean" "$work/Crc/Globals.lean"; then
      cp "$work/CrcTables.olean" "$work/CrcSpec.olean" "$broken"
    else
      for module in CrcTables CrcSpec; do
        if stops_checking "$broken" "$root/tests/proofs/$module.lean"; then
          printf 'ok    %s: the proof stops checking\n' "$1"
          return 0
        fi
        in_dir "$broken" lean -R "$root/tests/proofs" -o "$broken/$module.olean" "$root/tests/proofs/$module.lean" >/dev/null
      done
    fi
  fi
  if ! stops_checking "$broken" "$6"; then
    printf 'FAIL  %s: the proof still checks\n' "$1"
    return 1
  fi
  printf 'ok    %s: the proof stops checking\n' "$1"
}

gen "$root/tests/real/bi_reverse.c" Real "$work" &
real=$!
gen "$work/zlib/adler32.c" Zlib "$work" &
adler=$!
gen "$work/zlib/crc32.c" Crc "$work" &
crc=$!
wait "$real"
wait "$adler"
wait "$crc"

if [ "${2:-}" = --generate ]; then
  for module in Real Zlib Crc; do
    mkdir -p "$3/$module"
    cp "$work/$module.lean" "$3"
    cp "$work/$module"/*.lean "$3/$module"
  done
  exit 0
fi

for proof in Adler32 Popcount; do
  start check_proof "$root/tests/proofs/$proof.lean"
done

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

breaks_popcount() { must_break "popcount $1" Real "$root/tests/real" bi_reverse.c bi_reverse.c "$root/tests/proofs/Popcount.lean" "$2"; }
breaks_adler() { must_break "adler32 $1" Zlib "$work/zlib" adler32.c adler32.c "$root/tests/proofs/Adler32.lean" "$2"; }
breaks_crc() { must_break "crc32 $1" Crc "$work/zlib" crc32.c "$2" "$root/tests/proofs/Crc32.lean" "$3"; }

start breaks_popcount 'shifts by 2' 's/x >>= 1;/x >>= 2;/'

start breaks_adler 'wrong modulus' 's/#define BASE 65521U/#define BASE 65519U/'
start breaks_adler 'reads past the end' 's/while (len >= 16) {/while (len >= 15) {/'
start breaks_adler 'wrong sum' 's/#define DO1(buf,i)  {adler += (buf)\[i\]; sum2 += adler;}/#define DO1(buf,i)  {adler += (buf)[i]; sum2 += adler + 1;}/'
start breaks_adler 'skips a byte per block' 's/len -= NMAX;/len -= NMAX - 1;/'
start breaks_adler 'single-byte path forgets the modulus' '/^    if (len == 1) {/,/^    }/ s/if (adler >= BASE)/if (adler > BASE)/'

# Crc32 and the mutants of crc32.c need these two.
check_proof "$root/tests/proofs/CrcTables.lean"
check_proof "$root/tests/proofs/CrcSpec.lean"
start check_proof "$root/tests/proofs/Crc32.lean"

start breaks_crc 'wrong table entry' crc32.h 's/0x77073096/0x77073097/'
start breaks_crc 'wrong braid table entry' crc32.h 's/0xaf449247/0xaf449246/'
start breaks_crc 'reads past the end' crc32.c 's/while (len >= 8) {/while (len >= 7) {/'
start breaks_crc 'no preconditioning' crc32.c 's/crc = (~crc) \& 0xffffffff;/crc = crc \& 0xffffffff;/'
start breaks_crc 'no final inversion' crc32.c 's/return crc ^ 0xffffffff;/return crc;/'
start breaks_crc 'skips a word' crc32.c '0,/words += N;/s//words += N + 1;/'
start breaks_crc 'starts braid too soon' crc32.c 's/if (len >= N \* W + W - 1) {/if (len >= N * W - 2) {/'

failed=0
for pid in "${pids[@]}"; do
  wait "$pid" || failed=1
done
exit $failed
