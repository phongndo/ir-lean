#!/usr/bin/env bash
# shellcheck disable=SC2329 # `start` and `in_dir` call these functions.
# Regenerates Lean from real compiler output, then checks the proofs against it. Anything that
# depends on `sorry` fails, and so does a proof the regenerated code no longer satisfies.
# usage: tests/proofs.sh path/to/llvm-lean [--generate DIR]
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

# Compiles a C file with stock clang and translates it to the Lean module `$2` in the directory `$3`.
# Proofs never run the code, so Lean doesn't have to generate any. PROOF_CFLAGS comes from the dev shell
# and fixes the target, so a proof checks the same IR on every host.
gen() {
  # shellcheck disable=SC2086 # PROOF_CFLAGS is several flags.
  clang $PROOF_CFLAGS -O2 -S -emit-llvm -fno-discard-value-names -D_LARGEFILE64_SOURCE=1 -o "$3/$2.ll" "$1"
  "$tool" "$3/$2.ll" -o "$3/$2.lean" --namespace "$2" --no-code >/dev/null
  in_dir "$3" lean -R "$3" -o "$3/$2.olean" "$3/$2.lean"
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

check_proof() {
  local name=${1##*/}
  if ! in_dir "$work" lean "$1" >"$work/$name.out" 2>&1; then
    printf 'FAIL  %s\n' "$name"
    head -c 4000 "$work/$name.out"
    return 1
  elif grep -q sorryAx "$work/$name.out"; then
    printf 'FAIL  %s depends on sorry\n' "$name"
    return 1
  fi
  printf 'ok    %s (%s axioms besides the standard three)\n' "$name" \
    "$(grep -c '_native' "$work/$name.out" || true)"
}

# A proof has to depend on the code. Break the C, and the same proof must stop checking.
# usage: must_break NAME MODULE DIR C_FILE FILE_TO_EDIT PROOF SED
must_break() {
  local broken
  broken=$(mktemp -d -p "$work")
  cp -r "$3" "$broken/src"
  sed -i "$7" "$broken/src/$5"
  if cmp -s "$3/$5" "$broken/src/$5"; then
    printf 'FAIL  %s changed nothing in the C\n' "$1"
    return 1
  fi
  gen "$broken/src/$4" "$2" "$broken"
  if in_dir "$broken" lean "$6" >/dev/null 2>&1; then
    printf 'FAIL  %s: the proof still checks\n' "$1"
    return 1
  fi
  printf 'ok    %s: the proof stops checking\n' "$1"
}

gen "$root/tests/real/bi_reverse.c" Real "$work"
gen "$work/zlib/adler32.c" Zlib "$work"
gen "$work/zlib/crc32.c" Crc "$work"

if [ "${2:-}" = --generate ]; then
  mkdir -p "$3"
  cp "$work"/{Real,Zlib,Crc}.lean "$3"
  exit 0
fi

for proof in "$root"/tests/proofs/*.lean; do
  start check_proof "$proof"
done

breaks_popcount() { must_break "popcount $1" Real "$root/tests/real" bi_reverse.c bi_reverse.c "$root/tests/proofs/Popcount.lean" "$2"; }
breaks_adler() { must_break "adler32 $1" Zlib "$work/zlib" adler32.c adler32.c "$root/tests/proofs/Adler32.lean" "$2"; }
breaks_crc() { must_break "crc32 $1" Crc "$work/zlib" crc32.c "$2" "$root/tests/proofs/Crc32.lean" "$3"; }

start breaks_popcount 'shifts by 2' 's/x >>= 1;/x >>= 2;/'

start breaks_adler 'wrong modulus' 's/#define BASE 65521U/#define BASE 65519U/'
start breaks_adler 'reads past the end' 's/while (len >= 16) {/while (len >= 15) {/'
start breaks_adler 'wrong sum' 's/#define DO1(buf,i)  {adler += (buf)\[i\]; sum2 += adler;}/#define DO1(buf,i)  {adler += (buf)[i]; sum2 += adler + 1;}/'
start breaks_adler 'skips a byte per block' 's/len -= NMAX;/len -= NMAX - 1;/'
start breaks_adler 'single-byte path forgets the modulus' '/^    if (len == 1) {/,/^    }/ s/if (adler >= BASE)/if (adler > BASE)/'

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
