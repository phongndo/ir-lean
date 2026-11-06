#!/usr/bin/env bash
# Regenerates Lean from real compiler output, then checks the proofs against it. Anything that
# depends on `sorry` fails, and so does a proof the regenerated code no longer satisfies.
# usage: tests/proofs.sh path/to/llvm-lean
set -euo pipefail
tool=$(realpath "$1")
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$root/.lake/build/lib/lean:$work"
# A runaway proof fails with Lean's own error instead of taking the machine's memory.
lean() { command lean -M "${LEAN_MAX_MB:-4000}" "$@"; }

# zlib's own source, at the version the flake pins.
zlib_src=${ZLIB_SRC:-$(nix build --inputs-from "$root" --no-link --print-out-paths nixpkgs#zlib.src)}
mkdir "$work/zlib"
tar -xf "$zlib_src" -C "$work/zlib" --strip-components=1

# Compiles a C file with stock clang and translates it to the Lean module `$2`. Proofs never run the
# code, so Lean doesn't have to generate any.
gen() {
  clang -O2 -S -emit-llvm -fno-discard-value-names -D_LARGEFILE64_SOURCE=1 -o "$work/$2.ll" "$1"
  "$tool" "$work/$2.ll" -o "$work/$2.lean" --namespace "$2" --no-code >/dev/null
  lean -R "$work" -o "$work/$2.olean" "$work/$2.lean"
}

gen "$root/tests/real/bi_reverse.c" Real
gen "$work/zlib/adler32.c" Zlib
gen "$work/zlib/crc32.c" Crc

failed=0
for proof in "$root"/tests/proofs/*.lean; do
  name=${proof##*/}
  if ! lean "$proof" >"$work/out" 2>&1; then
    printf 'FAIL  %s\n' "$name"
    head -c 4000 "$work/out"
    failed=1
  elif grep -q sorryAx "$work/out"; then
    printf 'FAIL  %s depends on sorry\n' "$name"
    failed=1
  else
    printf 'ok    %s (%s axioms besides the standard three)\n' "$name" \
      "$(grep -c '_native' "$work/out" || true)"
  fi
done

# A proof has to depend on the code. Break the C, and the same proof must stop checking.
# usage: must_break NAME MODULE DIR C_FILE FILE_TO_EDIT PROOF SED
must_break() {
  rm -rf "$work/broken"
  cp -r "$3" "$work/broken"
  sed -i "$7" "$work/broken/$5"
  if cmp -s "$3/$5" "$work/broken/$5"; then
    printf 'FAIL  %s changed nothing in the C\n' "$1"
    failed=1
    return
  fi
  gen "$work/broken/$4" "$2"
  if lean "$6" >/dev/null 2>&1; then
    printf 'FAIL  %s: the proof still checks\n' "$1"
    failed=1
  else
    printf 'ok    %s: the proof stops checking\n' "$1"
  fi
}

must_break 'popcount shifts by 2' Real "$root/tests/real" bi_reverse.c bi_reverse.c \
  "$root/tests/proofs/Popcount.lean" 's/x >>= 1;/x >>= 2;/'

breaks_adler() { must_break "adler32 $1" Zlib "$work/zlib" adler32.c adler32.c "$root/tests/proofs/Adler32.lean" "$2"; }
breaks_adler 'wrong modulus' 's/#define BASE 65521U/#define BASE 65519U/'
breaks_adler 'reads past the end' 's/while (len >= 16) {/while (len >= 15) {/'
breaks_adler 'wrong sum' 's/#define DO1(buf,i)  {adler += (buf)\[i\]; sum2 += adler;}/#define DO1(buf,i)  {adler += (buf)[i]; sum2 += adler + 1;}/'
breaks_adler 'skips a byte per block' 's/len -= NMAX;/len -= NMAX - 1;/'
breaks_adler 'single-byte path forgets the modulus' '/^    if (len == 1) {/,/^    }/ s/if (adler >= BASE)/if (adler > BASE)/'
gen "$work/zlib/adler32.c" Zlib

breaks_crc() { must_break "crc32 $1" Crc "$work/zlib" crc32.c "$2" "$root/tests/proofs/Crc32.lean" "$3"; }
breaks_crc 'wrong table entry' crc32.h 's/0x77073096/0x77073097/'
breaks_crc 'wrong braid table entry' crc32.h 's/0xaf449247/0xaf449246/'
breaks_crc 'reads past the end' crc32.c 's/while (len >= 8) {/while (len >= 7) {/'
breaks_crc 'no preconditioning' crc32.c 's/crc = (~crc) \& 0xffffffff;/crc = crc \& 0xffffffff;/'
breaks_crc 'no final inversion' crc32.c 's/return crc ^ 0xffffffff;/return crc;/'
breaks_crc 'skips a word' crc32.c '0,/words += N;/s//words += N + 1;/'
breaks_crc 'starts braid too soon' crc32.c 's/if (len >= N \* W + W - 1) {/if (len >= N * W - 2) {/'
exit $failed
