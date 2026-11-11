#!/usr/bin/env bash
# Builds a kernel-corpus candidate the way the project builds itself, with the dev shell's clang, runs its
# workload under `perf record`, and prints the functions the processor spent its time in. docs/kernels.md.
#
# It says which functions are hot. It times nothing, changes nothing, and searches for nothing.
#
# usage: bench/kernels/profile.sh NAME INPUTS
#   NAME    zlib-ng, zstd, libdeflate, xxhash, flac, libwebp, libsodium, opus or base64
#   INPUTS  a directory holding the workloads' inputs, as `bench/kernels/kernels.py inputs INPUTS` fetches them:
#           silesia.tar, made from silesia.zip, sintel-master-st.flac, and the WebP gallery's files
# Builds in build/kernels/profile/NAME, with 8 compile jobs. Needs `nix develop`, on Linux, for perf.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
name=${1:?usage: bench/kernels/profile.sh NAME INPUTS}
inputs=$(cd "${2:?usage: bench/kernels/profile.sh NAME INPUTS}" && pwd)
work=$root/build/kernels/profile/$name
mkdir -p "$work"
src=$("$root/bench/kernels/kernels.py" source "$name")

# Stock clang: without the hardening and frame pointers the dev shell's wrapper adds, as tests/llama_bench.py has it.
export NIX_ENFORCE_NO_NATIVE=0 NIX_HARDENING_ENABLE="" CC=clang CXX=clang++
unset SOURCE_DATE_EPOCH

configure() { cmake -S "$1" -B "$work/b" -G Ninja -DCMAKE_BUILD_TYPE=Release "${@:2}" >"$work/configure.log"; }
build() { ninja -C "$work/b" -j8 "$@" >"$work/build.log"; }
# Records one workload, and prints each function with at least 1.5% of the cycles spent in user code.
profile() {
  local label=$1
  shift
  perf record -q -e cycles:u -o "$work/$label.data" -- "$@" >"$work/$label.out" 2>&1
  echo "== $name, $label: $*"
  perf report -i "$work/$label.data" --stdio --sort dso,symbol --percent-limit 1.5 2>/dev/null |
    grep -v '^#' | grep -v '^$' | sed 's/  */ /g'
}

case $name in
zlib-ng)
  configure "$src" -DBUILD_TESTING=ON -DWITH_GTEST=OFF
  build minigzip
  profile compress sh -c "'$work/b/minigzip' -6 -c '$inputs/silesia.tar' >'$work/silesia.tar.gz'"
  profile decompress sh -c "'$work/b/minigzip' -d -c '$work/silesia.tar.gz' >/dev/null"
  ;;
zstd)
  configure "$src/build/cmake" -DZSTD_BUILD_TESTS=OFF
  build zstd
  profile level3 "$work/b/programs/zstd" -b3 -i5 "$inputs/silesia.tar"
  profile level19 "$work/b/programs/zstd" -b19 -i5 "$inputs/silesia.tar"
  ;;
libdeflate)
  configure "$src" -DLIBDEFLATE_BUILD_TESTS=ON
  build benchmark
  profile level6 "$work/b/programs/benchmark" -6 "$inputs/silesia.tar"
  ;;
xxhash)
  # Its Makefile builds in the source tree, so on a copy.
  rm -rf "$work/src"
  cp -r "$src" "$work/src"
  chmod -R u+w "$work/src"
  make -C "$work/src" -j8 xxhsum >"$work/build.log" 2>&1
  profile bench "$work/src/xxhsum" -b -i5
  profile file sh -c "for i in 1 2 3 4 5 6 7 8 9 10; do '$work/src/xxhsum' -H3 '$inputs/silesia.tar'; done"
  ;;
flac)
  configure "$src" -DWITH_OGG=OFF -DBUILD_TESTING=OFF -DBUILD_EXAMPLES=OFF -DBUILD_DOCS=OFF \
    -DINSTALL_MANPAGES=OFF -DBUILD_CXXLIBS=OFF
  build flacapp
  "$work/b/src/flac/flac" -s -d -f -o "$work/sintel.wav" "$inputs/sintel-master-st.flac"
  profile decode "$work/b/src/flac/flac" -s -d -f -o "$work/out.wav" "$inputs/sintel-master-st.flac"
  profile encode5 "$work/b/src/flac/flac" -s -5 -f -o "$work/out5.flac" "$work/sintel.wav"
  profile encode8 "$work/b/src/flac/flac" -s -8 -f -o "$work/out8.flac" "$work/sintel.wav"
  ;;
libwebp)
  configure "$src"
  build dwebp cwebp
  loop='for n in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20; do'
  five='for i in 1 2 3 4 5; do'
  profile decode sh -c "$loop $five '$work/b/dwebp' '$inputs/'\$i.webp -ppm -o '$work/o.ppm'; done; done"
  profile decode-lossless sh -c "$loop $five '$work/b/dwebp' '$inputs/'\${i}_webp_ll.webp -pam -o '$work/'\$i.pam; done; done"
  # cwebp is built without libpng here, so it encodes the lossless images' pixels, which dwebp just wrote.
  profile encode sh -c "$five '$work/b/cwebp' -quiet -q 75 '$work/'\$i.pam -o '$work/o.webp'; done"
  profile encode-lossless sh -c "$five '$work/b/cwebp' -quiet -lossless '$work/'\$i.pam -o '$work/o.webp'; done"
  ;;
libsodium)
  mkdir -p "$work/b"
  (cd "$work/b" && "$src/configure" --disable-dependency-tracking >"$work/configure.log" 2>&1)
  make -C "$work/b" -j8 >"$work/build.log" 2>&1
  # test/default/cmptest.h: with BENCHMARKS, a test runs its body ITERATIONS times and prints the time.
  tests="aead_chacha20poly1305 aead_xchacha20poly1305 secretbox generichash pwhash_argon2id aead_aes256gcm"
  # shellcheck disable=SC2086 # The tests are separate words.
  make -C "$work/b/test/default" -j8 CPPFLAGS="-DBENCHMARKS -DITERATIONS=200" $tests >>"$work/build.log" 2>&1
  for t in $tests; do
    (cd "$src/test/default" && profile "$t" "$work/b/test/default/$t")
  done
  ;;
opus)
  configure "$src" -DOPUS_BUILD_PROGRAMS=ON
  build opus_demo
  flac=$root/build/kernels/profile/flac/b/src/flac/flac
  "$flac" -s -d -f --force-raw-format --endian=little --sign=signed -o "$work/sintel.raw" \
    "$inputs/sintel-master-st.flac"
  profile encode "$work/b/opus_demo" -e audio 48000 2 96000 "$work/sintel.raw" "$work/sintel.bit"
  profile decode "$work/b/opus_demo" -d 48000 2 "$work/sintel.bit" "$work/out.raw"
  ;;
base64)
  configure "$src" -DBASE64_BUILD_TESTS=ON
  build benchmark
  profile bench "$work/b/bin/benchmark"
  ;;
*)
  echo "no profile for $name" >&2
  exit 2
  ;;
esac
