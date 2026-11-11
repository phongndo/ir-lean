#!/usr/bin/env bash
# The cut lemma, IRLean/Cut.lean, on what ir-lean emits: a proof about a slice of a function becomes a theorem about
# the function. Each loop in tests/cut is translated, with the slice it holds. tests/cut/Q5Kernel.lean proves the loop
# holding llama.cpp's q5_0 bit-spreading slice refines from the slice's own proof, tests/proofs/LlamaBitspread.lean,
# tests/cut/Q5KernelMemory.lean the same of the loop that loads each word and stores its result,
# tests/cut/ClangSum.lean a cut in a loop as clang compiled it, with its attributes and its promise to progress,
# tests/cut/GhAdBlocks.lean a cut in a kernel of the corpus as clang compiled it, libsodium's gh_ad_blocks, whose
# loops load vectors, multiply them with PCLMULQDQ and store an accumulator the next loop loads again,
# tests/cut/CutPromisedCases.lean a loop under that promise, and tests/cut/CutCases.lean a loop whose cut is refined
# and not equal, that it doesn't refine the other way, and that the lemma needs each of its hypotheses. They build
# with warnings as errors, rest on the axioms their slices' proofs do, and replay in the kernel. A wrong cut, a wrong
# loop, a wrong lemma and a wrong operation each have to stop a proof with an error of its own, where it's wrong.
# Alive2 gives each loop the theorem's verdict. See docs/refinement.md.
# Bounded: one Lean or Alive2 process at a time, each Lean process with a memory cap and a time limit, writing only to
# a temporary directory. GhAdBlocks.lean's cap is its own, KERNEL_MAX_MB, since it needs more than the rest. Needs
# `lake build`, and libsodium's source, which Nix fetches at the corpus's pin if the store doesn't have it.
# usage: tests/cut.sh path/to/ir-lean
set -euo pipefail
tool=$(realpath "$1")
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mb=${LEAN_MAX_MB:-4000}
kernel_mb=${KERNEL_MAX_MB:-8000}
secs=${CUT_TIMEOUT:-600}
export LEAN_PATH="$work:$root/.lake/build/lib/lean"
lean_bin=$(command -v lean)
lean() { timeout "$secs" "$lean_bin" -M "$mb" "$@"; }
failed=0
fail() {
  printf 'FAIL  %s\n' "$1"
  [ -n "${2:-}" ] && printf '%s\n' "${2:0:4000}"
  failed=1
}
# A check that stopped at a limit decides nothing, so it's unknown, with the limit, and not a failure of the proof.
# The test still fails, since the evidence it asks for isn't there.
limited=0
unknown() {
  printf 'UNKNOWN  %s\n' "$1"
  [ -n "${2:-}" ] && printf '%s\n' "${2:0:4000}"
  failed=1
  limited=1
}
# Resource limits say a proof might check with more, so they never count as a failure of its own.
limit='maximum number of heartbeats|deterministic\)? timeout|maximum recursion depth|deep recursion|stack overflow|'
limit+='excessive memory|out of memory|maximum number of steps'
slice=tests/real/llama_q5_bitspread.ll

# The lemma and the operations that keep refinement: on the standard axioms alone, replayed in the kernel.
for module in IRLean.Cut IRLean.CutPromised IRLean.Mono IRLean.MonoX86; do
  if out=$(IRLEAN_CHECK_MODULE=$module lean tests/check_axioms.lean 2>&1) && grep -q 'and 0 from bv_decide' <<<"$out" &&
    replay=$(timeout "$secs" leanchecker "$module" 2>&1); then
    printf 'ok    %s: %s, and leanchecker replays it\n' "$module" "$out"
  else
    fail "$module: axioms and replay" "$out ${replay:-}"
  fi
done

# The instructions of FUNCTION in FILE, without its `ret`.
# usage: body FUNCTION FILE
body() {
  awk -v f="@$1(" 'index($0, "define ") == 1 { on = index($0, f) > 0; next } on && /^}/ { on = 0 } on && /^  %/' "$2"
}
# The kernels' loops hold the slice and its replacement, word for word.
for kernel in tests/cut/q5_kernel.ll tests/cut/q5_kernel_memory.ll; do
  held=1
  for side in src tgt; do
    missing=$(grep -Fxvf <(body "$side" "$kernel") <(body "$side" "$slice") || true)
    if [ -z "$(body "$side" "$slice")" ] || [ -n "$missing" ]; then
      fail "$kernel's @$side doesn't hold every instruction of $slice's @$side" "$missing"
      held=0
    fi
  done
  [ "$held" = 1 ] && printf 'ok    %s holds the instructions of %s, both sides\n' "$kernel" "$slice"
done

# The function with clang's attributes is what clang makes of tests/cut/clang_sum.c: compiled again, as the fixture
# was, its function and its attributes are the fixture's @src and #0, to the letter.
# usage: fn_text NAME FILE
fn_text() {
  awk -v f="@$1(" 'index($0, "define ") == 1 && index($0, f) > 0 { on = 1 } on { print } on && /^}/ { exit }' "$2"
}
if ! out=$(clang -O1 -fno-strict-aliasing -fno-vectorize -fno-unroll-loops -S -emit-llvm tests/cut/clang_sum.c \
  -o "$work/clang_sum.c.ll" 2>&1); then
  fail "clang doesn't compile tests/cut/clang_sum.c" "$out"
elif [ -z "$(fn_text sum "$work/clang_sum.c.ll")" ] ||
  ! diff <(fn_text sum "$work/clang_sum.c.ll" | sed 's/@sum(/@src(/') <(fn_text src tests/cut/clang_sum.ll) \
    >"$work/clang.diff" ||
  ! diff <(grep '^attributes #0 ' "$work/clang_sum.c.ll") <(grep '^attributes #0 ' tests/cut/clang_sum.ll) \
    >>"$work/clang.diff"; then
  fail "tests/cut/clang_sum.ll's @src isn't what clang makes of tests/cut/clang_sum.c" "$(cat "$work/clang.diff")"
else
  printf 'ok    tests/cut/clang_sum.ll holds what %s makes of tests/cut/clang_sum.c\n' \
    "$(clang --version | head -1)"
fi

# The corpus's kernel is what clang makes of libsodium's AES-GCM unit at the corpus's pin, with the corpus's flags, the
# project's and the unit's, as bench/kernels/manifest.toml has them: compiled again, gh_ad_blocks and its attributes
# are the fixture's @src and #10, to the letter.
# usage: compile_sodium SOURCE OUT
compile_sodium() {
  # shellcheck disable=SC2086 # PROOF_CFLAGS is several flags.
  NIX_HARDENING_ENABLE='' NIX_ENFORCE_NO_NATIVE=0 clang -O3 -fomit-frame-pointer -momit-leaf-frame-pointer \
    -DCONFIGURED=1 -DHAVE_MMINTRIN_H=1 -DHAVE_EMMINTRIN_H=1 -DHAVE_PMMINTRIN_H=1 -DHAVE_TMMINTRIN_H=1 \
    -DHAVE_SMMINTRIN_H=1 -DHAVE_AVXINTRIN_H=1 -DHAVE_AVX2INTRIN_H=1 -DHAVE_AVX512FINTRIN_H=1 -DHAVE_WMMINTRIN_H=1 \
    -DHAVE_RDRAND=1 -DNATIVE_LITTLE_ENDIAN=1 -DHAVE_INLINE_ASM=1 -DHAVE_AMD64_ASM=1 -DHAVE_AVX_ASM=1 -DHAVE_TI_MODE=1 \
    -DHAVE_CPUID=1 -DHAVE_WEAK_SYMBOLS=1 -DHAVE_ATOMIC_OPS=1 -D_GNU_SOURCE=1 -D_FORTIFY_SOURCE=3 -pthread \
    -fvisibility=hidden -fPIC -fno-strict-aliasing -fno-strict-overflow -fstack-protector -ftls-model=global-dynamic \
    -mavx -maes -mpclmul -I"$1/src/libsodium/include/sodium" -I"$1/src/libsodium/include" ${PROOF_CFLAGS:-} \
    -S -emit-llvm -o "$2" "$1/src/libsodium/crypto_aead/aes256gcm/aesni/aead_aes256gcm_aesni.c"
}
sodium_rev=77e1ce5d6dee871c49ef211222ba18ef0c486bda
sodium_hash=sha256-k8u7iNqvjLA0PptbneDyE8zCtutJlV2LirrRb41tmBY=
if ! sodium=$(timeout 1800 nix eval --raw --expr "(builtins.fetchTree { type = \"github\"; owner = \"jedisct1\";
  repo = \"libsodium\"; rev = \"$sodium_rev\"; narHash = \"$sodium_hash\"; }).outPath" 2>"$work/sodium.err") ||
  [ ! -d "$sodium/src/libsodium" ]; then
  # Only stdout is the path: on a fetch, Nix says what it's unpacking on stderr, which isn't part of it.
  fail "Nix can't fetch libsodium at $sodium_rev, so tests/cut/gh_ad_blocks.ll's @src can't be checked" \
    "$(cat "$work/sodium.err") $sodium"
elif ! out=$(compile_sodium "$sodium" "$work/aead_aes256gcm_aesni.ll" 2>&1); then
  fail "clang doesn't compile libsodium's aead_aes256gcm_aesni.c" "$out"
elif [ -z "$(fn_text gh_ad_blocks "$work/aead_aes256gcm_aesni.ll")" ] ||
  ! diff <(fn_text gh_ad_blocks "$work/aead_aes256gcm_aesni.ll" | sed 's/@gh_ad_blocks(/@src(/') \
    <(fn_text src tests/cut/gh_ad_blocks.ll) >"$work/sodium.diff" ||
  ! diff <(grep '^attributes #10 ' "$work/aead_aes256gcm_aesni.ll") <(grep '^attributes #10 ' tests/cut/gh_ad_blocks.ll) \
    >>"$work/sodium.diff"; then
  fail "tests/cut/gh_ad_blocks.ll's @src isn't what clang makes of libsodium's gh_ad_blocks" "$(cat "$work/sodium.diff")"
else
  printf 'ok    tests/cut/gh_ad_blocks.ll holds what %s makes of libsodium %s'"'"'s gh_ad_blocks\n' \
    "$(clang --version | head -1)" "${sodium_rev:0:12}"
fi

# Each case as the module CASE_ir, the slice as LlamaBitspreadIR, and the slice's own proof.
# usage: translate FILE NAMESPACE DIR
translate() {
  local out
  if ! out=$("$tool" "$1" -o "$3/$2.lean" --namespace "$2" --no-code 2>&1) ||
    ! out=$(lean -R "$3" -o "$3/$2.olean" "$3/$2.lean" 2>&1); then
    fail "$1 doesn't translate and compile" "$out"
    return 1
  fi
}
cases=(tests/cut/*.ll)
translated=1
for file in "${cases[@]}"; do
  out=$(opt -passes=verify -disable-output "$file" 2>&1) || fail "$file isn't valid LLVM IR" "$out"
  translate "$file" "$(basename "$file" .ll)_ir" "$work" || translated=0
done
translate "$slice" LlamaBitspreadIR "$work" || translated=0
if ! out=$(lean -DwarningAsError=true -R tests/proofs -o "$work/LlamaBitspread.olean" \
  tests/proofs/LlamaBitspread.lean 2>&1); then
  fail 'tests/proofs/LlamaBitspread.lean' "$out"
  translated=0
fi
[ "$translated" = 1 ] && printf 'ok    %s loops and the slice translated, and the slice proved\n' "${#cases[@]}"

# Every case has its theorem.
for file in "${cases[@]}"; do
  name=$(basename "$file" .ll)
  grep -q "^theorem $name :" tests/cut/*.lean || fail "no file of theorems in tests/cut has a theorem $name"
done

# The theorems, with warnings as errors, replayed in the kernel. The cases rest on the standard axioms alone. The
# kernel's theorem rests on what its slice's proof does, and adds nothing: every bv_decide axiom is the slice's.
# usage: check MODULE GENERATED THEOREMS
check() {
  local out replay status=0
  out=$(lean -DwarningAsError=true -R tests/cut -o "$work/$1.olean" "tests/cut/$1.lean" 2>&1) || status=$?
  if [ "$status" != 0 ]; then
    # timeout exits 124, and a process the kernel killed for memory 137.
    if [ "$status" = 124 ] || [ "$status" = 137 ] || grep -qE "$limit" <<<"$out"; then
      unknown "tests/cut/$1.lean stopped at a limit (exit $status), so it's neither proved nor refuted" "$out"
    else
      fail "tests/cut/$1.lean" "$out"
    fi
    return 1
  fi
  if ! out=$(IRLEAN_CHECK_MODULE=$1 IRLEAN_CHECK_GENERATED=$2 IRLEAN_CHECK_THEOREMS=$3 lean tests/check_axioms.lean 2>&1); then
    fail "$1: axioms" "$out"
    return 1
  fi
  replay=$(timeout "$secs" leanchecker "$1" 2>&1) || status=$?
  if [ "$status" != 0 ]; then
    if [ "$status" = 124 ] || [ "$status" = 137 ] || grep -qE "$limit" <<<"$replay"; then
      unknown "$1: leanchecker stopped at a limit (exit $status), so its replay decided nothing" "$replay"
    else
      fail "$1: replay" "$replay"
    fi
    return 1
  fi
  printf 'ok    %s: %s, and leanchecker replays it\n' "$1" "$out"
  axioms=$out
}
built=1
axioms=
check CutCases drop_nuw_loop_ir $'drop_nuw_cut drop_nuw_loop_ir.cut_src\ndrop_nuw_cut drop_nuw_loop_ir.cut_tgt
drop_nuw_loop drop_nuw_loop_ir.src\ndrop_nuw_loop drop_nuw_loop_ir.tgt
drop_nuw_loop_converse drop_nuw_loop_ir.src\ndrop_nuw_loop_converse drop_nuw_loop_ir.tgt' || built=0
grep -q 'and 0 from bv_decide' <<<"$axioms" || fail "CutCases rests on more than the standard axioms: $axioms"
check CutPromisedCases drop_nuw_promised_ir $'drop_nuw_promised drop_nuw_promised_ir.src
drop_nuw_promised drop_nuw_promised_ir.tgt' || built=0
grep -q 'and 0 from bv_decide' <<<"$axioms" || fail "CutPromisedCases rests on more than the standard axioms: $axioms"
check ClangSum clang_sum_ir $'clang_sum clang_sum_ir.src\nclang_sum clang_sum_ir.tgt
cut clang_sum_ir.cut_src\ncut clang_sum_ir.cut_tgt' || built=0
grep -q 'and 0 from bv_decide' <<<"$axioms" || fail "ClangSum rests on more than the standard axioms: $axioms"
# A kernel of the corpus, with its own cap: its blocks are long, and Lean needs more than 4 GB for them.
saved_mb=$mb
mb=$kernel_mb
check GhAdBlocks gh_ad_blocks_ir $'gh_ad_blocks gh_ad_blocks_ir.src\ngh_ad_blocks gh_ad_blocks_ir.tgt
cut gh_ad_blocks_ir.cut_src\ncut gh_ad_blocks_ir.cut_tgt' || built=0
mb=$saved_mb
grep -q 'and 0 from bv_decide' <<<"$axioms" || fail "GhAdBlocks rests on more than the standard axioms: $axioms"
check Q5Kernel 'q5_kernel_ir LlamaBitspreadIR' $'q5_kernel q5_kernel_ir.src\nq5_kernel q5_kernel_ir.tgt
slice LlamaBitspreadIR.src\nslice LlamaBitspreadIR.tgt' || built=0
kernel=$(grep -oE 'and [0-9]+ from bv_decide' <<<"$axioms" || true)
check Q5KernelMemory 'q5_kernel_memory_ir LlamaBitspreadIR' \
  $'q5_kernel_memory q5_kernel_memory_ir.src\nq5_kernel_memory q5_kernel_memory_ir.tgt' || built=0
memory=$(grep -oE 'and [0-9]+ from bv_decide' <<<"$axioms" || true)
if ! out=$(IRLEAN_CHECK_MODULE=LlamaBitspread lean tests/check_axioms.lean 2>&1) || [ -z "$kernel" ] ||
  [ "$(grep -oE 'and [0-9]+ from bv_decide' <<<"$out")" != "$kernel" ] || [ "$memory" != "$kernel" ]; then
  fail "a kernel's theorem doesn't rest on exactly its slice's axioms: $kernel and $memory, and the slice's proof: $out"
else
  printf 'ok    neither kernel adds an axiom to its slice'"'"'s: %s\n' "$kernel"
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
# usage: must_fail WHAT FILE THEOREM [LEAN_PATH]
must_fail() {
  local what=$1 file=$2 theorem=$3 expect=${5:-} status=0 out errors hit
  out=$(LEAN_PATH=${4:-$LEAN_PATH} lean -R "$(dirname "$file")" "$file" 2>&1) || status=$?
  errors=$(grep -E "^$file:[0-9]+:[0-9]+: error" <<<"$out" | grep -v "^$file:1:0:" | grep -vE "$limit" || true)
  if [ "$status" = 0 ]; then
    fail "$what checks, so something wrong was certified" "$out"
  elif [ -z "$errors" ]; then
    fail "$what stops only at a resource limit, at its imports, or never says why" "$out"
  elif grep -qiE 'unknown (identifier|constant|tactic|namespace)|unexpected (token|identifier)' <<<"$errors"; then
    fail "$what fails because the proof text can't be read (a renamed or removed name), not because it's wrong" "$out"
  elif ! hit=$(theorems_with_errors "$file" <<<"$errors" | grep -xF "$theorem"); then
    fail "$what doesn't stop $theorem with an error of its own, only $(theorems_with_errors "$file" <<<"$errors" |
      tr '\n' ' ')" "$out"
  elif [ -n "$expect" ] && ! grep -qE "$expect" <<<"$out"; then
    fail "$what stops $theorem, but not where it should: nothing Lean says matches $expect" "$out"
  else
    printf 'ok    %s stops %s: %s\n' "$what" "$hit" "$(head -1 <<<"$errors" | sed "s|$work/||" | cut -c1-140)"
  fi
}

if [ "$built" = 0 ]; then
  if [ "$limited" = 1 ]; then
    unknown "the wrong versions can't be checked, since a right one stopped at a limit"
  else
    fail "the wrong versions can't be checked, since the right ones didn't build"
  fi
  exit 1
fi

# A cut that isn't refined: the cut's proof, with its sides swapped.
must_fail 'a cut that is not refined' tests/cut/must_fail/AddNuwLoop.lean add_nuw_cut

# A wrong operation stops the lemma about it, where the operation is wrong. Each is an operation changed so that it
# no longer keeps refinement, and the proof that it does, as the right one's is written, has to stop at the
# obligation it breaks: a lane-wise function that isn't poison for poison, an x86 intrinsic whose poison rule
# forgets a lane it reads, and `sdiv` with a poison dividend that can't overflow.
must_fail 'a lane-wise operation whose function on a lane is not poison for poison' \
  tests/cut/must_fail/LanewiseNotStrict.lean pavg_frozen_mono "$LEAN_PATH" '⊢ some .*none\.getD 0.* = none'
must_fail 'PCLMULQDQ with a poison rule that forgets a quadword it reads' \
  tests/cut/must_fail/X86PoisonRule.lean pclmulqdq_forgets_mono "$LEAN_PATH" 'clmul64 x \(none\.getD 0\)'
must_fail 'sdiv with a poison dividend that never overflows' \
  tests/cut/must_fail/SdivPoisonDividend.lean divOverflowsWrong_mono "$LEAN_PATH" \
  "x' = BitVec.intMin w → ¬y = BitVec.allOnes w"

# A loop that isn't the slice and then the rest stops its kernel's proof. Each is a kernel with its target changed,
# translated again, under the unchanged proof and the unchanged modules it imports. EXPECT, if given, is what Lean's
# error has to say, for a mutant that could stop the proof somewhere other than where it's wrong.
# usage: wrong_kernel WHAT CASE PROOF THEOREM EDIT [EXPECT]
wrong_kernel() {
  local what=$1 case=$2 proof=$3 theorem=$4 dir out
  dir=$(mktemp -d -p "$work")
  cp "$work"/*.olean "$dir/"
  python3 - "tests/cut/$case.ll" "$dir/$case.ll" "$5" <<'PY'
from pathlib import Path
import sys

# The target is the last function.
head, tail = Path(sys.argv[1]).read_text().rsplit("\ndefine ", 1)
mask = ", ".join(f"i32 {1 if i == 0 else i}" for i in range(32))
edits = {
    # Output lane zero reads input bit one, as tests/llama-bitspread.sh's wrong replacement does.
    "wrong bit": [
        ("  %out = select", f"  %wrong = shufflevector <32 x i1> %mask, <32 x i1> poison, <32 x i32> <{mask}>\n"
         "  %out = select"),
        ("select <32 x i1> %mask,", "select <32 x i1> %wrong,"),
    ],
    # The replacement is right, and the loop steps by two.
    "skips a round": [("  %i1 = add i32 %i, 1", "  %i1 = add i32 %i, 2")],
    # The replacement is right, and each round loads the word after the one the source loads.
    "next word": [("  %at = zext i32 %i to i64", "  %to = zext i32 %i to i64\n  %at = add i64 %to, 1")],
    # The replacement is right, and what's added up goes 32 bytes past the pointer it should. %dst stays in use, so
    # the target's blocks take the same values as the source's, and the proof can only stop at the store.
    "other pointer": [
        ("  store <32 x i8> %acc, ptr %dst, align 1",
         "  %past = getelementptr i8, ptr %dst, i64 32\n  store <32 x i8> %acc, ptr %past, align 1"),
    ],
    # clang's loop, with four times the word and the word, which is five times it and not three.
    "five times": [("  %twice = shl i32 %12, 1", "  %twice = shl i32 %12, 2")],
    # The corpus's kernel, with the main loop's accumulator stored 16 bytes past where the next loop loads it. %1
    # stays in use, so the blocks take the same values on both sides, and the proof can only stop at the store.
    "accumulator elsewhere": [
        ("  store <2 x i64> %229, ptr %1, align 16",
         "  %past = getelementptr i8, ptr %1, i64 16\n  store <2 x i64> %229, ptr %past, align 16"),
    ],
}
for old, new in edits[sys.argv[3]]:
    assert tail.count(old) == 1, old
    tail = tail.replace(old, new)
Path(sys.argv[2]).write_text(head + "\ndefine " + tail)
PY
  if ! out=$(opt -passes=verify -disable-output "$dir/$case.ll" 2>&1) ||
    ! out=$("$tool" "$dir/$case.ll" -o "$dir/${case}_ir.lean" --namespace "${case}_ir" --no-code 2>&1) ||
    ! out=$(lean -R "$dir" -o "$dir/${case}_ir.olean" "$dir/${case}_ir.lean" 2>&1); then
    fail "the kernel whose target $what doesn't translate, so it can't show anything" "$out"
    return
  fi
  cp "tests/cut/$proof.lean" "$dir/"
  must_fail "a kernel whose target $what" "$dir/$proof.lean" "$theorem" "$dir:$root/.lake/build/lib/lean" "${6:-}"
}
wrong_kernel 'reads the wrong bit' q5_kernel Q5Kernel tgt_body 'wrong bit'
wrong_kernel 'skips a round' q5_kernel Q5Kernel tgt_body 'skips a round'
wrong_kernel 'reads the wrong bit, with memory' q5_kernel_memory Q5KernelMemory tgt_body 'wrong bit'
wrong_kernel 'loads the next word' q5_kernel_memory Q5KernelMemory tgt_body 'next word'
wrong_kernel 'stores past its pointer' q5_kernel_memory Q5KernelMemory step_sim 'other pointer' \
  "storeVec \\(m\\.gep dst' \\(some 32#64\\)\\)"
wrong_kernel 'adds up five times each word, as clang compiled it' clang_sum ClangSum tgt_body 'five times'
saved_mb=$mb
mb=$kernel_mb
wrong_kernel 'stores its accumulator past its pointer, in a kernel of the corpus' gh_ad_blocks GhAdBlocks step_bb5 \
  'accumulator elsewhere' "Refine\\.le a1 \\(m'\\.gep a1' \\(some 16#64\\)\\)"
mb=$saved_mb

# A wrong lemma. Each mutant changes a definition in a copy of IRLean/Cut.lean, so that something wrong would be
# allowed, and the copy's own lemmas have to stop on it.
# usage: lemma_mutant NAME SED_EXPRESSION THEOREM
lemma_mutant() {
  local dir
  dir=$(mktemp -d -p "$work")
  sed "$2" IRLean/Cut.lean >"$dir/Cut.lean"
  if cmp -s IRLean/Cut.lean "$dir/Cut.lean"; then
    fail "lemma mutant $1 doesn't change IRLean/Cut.lean"
    return
  fi
  must_fail "lemma mutant $1" "$dir/Cut.lean" "$3"
}
# A source that never finishes allows a target that returns.
lemma_mutant 'a run that never finishes allows anything' 's/^  | none => b = none$/  | none => True/' le_iff_sim
# A result allows a target that's undefined, or never finishes.
lemma_mutant 'a result allows a run with none' \
  's/^  | some (.ok x) => ∃ y, b = some (.ok y) ∧ r x y$/  | some (.ok x) => ∀ y, b = some (.ok y) → r x y/' le_iff_sim
# The guard takes out every input, not only those where the source stops the model.
lemma_mutant 'the guard hides every run' 's/^  | o => o$/  | _ => Outcome.ub .assumeFailed/' answered_iff
# A block that returns is in step with one that jumps.
lemma_mutant 'a return matches a jump' 's/^  | _, _ => False$/  | _, _ => True/' runFuel_sim

# Alive2's verdict on each loop is the theorem's.
if ! tests/calls_alive.py tests/cut tests/cut/*.lean; then
  failed=1
fi

exit "$failed"
