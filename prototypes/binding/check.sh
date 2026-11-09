#!/usr/bin/env bash
# The prototype, end to end: compiles `llvm::isKnownNegation` from the pinned ValueTracking.cpp, cuts its three calls
# out of the module, translates it with ir-lean, checks the layout against the pinned libLLVM, and checks the proof
# that it computes #47's model: warnings as errors, the standard axioms only, and leanchecker. Then two bugs put into
# the C++ each have to stop the proof. See README.md and docs/binding-approach.md.
#
# usage: prototypes/binding/check.sh IR_LEAN WORK_DIR
# Needs `nix develop` and `lake build IRLean`. Each Lean process is capped by its -M.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
irlean=$(realpath "$1")
work=$(mkdir -p "$2/check" && realpath "$2/check")
src=${LLVM_PROJECT_SRC:?run inside nix develop}
memory=${LEAN_MEMORY_MB:-3000}
fn=_ZN4llvm15isKnownNegationEPKNS_5ValueES2_bb
cut=(_ZNK4llvm5APInt25countLeadingZerosSlowCaseEv
  _ZNK4llvm12PatternMatch14cstval_pred_tyINS0_11is_zero_intENS_11ConstantIntELb1EE11matchVectorEPKNS_5ValueE
  _ZNK4llvm11Instruction15hasNoSignedWrapEv)

fail() {
  echo "FAIL $*" >&2
  exit 1
}

# The pin: llvm-project's NAR hash is targets.toml's, and ValueTracking.cpp is the file #47 quotes.
want=$(python3 -I -c 'import sys, tomllib; print(tomllib.load(open(sys.argv[1], "rb"))["project"]["nix_hash"])' \
  "$root/tests/llvm/targets.toml")
[ "$(nix hash path "$src")" = "$want" ] || fail "llvm-project isn't the pinned $want"
want=$(python3 -I -c 'import json, sys; print(json.load(open(sys.argv[1]))["files"]["llvm/lib/Analysis/ValueTracking.cpp"])' \
  "$root/tests/cpp_correspondence/anchors.json")
[ "$(sha256sum "$src/llvm/lib/Analysis/ValueTracking.cpp" | cut -d' ' -f1)" = "$want" ] ||
  fail "ValueTracking.cpp isn't the one anchors.json pins"
echo "ok   pin: llvm-project and ValueTracking.cpp are the pinned ones"

mapfile -t flags < <(python3 -I -c '
import sys, tomllib
print("\n".join(tomllib.load(open(sys.argv[1], "rb"))["flags"]["llvm"]["args"]))' "$root/tests/llvm/targets.toml")
pc=()
# shellcheck disable=SC2086 # PROOF_CFLAGS is several flags.
for f in $PROOF_CFLAGS; do [ "$f" = -isystem ] && pc+=(-idirafter) || pc+=("$f"); done

# Compiles a ValueTracking.cpp to IR, takes isKnownNegation out, cuts it and translates it, into directory $2.
translate() {
  local source=$1 out=$2
  mkdir -p "$out/lean"
  clang "${pc[@]}" "${flags[@]}" -I"$src/llvm/include" -I"$src/llvm/lib/Analysis" -I"$root/tests/llvm/include" \
    -I"$(llvm-config --includedir)" -S -emit-llvm -fno-discard-value-names -o "$out/ValueTracking.ll" "$source"
  llvm-extract --func="$fn" -S -o "$out/extracted.ll" "$out/ValueTracking.ll"
  # The function has to come out unchanged, apart from attribute groups, which llvm-extract renumbers, and the order
  # of predecessors in the comments it prints.
  body() { awk -v f="@$fn(" 'index($0, "define ") == 1 && index($0, f) {on=1} on {print} on && /^}/ {exit}' "$1" |
    sed -E 's/#[0-9]+/#N/g; s/ *;.*$//'; }
  [ "$(body "$out/ValueTracking.ll")" = "$(body "$out/extracted.ll")" ] || fail "llvm-extract changed $fn"
  python3 -I "$here/cut.py" "$out/extracted.ll" "$out/cut.ll" "${cut[@]}" >"$out/cut.log"
  opt -passes=verify -disable-output "$out/cut.ll"
  "$irlean" "$out/cut.ll" --namespace KnownNegation -o "$out/lean/KnownNegation.lean"
}

translate "$src/llvm/lib/Analysis/ValueTracking.cpp" "$work"
echo "ok   translate: $fn compiled, extracted unchanged, $(wc -l <"$work/cut.log") callees cut, and translated whole"
echo "     as clang emitted it: $(awk '/^define /{on=1; b=1; next} on && /^}/{on=0}
  on && /^[A-Za-z_.0-9$]+:/{b++} on && /^  / && $1 !~ /^;/{n++} END{print n " instructions in " b " blocks"}' \
  "$work/extracted.ll"). KnownNegation.lean sha256 $(sha256sum "$work/lean/KnownNegation.lean" | cut -d' ' -f1)"

mapfile -t llvm_flags < <(llvm-config --cxxflags --ldflags --libs core | tr ' ' '\n' | grep -v '^$')
clang++ "$here/layout_probe.cpp" "${llvm_flags[@]}" -o "$work/layout_probe"
"$work/layout_probe" >"$work/layout_probe.log" || {
  cat "$work/layout_probe.log"
  fail "the layout probe disagrees with HeapView.lean"
}
echo "ok   layout: $(grep -c '^ok' "$work/layout_probe.log") facts hold on the pinned libLLVM"

export LEAN_PATH="$root/.lake/build/lib/lean:$work/lean"
lean_check() {
  (cd "$work/lean" && lean -j1 -M "$memory" -DwarningAsError=true -R . -o "$1.olean" "$1.lean")
}
cp "$root/tests/cpp_correspondence/SimplifyAddModel.lean" "$here/HeapView.lean" "$here/KnownNegationProof.lean" \
  "$work/lean/"
for m in SimplifyAddModel KnownNegation HeapView KnownNegationProof; do
  lean_check "$m" || fail "lean: $m"
done
IRLEAN_CHECK_MODULE=KnownNegationProof IRLEAN_CHECK_GENERATED=KnownNegation \
  IRLEAN_CHECK_THEOREMS="Binding.isKnownNegation_compiled KnownNegation.$fn
Binding.Example.returns_true KnownNegation.$fn" \
  lean -j1 -M "$memory" "$root/tests/check_axioms.lean" || fail "axioms"
(cd "$work/lean" && leanchecker KnownNegationProof HeapView) || fail "leanchecker"
echo "ok   lean: the proof checks with warnings as errors, on the standard axioms, and leanchecker replays it"

# Each bug changes what the C++ computes. The proof has to stop with an error of its own, not a resource limit.
mutant() {
  local name=$1 from=$2 to=$3 dir="$work/mutant-$1"
  rm -rf "$dir" && mkdir -p "$dir"
  python3 -I -c '
import sys
text = open(sys.argv[1]).read()
assert text.count(sys.argv[2]) == 1, "the mutation has to match exactly once"
open(sys.argv[4], "w").write(text.replace(sys.argv[2], sys.argv[3]))' \
    "$src/llvm/lib/Analysis/ValueTracking.cpp" "$from" "$to" "$dir/ValueTracking.cpp"
  translate "$dir/ValueTracking.cpp" "$dir"
  cmp -s "$dir/lean/KnownNegation.lean" "$work/lean/KnownNegation.lean" && fail "mutant $name: the IR didn't change"
  cp "$work/lean/"{SimplifyAddModel,HeapView}.{lean,olean} "$work/lean/KnownNegationProof.lean" "$dir/lean/"
  local log="$dir/proof.log"
  if (cd "$dir/lean" && LEAN_PATH="$root/.lake/build/lib/lean:$dir/lean" timeout 600 \
    lean -j1 -M "$memory" -R . -o KnownNegation.olean KnownNegation.lean &&
    LEAN_PATH="$root/.lake/build/lib/lean:$dir/lean" timeout 600 \
      lean -j1 -M "$memory" -R . KnownNegationProof.lean) >"$log" 2>&1; then
    fail "mutant $name: the proof still checks"
  fi
  grep -q -E 'error' "$log" || fail "mutant $name: stopped without an error of its own"
  grep -q -E 'maximum recursion|heartbeats|out of memory|memory limit' "$log" &&
    fail "mutant $name: stopped on a resource limit, so unknown"
  echo "ok   mutant $name: the proof fails, at $(grep -m1 -o 'KnownNegationProof.lean:[0-9]*' "$log")"
}
mutant swapped_operands 'match(Y, m_Sub(m_Specific(B), m_Specific(A)))' 'match(Y, m_Sub(m_Specific(A), m_Specific(B)))'
mutant negation_of_self 'if (!match(X, m_Neg(m_Specific(Y))))' 'if (!match(X, m_Neg(m_Specific(X))))'
