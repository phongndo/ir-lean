#!/usr/bin/env bash
# What the emitter refuses, what it accepts on purpose, and what it does with the input's name. Also that
# tests/opcheck.py can't quietly pass without Alive2.
# usage: tests/emitter.sh path/to/llvm-lean
set -uo pipefail
tool=$(realpath "$1")
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root" || exit 1
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work:$root/.lake/build/lib/lean"
failed=0

fail() {
  printf 'FAIL  %s\n' "$*"
  failed=1
}

# What the emitter says about @f in this IR.
report() {
  printf '%s\n' "$1" >"$work/input.ll"
  "$tool" "$work/input.ll" --report | grep -P '^\w+\tf\t'
}

# usage: refuses REASON IR
refuses() {
  local line
  line=$(report "$2")
  if [[ $line == unsupported* && $line == *"$1"* ]]; then
    printf 'ok    refused for %s\n' "$1"
  else
    fail "expected a refusal for \"$1\", got \"$line\", in: $2"
  fi
}

# usage: accepts IR
accepts() {
  local line
  line=$(report "$1")
  if [[ $line == ok* ]]; then
    printf 'ok    accepted %s\n' "$1"
  else
    fail "expected it to translate, got \"$line\", in: $1"
  fi
}

# Two rules no real program can show, since the rest imply them on every layout LLVM allows. The first only
# matters for an object that crosses the top of the address space, which LLVM rules out. The second says the
# offsets' running total can't wrap under `nuw`, which adding them to the address one by one already says.
cat >"$work/GepRules.lean" <<'LEAN'
import LLVMLean
open LLVMLean

example :
    Mem.gep ((Mem.empty fun _ => BitVec.ofNat 64 (2 ^ 64 - 4)).addGlobal 1 8 false #[]) (some ⟨1, 0#64⟩)
      (some 8#64) (inbounds := true) = none := rfl

example (a x y : BitVec 64) (hx : a.uaddOverflow x = false) (hy : (a + x).uaddOverflow y = false) :
    x.uaddOverflow y = false := by
  bv_decide
LEAN
if lean "$work/GepRules.lean"; then
  printf 'ok    the GEP rules no program can show hold as stated\n'
else
  fail 'the GEP rules no program can show'
fi

# `getelementptr` flags on a constant have to hold in every layout, since a constant has no check of its own.
gep_constant() {
  printf '@g = global [8 x i8] zeroinitializer\ndefine ptr @f() { ret ptr %s }\n' "$1"
}
refuses "don't plainly hold" "$(gep_constant 'getelementptr inbounds (i8, ptr @g, i64 9)')"
refuses "don't plainly hold" "$(gep_constant 'getelementptr nusw (i8, ptr @g, i64 9)')"
refuses "don't plainly hold" "$(gep_constant 'getelementptr nuw (i8, ptr @g, i64 9)')"
refuses "don't plainly hold" "$(gep_constant 'getelementptr inbounds (i8, ptr @g, i64 -1)')"
refuses "don't plainly hold" "$(gep_constant 'getelementptr inbounds (i8, ptr getelementptr (i8, ptr @g, i64 100), i64 -96)')"
refuses "don't plainly hold" "$(gep_constant 'getelementptr nuw (i8, ptr getelementptr inbounds (i8, ptr @g, i64 4), i64 -1)')"
refuses 'constant' "$(gep_constant 'getelementptr inbounds inrange(0, 4) (i8, ptr @g, i64 1)')"
refuses "don't plainly hold" '@g = global [8 x i8] zeroinitializer
@h = global ptr getelementptr inbounds (i8, ptr @g, i64 9)
define ptr @f() { %r = load ptr, ptr @h
  ret ptr %r }'
accepts "$(gep_constant 'getelementptr inbounds (i8, ptr @g, i64 8)')"
accepts "$(gep_constant 'getelementptr nuw (i8, ptr @g, i64 4)')"
accepts "$(gep_constant 'getelementptr (i8, ptr @g, i64 100)')"
accepts "$(gep_constant 'getelementptr inbounds (i8, ptr getelementptr (i8, ptr @g, i64 100), i64 0)')"

# `inbounds` with a non-zero index but a zero offset still needs its base in bounds, which `Mem.gep` can't see.
refuses 'instruction' 'define ptr @f(ptr %p) { %q = getelementptr inbounds [0 x i8], ptr %p, i64 1
  ret ptr %q }'
refuses 'instruction' 'define ptr @f(ptr %p, i64 %i) { %q = getelementptr inbounds [0 x i8], ptr %p, i64 %i
  ret ptr %q }'
refuses 'instruction' 'define ptr @f(ptr %p) { %q = getelementptr inbounds { [0 x i8], i8 }, ptr %p, i64 0, i32 1
  ret ptr %q }'
accepts 'define ptr @f(ptr %p, i64 %i) { %q = getelementptr [0 x i8], ptr %p, i64 %i
  ret ptr %q }'

# The default namespace comes from the input's name, which can be a word Lean reserves.
for name in example end theorem Mem 2fast; do
  printf 'define i32 @f(i32 %%x) { ret i32 %%x }\n' >"$work/$name.ll"
  if "$tool" "$work/$name.ll" -o "$work/Named.lean" && lean "$work/Named.lean" >"$work/lean.out" 2>&1; then
    printf 'ok    %s.ll gives a namespace Lean accepts\n' "$name"
  else
    fail "$name.ll gives a namespace Lean rejects: $(head -c 300 "$work/lean.out")"
  fi
done
"$tool" "$work/example.ll" --split "$work/split" || fail '--split with a default namespace'
if ! LEAN_PATH="$work/split:$LEAN_PATH" lean -R "$work/split" -o "$work/split/mexample/Globals.olean" \
  "$work/split/mexample/Globals.lean"; then
  fail 'example.ll, split, gives a namespace Lean rejects'
fi

# Without `alive-tv`, tests/opcheck.py has to fail, unless told not to care.
no_alive=$(tr : '\n' <<<"$PATH" | while read -r dir; do [ -x "$dir/alive-tv" ] || printf '%s:' "$dir"; done)
output=$(PATH=$no_alive tests/opcheck.py "$tool" 2>&1)
status=$?
if [ "$status" -ne 0 ] && [[ $output == *'alive-tv is not on PATH'* ]]; then
  printf 'ok    opcheck fails without alive-tv\n'
else
  fail "opcheck without alive-tv: exit $status, $output"
fi
output=$(PATH=$no_alive tests/opcheck.py "$tool" --no-alive 2>&1)
status=$?
if [ "$status" -eq 0 ] && [[ $output == *'skipped by --no-alive'* ]]; then
  printf 'ok    opcheck --no-alive says what it skipped\n'
else
  fail "opcheck --no-alive: exit $status, $output"
fi

exit $failed
