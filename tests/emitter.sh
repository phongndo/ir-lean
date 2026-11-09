#!/usr/bin/env bash
# What the emitter refuses, what it accepts on purpose, and what it does with the input's name. Also that
# tests/opcheck.py can't quietly pass without Alive2.
# usage: tests/emitter.sh path/to/ir-lean
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

# A `bitcast` between integers and vectors of integers puts lane 0 in the low bits only on a little-endian
# target, even in a function that doesn't touch memory. Lane widths that don't divide each other, floating-point
# lanes, pointers and scalable vectors are refused too. tests/x86check.py checks what the accepted ones mean
# against Alive2.
refuses 'big-endian integer bitcast' 'target datalayout = "E"
define <4 x i8> @f(<2 x i16> %x) { %r = bitcast <2 x i16> %x to <4 x i8>
  ret <4 x i8> %r }'
refuses 'nondividing lane widths' 'define <3 x i8> @f(<2 x i12> %x) { %r = bitcast <2 x i12> %x to <3 x i8>
  ret <3 x i8> %r }'
refuses 'type' 'define <2 x i32> @f(<2 x float> %x) { %r = bitcast <2 x float> %x to <2 x i32>
  ret <2 x i32> %r }'
refuses 'type' 'define <vscale x 4 x i8> @f(<vscale x 2 x i16> %x) { %r = bitcast <vscale x 2 x i16> %x to <vscale x 4 x i8>
  ret <vscale x 4 x i8> %r }'
refuses 'integer bitcast shape' 'define ptr @f(ptr %x) { %r = bitcast ptr %x to ptr
  ret ptr %r }'

# Native comparisons cannot observe poison. Check the generated code's lane boundaries directly,
# including the poison spread from joining and then splitting again.
cat >"$work/Bitcasts.ll" <<'IR'
target datalayout = "e"
define <4 x i8> @split(<2 x i16> %x) {
  %r = bitcast <2 x i16> %x to <4 x i8>
  ret <4 x i8> %r
}
define <2 x i16> @join(<4 x i8> %x) {
  %r = bitcast <4 x i8> %x to <2 x i16>
  ret <2 x i16> %r
}
define <8 x i1> @bits(i8 %x) {
  %r = bitcast i8 %x to <8 x i1>
  ret <8 x i1> %r
}
define i8 @scalar(<8 x i1> %x) {
  %r = bitcast <8 x i1> %x to i8
  ret i8 %r
}
IR
"$tool" "$work/Bitcasts.ll" -o "$work/Bitcasts.lean" --namespace Bitcasts --no-code
cat >"$work/BitcastsProof.lean" <<'LEAN'
import Bitcasts
open IRLean

example : Bitcasts.split #v[some 0x1234#16, none] =
    Outcome.ok #v[some 0x34#8, some 0x12#8, none, none] := by
  rw [Bitcasts.split, run]
  rfl

example : Bitcasts.join #v[some 0x34#8, some 0x12#8, none, some 0x56#8] =
    Outcome.ok #v[some 0x1234#16, none] := by
  rw [Bitcasts.join, run]
  rfl

example : Bitcasts.join #v[none, some 0x56#8, some 0x34#8, some 0x12#8] =
    Outcome.ok #v[none, some 0x1234#16] := by
  rw [Bitcasts.join, run]
  rfl

example : Vec.split 4 8 2 (Vec.join 2 16 2 #v[some 7#8, none, some 9#8, some 10#8]) =
    #v[none, none, some 9#8, some 10#8] := rfl

example : Bitcasts.bits (some 0x81#8) =
    Outcome.ok #v[some 1#1, some 0#1, some 0#1, some 0#1, some 0#1, some 0#1, some 0#1, some 1#1] := by
  rw [Bitcasts.bits, run]
  rfl

example : Bitcasts.bits none = Outcome.ok (Vector.replicate 8 none) := by
  rw [Bitcasts.bits, run]
  rfl

example : Bitcasts.scalar #v[some 1#1, some 0#1, some 0#1, some 0#1, some 0#1, some 0#1, some 0#1, some 1#1] =
    Outcome.ok (some 0x81#8) := by
  rw [Bitcasts.scalar, run]
  rfl

example : Bitcasts.scalar #v[some 1#1, some 0#1, some 0#1, some 0#1, none, some 0#1, some 0#1, some 1#1] =
    Outcome.ok none := by
  rw [Bitcasts.scalar, run]
  rfl
LEAN
if lean -R "$work" -o "$work/Bitcasts.olean" "$work/Bitcasts.lean" && lean "$work/BitcastsProof.lean"; then
  printf 'ok    integer bitcasts preserve lane order and propagate poison at lane boundaries\n'
else
  fail 'integer bitcast lane order or poison propagation'
fi
accepts 'target datalayout = "e"
define <4 x i8> @f(<2 x i16> %x) { %r = bitcast <2 x i16> %x to <4 x i8>
  ret <4 x i8> %r }'

# A function of N blocks that calls itself, which keeps it from nesting its blocks.
recursive_blocks() {
  local i phi="[ %r, %last ]"
  printf 'define i32 @f(i32 %%x) {\nentry:\n  br label %%b0\n'
  for ((i = 0; i < $1 - 4; i++)); do
    printf 'b%d:\n  %%c%d = icmp eq i32 %%x, %d\n  br i1 %%c%d, label %%done, label %%b%d\n' "$i" "$i" "$i" "$i" "$((i + 1))"
    phi+=", [ 1, %b$i ]"
  done
  printf 'b%d:\n  br label %%last\nlast:\n  %%r = call i32 @f(i32 0)\n  br label %%done\n' "$(($1 - 4))"
  printf 'done:\n  %%p = phi i32 %s\n  ret i32 %%p\n}\n' "$phi"
}

# Grouping blocks mustn't lower what a recursive function can have.
accepts "$(recursive_blocks 200)"
refuses 'recursive function with more than 200 blocks' "$(recursive_blocks 201)"

# A function of N blocks that doesn't call itself, so it nests them, which calls @$2 if that's given.
nested_blocks() {
  local i
  [ -n "${2:-}" ] && printf 'define i32 @%s() {\n  ret i32 1\n}\n' "$2"
  printf 'define i32 @f(i32 %%x) {\nentry:\n  br label %%b0\n'
  for ((i = 0; i < $1 - 2; i++)); do
    printf 'b%d:\n  %%c%d = icmp eq i32 %%x, %d\n  br i1 %%c%d, label %%done, label %%b%d\n' "$i" "$i" "$i" "$i" "$((i + 1))"
  done
  printf 'b%d:\n' "$(($1 - 2))"
  [ -n "${2:-}" ] && printf '  %%r = call i32 @%s()\n' "$2"
  printf '  br label %%done\ndone:\n  ret i32 0\n}\n'
}

# A callee can't share a name with the types that hold a function's nested blocks.
nested_blocks 33 G0 >"$work/Nested.ll"
if ! "$tool" "$work/Nested.ll" -o "$work/Nested.lean" --no-code || ! lean "$work/Nested.lean"; then
  fail 'a function with nested blocks calling @G0 should check'
fi

# However large a function is, its nested blocks have to fit in the types that hold them.
nested_blocks 3905 >"$work/Huge.ll"
"$tool" "$work/Huge.ll" -o "$work/Huge.lean" --no-code
groups=$(grep -c '^  | g[0-9]* (block : G[0-9]*)$' "$work/Huge.lean")
if [ "$groups" -gt 244 ]; then
  fail "a Lean type holds at most 244 constructors, and this has $groups"
fi

# Linkage: a definition can be proved about if it's certainly the one a run uses, or if it's this translation's copy
# of an `_odr` one. Only the first can be called, since a call runs whichever copy the linker keeps.
for linkage in weak linkonce available_externally; do
  refuses linkage "define $linkage i32 @f(i32 %x) { ret i32 %x }"
done
for linkage in weak_odr linkonce_odr; do
  accepts "define $linkage i32 @f(i32 %x) { ret i32 %x }"
  refuses 'call to @g, whose definition may not be the one that runs' "define $linkage i32 @g() { ret i32 0 }
define i32 @f() { %r = call i32 @g()
  ret i32 %r }"
done
refuses 'call to @g, whose definition may not be the one that runs' 'define weak i32 @g() { ret i32 0 }
define i32 @f() { %r = call i32 @g()
  ret i32 %r }'
refuses 'indirect call that can reach @g, whose definition may not be the one that runs' 'define linkonce_odr i32 @g() { ret i32 0 }
@h = global ptr @g
define i32 @f() { %t = load ptr, ptr @h
  %r = call i32 %t()
  ret i32 %r }'
refuses 'indirect call that can reach @g, whose definition may not be the one that runs' 'define linkonce_odr i32 @g() { ret i32 0 }
@a = alias i32 (), ptr @g
define i32 @f() { %r = call i32 @a()
  ret i32 %r }'
# Calling itself is calling whichever copy the linker keeps, too.
refuses 'call to @f, whose definition may not be the one that runs' 'define linkonce_odr i32 @f(i32 %x) {
entry:
  %c = icmp eq i32 %x, 0
  br i1 %c, label %done, label %again
again:
  %y = sub i32 %x, 1
  %r = call i32 @f(i32 %y)
  ret i32 %r
done:
  ret i32 0
}'
# What an `_odr` copy calls is another matter: an exact definition is the one that runs, whoever calls it.
accepts 'define i32 @g(i32 %x) { ret i32 %x }
define linkonce_odr i32 @f(i32 %x) { %r = call i32 @g(i32 %x)
  ret i32 %r }'
# Being `_odr` changes what can call a definition, and nothing about what it means.
odr_body='i32 @f(ptr %p, i32 %x) {
  %v = load i32, ptr %p, align 4
  %s = add nsw i32 %v, %x
  store i32 %s, ptr %p, align 4
  ret i32 %s
}'
printf 'define %s\n' "$odr_body" >"$work/Exact.ll"
printf 'define linkonce_odr %s\n' "$odr_body" >"$work/Odr.ll"
if "$tool" "$work/Exact.ll" --namespace Same -o "$work/Exact.lean" &&
  "$tool" "$work/Odr.ll" --namespace Same -o "$work/Odr.lean" &&
  diff <(tail -n +2 "$work/Exact.lean") <(tail -n +2 "$work/Odr.lean") >/dev/null; then
  printf 'ok    an _odr definition translates as the same definition with external linkage does\n'
else
  fail 'an _odr definition should translate as the same definition with external linkage does'
fi
for linkage in weak weak_odr linkonce linkonce_odr common; do
  refuses 'initial value' "@g = $linkage global i32 0
define ptr @f() { ret ptr @g }"
done
refuses 'initial value' '@g = externally_initialized global i32 0
define ptr @f() { ret ptr @g }'
refuses 'external @malloc' 'declare extern_weak ptr @malloc(i64)
define ptr @f() { %r = call ptr @malloc(i64 1)
  ret ptr %r }'
for linkage in '' internal private dso_local; do
  accepts "define $linkage i32 @f(i32 %x) { ret i32 %x }"
done

# Function attributes: anything that isn't on the reviewed list.
for attribute in noreturn naked returns_twice sanitize_address strictfp null_pointer_is_valid \
  convergent nocf_check speculatable nocallback '"made-up"="1"'; do
  # The verifier rejects a naked function that reads its arguments.
  refuses "attribute" "define i32 @f(i32 %x) $attribute { ret i32 0 }"
done
refuses 'call attribute nobuiltin' 'declare ptr @malloc(i64)
define ptr @f() {
  %p = call ptr @malloc(i64 8) nobuiltin
  ret ptr %p
}'
accepts 'define internal i32 @g(i32 %x) { ret i32 %x }
define i32 @f(i32 %x) {
  %y = call i32 @g(i32 %x) nobuiltin
  ret i32 %y
}'
accepts 'declare void @gives_up() noreturn
define i32 @f(i32 %x) {
  call void @gives_up() noreturn
  unreachable
}'
# A call outside the module with effects, in a function without memory, goes in the trace: docs/calls.md.
accepts 'declare void @returns()
define i32 @f(i32 %x) {
  call void @returns()
  ret i32 %x
}'
# Calls outside the module: docs/calls.md. One that accesses no memory answers from the world, in any function. One
# that passes or returns a pointer touches memory, and waits for F4. Promises the model doesn't check are refused.
accepts 'declare i8 @g(i8) memory(none)
define i8 @f(i8 %x) { %r = call i8 @g(i8 %x)
  ret i8 %r }'
accepts 'declare <2 x i8> @g(<2 x i8>, i32 noundef) memory(none) willreturn nounwind
define <2 x i8> @f(<2 x i8> %x) { %r = call <2 x i8> @g(<2 x i8> %x, i32 7)
  ret <2 x i8> %r }'
accepts 'declare void @g(i8)
define i8 @f(i8 %x) { call void @g(i8 %x) memory(none)
  ret i8 %x }'
accepts 'declare i32 @g(i32) memory(none)
define i32 @f(ptr %p) { %v = load i32, ptr %p
  %r = call i32 @g(i32 %v)
  ret i32 %r }'
accepts 'declare i8 @g(i8) memory(none)
define internal i8 @h(i8 %x) { %r = call i8 @g(i8 %x)
  ret i8 %r }
define i8 @f(i8 %x) { %r = call i8 @h(i8 %x)
  ret i8 %r }'
accepts 'declare i8 @g(i8) memory(read)
define i8 @f(i8 %x) { %r = call i8 @g(i8 %x)
  ret i8 %r }'
accepts 'declare i8 @g() memory(inaccessiblemem: readwrite)
define i8 @f(ptr %p) { %v = load i8, ptr %p
  %r = call i8 @g()
  %s = add i8 %v, %r
  ret i8 %s }'
refuses 'touches memory: F4' 'declare void @g(i8)
define void @f(ptr %p) { call void @g(i8 1)
  ret void }'
refuses 'touches memory: F4' 'declare i8 @g(i8) memory(read)
define i8 @f(ptr %p) { %r = call i8 @g(i8 1)
  ret i8 %r }'
# Under a promise to progress, a call with effects is progress, which the model can't count yet.
for attribute in mustprogress willreturn; do
  refuses 'with effects, under a promise to progress' "declare void @g(i8)
define void @f(i8 %x) $attribute { call void @g(i8 %x)
  ret void }"
done
refuses 'with effects, under a promise to progress' 'declare void @g(i8)
define void @f(i8 %x) {
entry:
  br label %loop
loop:
  call void @g(i8 %x)
  br label %loop, !llvm.loop !0
}
!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.mustprogress"}'
refuses 'which calls outside the module with effects, under a promise to progress' 'declare void @g(i8)
define internal void @h(i8 %x) { call void @g(i8 %x)
  ret void }
define void @f(i8 %x) mustprogress { call void @h(i8 %x)
  ret void }'
accepts 'declare i8 @g(i8) memory(read)
define i8 @f(i8 %x) mustprogress { %r = call i8 @g(i8 %x)
  ret i8 %r }'
# A recursive function's promise is its cycle's, and covers a call with effects in it the same way.
refuses 'with effects, under a promise to progress' 'declare void @e()
define void @f(i1 %c) {
entry:
  br i1 %c, label %rec, label %loop
rec:
  call void @f(i1 false)
  ret void
loop:
  call void @e()
  br label %loop, !llvm.loop !0
}
!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.mustprogress"}'
# A function with memory can't reach a call outside the module that may touch it through one without memory.
for memory in '' ' memory(read)'; do
  refuses 'whose calls outside the module may access' "declare i32 @e()$memory
define internal i32 @g() { %r = call i32 @e()
  ret i32 %r }
define i32 @f(ptr %p) { %a = load i32, ptr %p
  %c = call i32 @g()
  %b = load i32, ptr %p
  ret i32 %b }"
done
accepts 'declare i32 @e() memory(inaccessiblemem: readwrite)
define internal i32 @g() { %r = call i32 @e()
  ret i32 %r }
define i32 @f(ptr %p) { %a = load i32, ptr %p
  %c = call i32 @g()
  ret i32 %a }'
# `nosync` at a call promises the callee's calls outside the module don't synchronize.
refuses 'call attribute nosync on a call to @g' 'declare void @e(i8)
define internal void @g(i8 %x) { call void @e(i8 %x)
  ret void }
define void @f(i8 %x) { call void @g(i8 %x) nosync
  ret void }'
# A callee that accesses memory may synchronize, free, or access what its caller promised not to.
refuses 'nosync on a function whose calls outside the module access memory' 'declare i8 @g(i8) memory(read)
define i8 @f(i8 %x) nosync { %r = call i8 @g(i8 %x)
  ret i8 %r }'
refuses 'nofree on a function whose calls outside the module have effects' 'declare void @g(i8)
define void @f(i8 %x) nofree { call void @g(i8 %x)
  ret void }'
refuses 'memory on a function whose calls outside the module access memory' 'declare void @g(i8)
define void @f(i8 %x) memory(none) { call void @g(i8 %x)
  ret void }'
accepts 'declare i8 @g(i8) memory(none)
define i8 @f(i8 %x) nosync nofree memory(none) { %r = call i8 @g(i8 %x)
  ret i8 %r }'
refuses 'touches memory: F4' 'declare i8 @g(ptr) memory(none)
define i8 @f(ptr %p) { %r = call i8 @g(ptr %p)
  ret i8 %r }'
refuses 'touches memory: F4' 'declare ptr @g(i8) memory(none)
define ptr @f(i8 %x) { %r = call ptr @g(i8 %x)
  ret ptr %r }'
for attribute in speculatable nosync nofree norecurse nocallback convergent returns_twice; do
  refuses "attribute $attribute of external @g" "declare i8 @g(i8) memory(none) $attribute
define i8 @f(i8 %x) { %r = call i8 @g(i8 %x)
  ret i8 %r }"
done
# A callee outside the module may call back into its caller, which `norecurse` rules out.
refuses 'norecurse on a function that calls outside the module' 'declare i8 @g(i8) memory(none)
define i8 @f(i8 %x) norecurse { %r = call i8 @g(i8 %x)
  ret i8 %r }'
# Mem.withFrame and Mem.call don't pass a run that didn't come back through yet.
refuses 'stack frame or promises about memory' 'declare i8 @g(i8) memory(none)
define i8 @f(i8 %x) { %p = alloca i8
  store i8 %x, ptr %p
  %v = load i8, ptr %p
  %r = call i8 @g(i8 %v)
  ret i8 %r }'
refuses 'stack frame or promises about memory' 'declare i8 @g(i8) memory(none)
define i8 @f(ptr %p) memory(read) { %v = load i8, ptr %p
  %r = call i8 @g(i8 %v)
  ret i8 %r }'
refuses 'call to external @g, which may be null' 'declare extern_weak void @g(i8)
define void @f(i8 %x) { call void @g(i8 %x)
  ret void }'
refuses 'calling convention' 'declare fastcc i8 @g(i8) memory(none)
define i8 @f(i8 %x) { %r = call i8 @g(i8 %x)
  ret i8 %r }'
refuses 'which calls outside the module' 'declare i8 @g(i8) memory(none)
define i8 @h(i8 %x) { %r = call i8 @g(i8 %x)
  ret i8 %r }
@p = global ptr @h
define i8 @f(i8 %x) { %t = load ptr, ptr @p
  %r = call i8 %t(i8 %x)
  ret i8 %r }'
# Values and functions named like what emitted code uses for calls outside the module get other names.
cat >"$work/Names.ll" <<'IR'
declare i8 @g(i8) memory(none)
define i8 @Talks(i8 %x) {
  %r = call i8 @g(i8 %x)
  ret i8 %r
}
define i8 @f(i8 %Talks, i8 %World, i8 %Trace, i8 %Exit, i8 %Lanes) {
  %r = call i8 @g(i8 %Talks)
  ret i8 %r
}
define i8 @h(i8 %x) {
  %r = call i8 @Talks(i8 %x)
  ret i8 %r
}
IR
if out=$("$tool" "$work/Names.ll" -o "$work/Names.lean" --namespace Names --no-code 2>&1) &&
  out=$(lean -R "$work" -o "$work/Names.olean" "$work/Names.lean" 2>&1); then
  printf 'ok    names that calls outside the module use are kept for them\n'
else
  fail "names that calls outside the module use should be kept for them: $out"
fi
# Under a promise to progress, one that promises to progress, and not to return, and never comes back stops the model.
printf '%s\n' 'declare i8 @g(i8) memory(none) mustprogress
define i8 @f(i8 %x) mustprogress { %r = call i8 @g(i8 %x)
  ret i8 %r }' >"$work/input.ll"
if "$tool" "$work/input.ll" | grep -q 'fun _ => Outcome.stop .progressUnsettled'; then
  printf 'ok    a call outside the module that may never come back under a promise stops the model\n'
else
  fail 'a call outside the module that may never come back under a promise should stop the model'
fi
refuses 'call attribute noreturn' 'declare void @llvm.donothing()
define void @f() { call void @llvm.donothing() noreturn
  ret void }'
refuses 'garbage collector' 'define i32 @f(i32 %x) gc "statepoint-example" { ret i32 %x }'
refuses 'prefix data' 'define i32 @f(i32 %x) prefix i32 1 { ret i32 %x }'
for attribute in mustprogress willreturn 'memory(none)' nofree nosync norecurse nounwind uwtable sspstrong \
  noinline '"target-cpu"="x86-64"'; do
  accepts "define i32 @f(i32 %x) $attribute { ret i32 %x }"
done

# Promises the model has no rule for, or that are only checked on a function's own parameters.
for attribute in noalias 'dereferenceable_or_null(4)'; do
  refuses "parameter attribute" "define ptr @f(ptr $attribute %p) { ret ptr %p }"
done
refuses 'parameter attribute' 'define { i32, i32 } @f({ i32, i32 } returned %x) { ret { i32, i32 } %x }'
refuses 'call parameter attribute' 'define void @g(ptr %p) { ret void }
define void @f(ptr %p) { call void @g(ptr readonly %p)
  ret void }'
refuses 'call attribute memory' 'define void @g() { ret void }
define void @f() { call void @g() memory(none)
  ret void }'
refuses 'call return attribute' 'define ptr @g() { ret ptr null }
define ptr @f() { %r = call noalias ptr @g()
  ret ptr %r }'
refuses 'parameter attribute' 'define ptr @f(ptr captures(ret: address, provenance) %p) { ret ptr %p }'
refuses 'norecurse' 'define i32 @f(i32 %x) norecurse { %r = call i32 @f(i32 %x)
  ret i32 %r }'
refuses 'nofree' 'declare void @free(ptr)
define void @f(ptr %p) nofree { call void @free(ptr %p)
  ret void }'
refuses 'nofree' 'declare void @free(ptr)
define void @g(ptr %p) { call void @free(ptr %p)
  ret void }
define void @f(ptr %p) nofree { call void @g(ptr %p)
  ret void }'
refuses 'nofree' 'declare void @free(ptr)
define void @g(ptr %p) { call void @free(ptr %p)
  ret void }
@h = global ptr @g
define void @f(ptr %p) nofree { %t = load ptr, ptr @h
  call void %t(ptr %p)
  ret void }'
# A promise at a call isn't checked, so it can't be taken on trust either.
for attribute in nofree norecurse willreturn mustprogress; do
  refuses 'call attribute' "define void @g() { ret void }
define void @f() { call void @g() $attribute
  ret void }"
done
refuses 'call attribute nofree' 'declare void @free(ptr)
define void @f(ptr %p) { call void @free(ptr %p) nofree
  ret void }'
# Declaring the C library with promises it doesn't keep means it isn't that library.
refuses 'external @free' 'declare void @free(ptr nofree)
define void @f(ptr %p) { call void @free(ptr %p)
  ret void }'
refuses 'external @free' 'declare void @free(ptr) memory(none)
define void @f(ptr %p) { call void @free(ptr %p)
  ret void }'
refuses 'external @free' 'declare void @free(ptr) nofree
define void @f(ptr %p) { call void @free(ptr %p)
  ret void }'
refuses 'external @strlen' 'declare i64 @strlen(ptr readnone)
define i64 @f(ptr %p) { %n = call i64 @strlen(ptr %p)
  ret i64 %n }'
refuses 'external @strlen' 'declare i64 @strlen(ptr) memory(none)
define i64 @f(ptr %p) { %n = call i64 @strlen(ptr %p)
  ret i64 %n }'
refuses 'external @malloc' 'declare nonnull ptr @malloc(i64)
define ptr @f() { %r = call ptr @malloc(i64 1)
  ret ptr %r }'
refuses 'external @malloc' 'declare ptr @malloc(i64) memory(none)
define ptr @f() { %r = call ptr @malloc(i64 1)
  ret ptr %r }'
refuses 'external @malloc' 'declare ptr @malloc(i64) memory(inaccessiblemem: readwrite, errnomem: read)
define ptr @f() { %r = call ptr @malloc(i64 1)
  ret ptr %r }'
accepts 'declare noalias noundef ptr @malloc(i64 noundef) mustprogress nofree nounwind willreturn allockind("alloc,uninitialized") allocsize(0) memory(inaccessiblemem: readwrite, errnomem: write)
define ptr @f() { %r = call noalias ptr @malloc(i64 1)
  ret ptr %r }'
accepts 'declare void @free(ptr allocptr noundef captures(none)) mustprogress nounwind willreturn allockind("free") memory(argmem: readwrite, inaccessiblemem: readwrite)
define void @f(ptr %p) { call void @free(ptr %p)
  ret void }'
accepts 'declare i64 @strlen(ptr noundef captures(none)) nocallback nofree nounwind willreturn memory(argmem: read)
define i64 @f(ptr %p) { %n = call i64 @strlen(ptr %p) nounwind willreturn memory(read)
  ret i64 %n }'
# Two `initializes` arguments could overlap, and each needs its own record of what it wrote.
refuses 'initializes' 'define void @f(ptr initializes((0, 4)) %p, ptr initializes((0, 4)) %q) { ret void }'
# `tbaa` isn't modeled yet, and the others aren't used. -fno-strict-aliasing leaves `tbaa` out.
refuses 'metadata !tbaa' 'define i32 @f(ptr %p) { %v = load i32, ptr %p, !tbaa !0
  ret i32 %v }
!0 = !{!1, !1, i64 0}
!1 = !{!"int", !2, i64 0}
!2 = !{!"root"}'
refuses 'metadata !alias.scope' 'define i32 @f(ptr %p) { %v = load i32, ptr %p, !alias.scope !0
  ret i32 %v }
!0 = !{!1}
!1 = distinct !{!1, !2}
!2 = distinct !{!2}'
refuses 'instruction' 'declare void @llvm.assume(i1)
define void @f(ptr %p) { call void @llvm.assume(i1 true) [ "align"(ptr %p, i64 8) ]
  ret void }'

# `allocsize` and `allockind` make a function `malloc` or `free` to the optimizer. The model only knows the C library's.
refuses 'function attribute allocsize' 'define ptr @f(i64 %n) allocsize(0) { ret ptr null }'
refuses 'function attribute allockind' 'define ptr @f(i64 %n) allockind("alloc") { ret ptr null }'
refuses 'call attribute allocsize' 'define ptr @g(i64 %n) { ret ptr null }
define ptr @f() { %p = call ptr @g(i64 4) allocsize(0)
  ret ptr %p }'
accepts 'declare noalias noundef ptr @malloc(i64 noundef) nounwind allockind("alloc,uninitialized") allocsize(0) memory(inaccessiblemem: readwrite, errnomem: write)
define ptr @f() { %r = call noalias ptr @malloc(i64 1) allocsize(0)
  ret ptr %r }'
# An allocation whose size in bytes doesn't fit in 64 bits would wrap to a small one.
refuses 'alloca of more bytes than 64 bits can count' 'define i32 @f() { %a = alloca i32, i64 4611686018427387905
  store i32 1, ptr %a
  ret i32 0 }'
refuses 'alloca of more bytes than 64 bits can count' 'define i32 @f() { %a = alloca i8, i128 18446744073709551617
  store i8 1, ptr %a
  ret i32 0 }'
refuses 'alloca with a count wider than 64 bits' 'define i32 @f(i128 %n) { %a = alloca i8, i128 %n
  store i8 1, ptr %a
  ret i32 0 }'
# Another module can replace a definition when it's loaded, unless it's local to this one.
refuses linkage 'define i32 @f(i32 %x) { ret i32 %x }
!llvm.module.flags = !{!0}
!0 = !{i32 1, !"SemanticInterposition", i32 1}'
accepts 'define dso_local i32 @f(i32 %x) { ret i32 %x }
!llvm.module.flags = !{!0}
!0 = !{i32 1, !"SemanticInterposition", i32 1}'

# What LLVM's verifier rejects isn't translated, since the model would give it a meaning LLVM doesn't.
printf '%s\n' '@g = constant i32 0
declare void @llvm.lifetime.start.p0(ptr)
define void @f() { call void @llvm.lifetime.start.p0(ptr @g)
  store i32 1, ptr @g
  ret void }' >"$work/Invalid.ll"
output=$("$tool" "$work/Invalid.ll" --report 2>&1)
status=$?
if [ "$status" -eq 1 ] && [[ $output == *"doesn't pass LLVM's verifier"* ]]; then
  printf 'ok    IR that fails the verifier is refused\n'
else
  fail "IR that fails the verifier: exit $status, $output"
fi

# Emitted code binds names of its own, which no value's name can be. A `switch` once bound its selector as `sel`,
# so here a parameter named `%sel` read in a case was replaced by the selector: pick 5 2 gave 6.
cat >"$work/Pick.ll" <<'IR'
define i32 @pick(i32 noundef %sel, i32 noundef %op) {
entry:
  switch i32 %op, label %return [
    i32 0, label %zero
    i32 2, label %two
  ]
zero:
  %add = add i32 %sel, 1
  br label %return
two:
  %mul = mul i32 %sel, 3
  br label %return
return:
  %r = phi i32 [ %add, %zero ], [ %mul, %two ], [ %sel, %entry ]
  ret i32 %r
}
IR
cat >"$work/PickProof.lean" <<'LEAN'
import Pick
open IRLean Pick

theorem pick_two (s : BitVec 32) : pick (some s) (some 2#32) = Outcome.ok (some (s * 3#32)) := by
  simp only [pick, noundef]
  rw [run_jump _ (by rfl), run_jump _ (by rfl), run_ret _ (by rfl)]
  simp [Val.mul]
LEAN
if "$tool" "$work/Pick.ll" -o "$work/Pick.lean" --namespace Pick --no-code && lean -R "$work" -o "$work/Pick.olean" "$work/Pick.lean" &&
  lean "$work/PickProof.lean"; then
  printf 'ok    a value named like a binder the emitter uses keeps its own value\n'
else
  fail 'a value named %sel read inside a switch'
fi

# Checks that are only seen by running: a `dereferenceable` result where the call returns, the arguments of a call
# that never returns before it stops, and an `alloca` whose size in bytes doesn't fit.
cat >"$work/Runs.ll" <<'IR'
define dereferenceable(8) ptr @past() {
  %a = alloca i32
  %p = getelementptr i8, ptr %a, i64 100
  ret ptr %p
}
define i32 @deref() {
  %p = call dereferenceable(8) ptr @past()
  ret i32 0
}
declare void @gives_up(i32 noundef) noreturn
define void @poison_to_abort() {
  call void @gives_up(i32 poison) noreturn
  unreachable
}
define void @abort() {
  call void @gives_up(i32 1) noreturn
  unreachable
}
declare void @dies(i32 noundef range(i32 0, 10)) noreturn
define void @narrower() {
  call void @dies(i32 range(i32 0, 100) 50) noreturn
  unreachable
}
define i32 @array(i64 %n) {
  %a = alloca i32, i64 %n
  store i32 1, ptr %a
  ret i32 0
}
IR
cat >"$work/RunsCheck.lean" <<'LEAN'
import Runs
open IRLean Runs

def show' : Outcome α → String
  | none => "none"
  | some (.error (.undefined e)) => s!"ub {repr e}"
  | some (.error (.model e)) => s!"stop {repr e}"
  | some (.ok _) => "ok"

#guard show' (deref initial) == "ub IRLean.UB.badAccess"
#guard show' poison_to_abort == "ub IRLean.UB.noundefPoison"
#guard show' abort == "stop IRLean.ModelStop.noReturnCall"
#guard show' narrower == "ub IRLean.UB.noundefPoison"
#guard show' (array (some 4611686018427387905#64) initial) == "ub IRLean.UB.poisonPointer"
#guard show' (array (some 4#64) initial) == "ok"
LEAN
if "$tool" "$work/Runs.ll" -o "$work/Runs.lean" --namespace Runs && lean -R "$work" -o "$work/Runs.olean" "$work/Runs.lean" &&
  lean "$work/RunsCheck.lean"; then
  printf 'ok    dereferenceable results, the arguments of calls that never return, and huge allocas are checked\n'
else
  fail 'dereferenceable results, the arguments of calls that never return, or huge allocas'
fi

# Choices: `freeze` of poison is a value the run's `IRLean.Choice` names, and each `freeze` a run executes reads its own
# place in it, in a loop, in a function called twice, through a pointer, at each depth of a recursion, and of memory
# never written. Running the emitted code under chosen choices shows each place is its own, so a change to how the
# emitter numbers them shows. Only integers are frozen: LangRef freezes a vector's lanes one by one, and a pointer to
# one with no provenance, and neither is modeled.
refuses 'instruction %r = freeze ptr %p' 'define ptr @f(ptr %p) { %r = freeze ptr %p
  ret ptr %r }'
refuses 'instruction %r = freeze <2 x i8> %v' 'define <2 x i8> @f(<2 x i8> %v) { %r = freeze <2 x i8> %v
  ret <2 x i8> %r }'
cat >"$work/Choices.ll" <<'IR'
; Two runs of one `freeze` in a loop choose apart: the result is how the first differs from the second.
define i8 @loop(i8 %x) {
entry:
  br label %body
body:
  %i = phi i8 [ 0, %entry ], [ 1, %body ]
  %prev = phi i8 [ 0, %entry ], [ %f, %body ]
  %f = freeze i8 poison
  %done = icmp eq i8 %i, 1
  br i1 %done, label %exit, label %body
exit:
  %d = sub i8 %prev, %f
  ret i8 %d
}

; A function called twice chooses apart each time.
define i8 @pick() {
  %f = freeze i8 poison
  ret i8 %f
}
define i8 @twice() {
  %a = call i8 @pick()
  %b = call i8 @pick()
  %d = sub i8 %a, %b
  ret i8 %d
}

; Through a pointer.
@target = global ptr @pick
define i8 @indirect() {
  %p = load ptr, ptr @target
  %a = call i8 %p()
  ret i8 %a
}

; A recursive function chooses at each depth.
define i8 @down(i8 %n) {
entry:
  %f = freeze i8 poison
  %z = icmp eq i8 %n, 0
  br i1 %z, label %done, label %more
more:
  %m = sub i8 %n, 1
  %r = call i8 @down(i8 %m)
  %s = add i8 %r, %f
  ret i8 %s
done:
  ret i8 %f
}

; Memory: a byte never written is poison, and `freeze` chooses a value for it.
define i8 @uninit() {
  %a = alloca i8
  %v = load i8, ptr %a
  %f = freeze i8 %v
  ret i8 %f
}

; A function that makes no choices is left as it was.
define i8 @plain(i8 %x) {
  ret i8 %x
}
IR
cat >"$work/ChoicesCheck.lean" <<'LEAN'
import Choices
open IRLean Choices

def show' : Outcome (Val 8) → String
  | some (.ok (some x)) => s!"{x.toNat}"
  | some (.ok none) => "poison"
  | none => "none"
  | some (.error (.undefined e)) => s!"ub {repr e}"
  | some (.error (.model e)) => s!"stop {repr e}"

def showMem (o : Outcome (Val 8 × Mem)) : String := show' (andThen o fun r => Outcome.ok r.1)

/-- `n` at every place. -/
def same (n : Nat) : Choice := fun _ => n
/-- `n` at the place `p`, and 0 everywhere else. -/
def only (p : List Nat) (n : Nat) : Choice := fun q => if q = p then n else 0

-- The loop's body runs twice, as blocks `c.sub 0` and `(c.sub 0).sub 0`: its `freeze` reads `[0, 1]` the first time
-- and `[0, 0, 1]` the second, so the two can differ.
#guard show' (loop_1 none (same 7)) == "0"
#guard show' (loop_1 none (only [0, 1] 3)) == "3"
#guard show' (loop_1 none (only [0, 0, 1] 3)) == "253"
-- Each call of `pick` gets its own place, `[1]` and `[2]`, under which its `freeze` reads `[1]`.
#guard show' (twice (same 7)) == "0"
#guard show' (twice (only [1, 1] 5)) == "5"
#guard show' (twice (only [2, 1] 5)) == "251"
-- Through a pointer too.
#guard showMem (indirect_1 initial (only [1, 1] 9)) == "9"
-- Each depth of a recursion chooses for itself: depth 0 reads `[1]`, and depth 1, called from the next block, `[0, 1, 1]`.
#guard show' (down (some 1#8) (only [0, 1, 1] 4)) == "4"
#guard show' (down (some 1#8) (only [1] 4)) == "4"
#guard show' (down (some 1#8) (same 2)) == "4"
-- A byte never written is poison, and `freeze` makes it the value chosen.
#guard showMem (uninit initial (only [1] 200)) == "200"
-- A function that makes no choices keeps its type.
example : plain = fun x => run plain.step (.bb1 x) := rfl
LEAN
if "$tool" "$work/Choices.ll" -o "$work/Choices.lean" --namespace Choices &&
  lean -R "$work" -o "$work/Choices.olean" "$work/Choices.lean" && lean "$work/ChoicesCheck.lean"; then
  printf 'ok    each freeze a run executes chooses for itself, in loops, calls, recursion and memory\n'
else
  fail 'what a freeze chooses, by where it runs'
fi

# Promises to progress and to return, as the model checks them (IRLean/Promise.lean): a run that never finishes under
# one is undefined, unless it's waiting on a call LangRef allows never to return, and where LangRef doesn't settle it
# the model stops. Each is proved here of what ir-lean emits, so a change to the emitter or the model shows.
cat >"$work/Promises.ll" <<'IR'
; A function marked mustprogress that spins.
define i32 @spin(i32 %x) mustprogress {
entry:
  br label %again
again:
  br label %again
}

; The same without the promise.
define i32 @spin_free(i32 %x) {
entry:
  br label %again
again:
  br label %again
}

; A loop marked llvm.loop.mustprogress that steps by 2 from 0 until it reaches %n: it never does when %n is odd.
define i32 @evens(i32 noundef %n) {
entry:
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %next, %loop ]
  %next = add i32 %i, 2
  %done = icmp eq i32 %i, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !0
exit:
  ret i32 %i
}

; Waiting on a call that never returns, under a promise, to a callee without one: LangRef allows it.
define i32 @calls_free(i32 %x) mustprogress {
  %r = call i32 @spin_free(i32 %x)
  ret i32 %r
}

; The callee promises to progress, and doesn't return because it waits on @spin_free: LangRef doesn't settle it.
define i32 @calls_excused(i32 %x) mustprogress {
  %r = call i32 @calls_free(i32 %x)
  ret i32 %r
}

; The same call from a function without a promise: it just waits.
define i32 @waits(i32 %x) {
  %r = call i32 @calls_free(i32 %x)
  ret i32 %r
}

; willreturn allows nothing that doesn't return.
define i32 @returns(i32 %x) willreturn {
  %r = call i32 @spin_free(i32 %x)
  ret i32 %r
}

; A cycle of calls under a promise.
define i32 @recurse(i32 %x) mustprogress {
  %r = call i32 @recurse(i32 %x)
  ret i32 %r
}

define i32 @recurse_wr(i32 %x) willreturn {
  %r = call i32 @recurse_wr(i32 %x)
  ret i32 %r
}

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.mustprogress"}
IR
cat >"$work/PromisesProof.lean" <<'LEAN'
import Meta
import Promises
open IRLean Promises Lean.Order

/-- A function marked `mustprogress` that spins breaks its promise. -/
theorem spin_ub (x : Val 32) : spin x = Outcome.ub .noProgress := by
  have loop : run spin.step .again = none :=
    run_forever (fun b => b = .again) (fun b hb => ⟨.again, by subst hb; rfl, rfl⟩) rfl
  have broken : runPromised (fun _ => true) spin.step .entry = Outcome.ub .noProgress :=
    runPromised_forever (fun _ => True) (fun b _ => by cases b <;> exact ⟨.again, rfl, rfl, trivial⟩) trivial
  rw [spin, run_jump _ (show spin.step .entry = jump .again from rfl), loop]
  exact broken

/-- Without the promise, it just never finishes. -/
theorem spin_free_none (x : Val 32) : spin_free x = none := by
  rw [spin_free, run_jump _ (show spin_free.step .entry = jump .again from rfl)]
  exact run_forever (fun b => b = .again) (fun b hb => ⟨.again, by subst hb; rfl, rfl⟩) rfl

/-- The loop's states for an odd `n`: `i` is always even, so it never reaches `n`. -/
theorem evens_odd (n : BitVec 32) (hn : n.toNat % 2 = 1) : evens (some n) = Outcome.ub .noProgress := by
  let I : evens.Block → Prop := fun b => ∃ i : BitVec 32, i.toNat % 2 = 0 ∧ b = .loop_1 (some i) (some n)
  have hI : ∀ b, I b → ∃ b', evens.step b = jump b' ∧ evens.promise b' = true ∧ I b' := by
    rintro b ⟨i, hi, rfl⟩
    have hne : i ≠ n := by rintro rfl; omega
    refine ⟨.loop_1 (some (i + 2#32)) (some n), ?_, rfl, i + 2#32, ?_, rfl⟩
    · simp [evens.step, llvm_val, hne]
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h0 : I (.loop_1 (some 0#32) (some n)) := ⟨0#32, rfl, rfl⟩
  have hrun : run evens.step (.entry (some n)) = none := by
    rw [run_jump _ (show evens.step (.entry (some n)) = jump (.loop_1 (some 0#32) (some n)) from rfl)]
    exact run_forever I (fun b hb => let ⟨b', h, _, h'⟩ := hI b hb; ⟨b', h, h'⟩) h0
  simp only [evens, noundef_some, hrun, promised_none]
  rw [runPromised_jump (show evens.step (.entry (some n)) = jump (.loop_1 (some 0#32) (some n)) from rfl)]
  exact runPromised_forever I hI h0

/-- For an even `n` it returns `n`: the promise holds there. -/
theorem evens_even (n : BitVec 32) (hn : n.toNat % 2 = 0) : evens (some n) = Outcome.ok (some n) := by
  have loop : ∀ k (i : BitVec 32), i.toNat % 2 = 0 → i.toNat ≤ n.toNat → n.toNat - i.toNat = 2 * k →
      run evens.step (.loop_1 (some i) (some n)) = Outcome.ok (some n) := by
    intro k
    induction k with
    | zero =>
      intro i _ hle hk
      have : i = n := BitVec.eq_of_toNat_eq (by omega)
      subst this
      rw [run_jump _ (show evens.step _ = jump (.exit (some i)) by simp [evens.step, llvm_val, br])]
      exact run_ret _ rfl
    | succ k ih =>
      intro i hi hle hk
      have hne : i ≠ n := by rintro rfl; omega
      rw [run_jump _ (show evens.step _ = jump (.loop_1 (some (i + 2#32)) (some n)) by
        simp [evens.step, llvm_val, hne])]
      have hlt : (i + 2#32).toNat = i.toNat + 2 := by
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := n.isLt; omega
      exact ih _ (by omega) (by omega) (by omega)
  simp only [evens, noundef_some]
  rw [run_jump _ (show evens.step (.entry (some n)) = jump (.loop_1 (some 0#32) (some n)) from rfl),
    loop (n.toNat / 2) 0#32 rfl (by simp) (by simp; omega)]
  rfl

/-- Waiting, under a promise, on a callee without one that never returns: LangRef allows it. -/
theorem calls_free_none (x : Val 32) : calls_free x = none := by
  have stuck : calls_free.step (.bb1 x) = none := by simp [calls_free.step, spin_free_none, andThen]
  rw [calls_free, show run calls_free.step (.bb1 x) = none by rw [run, stuck], promised_none]
  exact runPromised_stuck stuck

/-- Under a promise, waiting on a callee that also promised, and waits itself: LangRef doesn't settle it. -/
theorem calls_excused_stop (x : Val 32) : calls_excused x = Outcome.stop .progressUnsettled := by
  have h : calls_excused.step (.bb1 x) = Outcome.stop .progressUnsettled := by
    simp [calls_excused.step, calls_free_none, promised_none, andThen, Outcome.stop]
  rw [calls_excused, run, h]; rfl

/-- Without a promise of its own, it just waits. -/
theorem waits_none (x : Val 32) : waits x = none := by
  rw [waits, run]; simp [waits.step, calls_free_none, andThen]

/-- `willreturn` allows no run that doesn't return, whatever the reason. -/
theorem returns_ub (x : Val 32) : returns x = Outcome.ub .noReturn := by
  rw [returns, show run returns.step (.bb1 x) = none by rw [run]; simp [returns.step, spin_free_none, andThen]]
  rfl

/-- Calling itself forever: the raw function never finishes. -/
theorem recurse_raw_none (x : Val 32) : recurse.raw x = none := by
  have := recurse.raw.fixpoint_induct (fun f => ∀ b, f b = none) (fun f => ∀ x, f x = none)
    (admissible_pi_apply (fun _ (r : Outcome (Val 32)) => r = none) fun _ => admissible_flatOrder _ rfl)
    (admissible_pi_apply (fun _ (r : Outcome (Val 32)) => r = none) fun _ => admissible_flatOrder _ rfl)
    (fun raw h b => by cases b; simp [h, andThen])
    (fun loop h x => h _)
  exact this x

theorem recurse_stop (x : Val 32) : recurse x = Outcome.stop .recursionUnsettled := by
  rw [recurse, recurse_raw_none]; rfl

theorem recurse_wr_ub (x : Val 32) : recurse_wr x = Outcome.ub .noReturn := by
  have := recurse_wr.raw.fixpoint_induct (fun f => ∀ b, f b = none) (fun f => ∀ x, f x = none)
    (admissible_pi_apply (fun _ (r : Outcome (Val 32)) => r = none) fun _ => admissible_flatOrder _ rfl)
    (admissible_pi_apply (fun _ (r : Outcome (Val 32)) => r = none) fun _ => admissible_flatOrder _ rfl)
    (fun raw h b => by cases b; simp [h, andThen])
    (fun loop h x => h _)
  rw [recurse_wr, this x]; rfl

-- Loop metadata off a latch, which a pass copied there, describes no loop: only the loop's own blocks are promised.
example : Meta.stale.promise (.loop_1 none none) = true := rfl
example : Meta.stale.promise (.split none) = false := rfl
LEAN
cat >"$work/Meta.ll" <<'IR'
define i32 @stale(i32 %n) {
entry:
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %next, %loop ]
  %next = add i32 %i, 1
  %done = icmp eq i32 %next, %n
  br i1 %done, label %split, label %loop, !llvm.loop !0
split:
  br label %exit, !llvm.loop !0
exit:
  ret i32 %i
}
!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.mustprogress"}
IR
if "$tool" "$work/Promises.ll" -o "$work/Promises.lean" --namespace Promises --no-code &&
  "$tool" "$work/Meta.ll" -o "$work/Meta.lean" --namespace Meta --no-code &&
  lean -R "$work" -o "$work/Promises.olean" "$work/Promises.lean" && lean -R "$work" -o "$work/Meta.olean" "$work/Meta.lean" &&
  lean "$work/PromisesProof.lean"; then
  printf 'ok    a run that never finishes is undefined under a promise, and waiting on a call LangRef allows is not\n'
else
  fail 'what the model says of a run that never finishes under a promise'
fi
# `llvm.sideeffect` is observable progress, which the model has none of, so a loop calling it would be undefined under a
# promise where LLVM defines it. It's refused, and so is anything calling a function that uses it.
refuses 'llvm.sideeffect' 'declare void @llvm.sideeffect()
define void @f() mustprogress {
entry:
  br label %again
again:
  call void @llvm.sideeffect()
  br label %again
}'
refuses "call to @g, which isn't translated" 'declare void @llvm.sideeffect()
define void @g() {
  call void @llvm.sideeffect()
  ret void
}
define void @f() mustprogress {
entry:
  br label %again
again:
  call void @g()
  br label %again
}'
# What LangRef doesn't settle about loop metadata is refused: latches that don't all carry it, a copy off a latch where
# control flow is irreducible, and a cycle through promised loops that leaves each of them, which only irreducible
# control flow allows.
promise_metadata='!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.mustprogress"}
!2 = distinct !{!2, !1}'
refuses "latches don't all carry it" "define i32 @f(i32 %x) {
entry:
  br label %h
h:
  %c = icmp eq i32 %x, 0
  br i1 %c, label %a, label %b
a:
  br label %h, !llvm.loop !0
b:
  br label %h
}
$promise_metadata"
refuses 'irreducible control flow' "define i32 @f(i1 %c) {
entry:
  br i1 %c, label %a, label %b
a:
  br label %b, !llvm.loop !0
b:
  br label %a
}
$promise_metadata"
refuses 'leaves each of them' "define i32 @f(i1 %c, i1 %d, i1 %e) {
entry:
  br i1 %c, label %h1, label %h2
h1:
  br i1 %d, label %h1, label %h2, !llvm.loop !0
h2:
  br i1 %e, label %h2, label %h1, !llvm.loop !2
}
$promise_metadata"

# Two rules no real program can show, since the rest imply them on every layout LLVM allows. The first only
# matters for an object that crosses the top of the address space, which LLVM rules out. The second says the
# offsets' running total can't wrap under `nuw`, which adding them to the address one by one already says.
cat >"$work/GepRules.lean" <<'LEAN'
import IRLean
open IRLean

example :
    Mem.gep ((Mem.empty fun _ => BitVec.ofNat 64 (2 ^ 64 - 4)).addGlobal 1 8 false #[]) (some ⟨1, 0#64, []⟩)
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
