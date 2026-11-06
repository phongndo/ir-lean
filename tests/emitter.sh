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

# Linkage: only a definition that's certainly the one a run uses can be proved about.
for linkage in weak weak_odr linkonce linkonce_odr available_externally; do
  refuses linkage "define $linkage i32 @f(i32 %x) { ret i32 %x }"
done
refuses "isn't translated" 'define weak i32 @g() { ret i32 0 }
define i32 @f() { %r = call i32 @g()
  ret i32 %r }'
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
  refuses "attribute" "define i32 @f(i32 %x) $attribute { ret i32 %x }"
done
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
# `tbaa` has no rule to model, and the others aren't used. -fno-strict-aliasing leaves `tbaa` out.
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

# `mustprogress` is on the list on purpose, and this is what that means: a run LLVM calls undefined is
# `none` here, not a stop. If the model ever starts to treat it as undefined, this has to change with it.
cat >"$work/Spin.ll" <<'IR'
define i32 @spin(i32 %x) mustprogress {
entry:
  br label %again
again:
  br label %again
}
IR
"$tool" "$work/Spin.ll" -o "$work/Spin.lean" --namespace Spin --no-code
cat >"$work/SpinProof.lean" <<'LEAN'
import Spin
open LLVMLean Spin Lean.Order

theorem spin_never_finishes (x : Val 32) : spin x = none := by
  have loop : run spin.step .again = none := by
    refine run.fixpoint_induct spin.step (fun f => f .again = none) ?_ ?_
    · exact admissible_apply (fun _ r => r = none) spin.Block.again (admissible_flatOrder _ rfl)
    · intro f h
      simpa [spin.step, jump, Outcome.ok] using h
  rw [spin, run]
  simpa [spin.step, jump, Outcome.ok] using loop
LEAN
if lean -R "$work" -o "$work/Spin.olean" "$work/Spin.lean" && lean "$work/SpinProof.lean"; then
  printf 'ok    a mustprogress function that spins never finishes in the model\n'
else
  fail 'the model no longer treats a mustprogress function that spins as never finishing'
fi

# Two rules no real program can show, since the rest imply them on every layout LLVM allows. The first only
# matters for an object that crosses the top of the address space, which LLVM rules out. The second says the
# offsets' running total can't wrap under `nuw`, which adding them to the address one by one already says.
cat >"$work/GepRules.lean" <<'LEAN'
import LLVMLean
open LLVMLean

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
