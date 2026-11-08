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
refuses 'call to external' 'declare void @returns()
define i32 @f(i32 %x) {
  call void @returns()
  ret i32 %x
}'
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
open IRLean Spin Lean.Order

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
