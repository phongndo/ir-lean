; Code the model stops on without an answer, which LLVM doesn't call undefined. These must not count as
; undefined behavior: they run with `tests/differential.py --expect-stop`.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare i64 @strlen(ptr)

; LLVM picks some value.
define i32 @freeze_poison(i32 %x) {
  %p = add nuw i32 -1, 1
  %f = freeze i32 %p
  %r = xor i32 %f, %x
  ret i32 %r
}

; LLVM has no settled answer for a stored pointer read back as an integer.
define i64 @pointer_as_bytes(i32 %x) {
  %a = alloca ptr, align 8
  store ptr %a, ptr %a, align 8
  %v = load i64, ptr %a, align 8
  ret i64 %v
}

@fn_table = global ptr @strlen

; A function outside the module, called through a pointer.
define i64 @unknown_callee(i32 %x) {
  %f = load ptr, ptr @fn_table, align 8
  %r = call i64 %f(ptr @fn_table)
  ret i64 %r
}

; LLVM reads `undef` here, where the model has no value for what `strlen` does next.
define i64 @strlen_of_uninit(i32 %x) {
  %a = alloca [4 x i8], align 1
  %r = call i64 @strlen(ptr %a)
  ret i64 %r
}

; `memory(none)` only rules out what's observed from outside, and the model can't tell if this is.
@shared = global i32 7

define internal i32 @reads_in_memory_none() memory(none) {
  %v = load i32, ptr @shared, align 4
  ret i32 %v
}

define i32 @memory_none_read(i32 %x) {
  %r = call i32 @reads_in_memory_none()
  ret i32 %r
}

; `noalias` on a result rules out storage the caller can reach, and the model can't tell if it can.
define internal noalias ptr @noalias_of_shared() {
  ret ptr @shared
}

define i32 @noalias_result_not_new(i32 %x) {
  %p = call ptr @noalias_of_shared()
  ret i32 %x
}

; LangRef doesn't settle what a bundle says about poison.
declare void @llvm.assume(i1)

define i32 @assume_nonnull_of_poison(i32 %x) {
  call void @llvm.assume(i1 true) [ "nonnull"(ptr poison) ]
  ret i32 %x
}

; LangRef says `returned` holds, but not what happens if it doesn't.
define internal ptr @returns_the_other(ptr returned %p, ptr %q) {
  ret ptr %q
}

define i32 @returned_differs(i32 %x) {
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %r = call ptr @returns_the_other(ptr %a, ptr %b)
  ret i32 %x
}

define internal i32 @returns_another_int(i32 returned %x, i32 %y) {
  ret i32 %y
}

define i32 @returned_int_differs(i32 %x) {
  %y = add i32 %x, 1
  %r = call i32 @returns_another_int(i32 %x, i32 %y)
  ret i32 %r
}

declare ptr @malloc(i64)
declare void @free(ptr)

; `malloc` and `free` aren't told apart from anything else `memory(inaccessiblemem: none)` rules out.
define internal void @mallocs_in_memory_none() memory(inaccessiblemem: none) {
  %p = call ptr @malloc(i64 4)
  ret void
}

define i32 @memory_none_mallocs(i32 %x) {
  call void @mallocs_in_memory_none()
  ret i32 %x
}

; Whether an address is captured depends on what a run with another address would do, so the model stops
; at the first look at one it was told not to capture.
define internal i64 @looks_at_uncaptured(ptr captures(none) %p) {
  %v = ptrtoint ptr %p to i64
  ret i64 %v
}

define i64 @captures_none_ptrtoint(i32 %x) {
  %a = alloca i32, align 4
  %r = call i64 @looks_at_uncaptured(ptr %a)
  ret i64 %r
}

define internal i1 @compares_uncaptured(ptr captures(none) %p, ptr %q) {
  %c = icmp eq ptr %p, %q
  ret i1 %c
}

define i32 @captures_none_compared(i32 %x) {
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %c = call i1 @compares_uncaptured(ptr %a, ptr %b)
  ret i32 %x
}

; `address_is_null` allows that one question and no other.
define internal i1 @compares_more_than_null(ptr captures(address_is_null) %p, ptr %q) {
  %c = icmp eq ptr %p, %q
  ret i1 %c
}

define i32 @address_is_null_compared_with_another(i32 %x) {
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %c = call i1 @compares_more_than_null(ptr %a, ptr %b)
  ret i32 %x
}

define internal i1 @compares_with_null_uncaptured(ptr captures(none) %p) {
  %c = icmp eq ptr %p, null
  ret i1 %c
}

define i32 @captures_none_compared_with_null(i32 %x) {
  %a = alloca i32, align 4
  %c = call i1 @compares_with_null_uncaptured(ptr %a)
  ret i32 %x
}

; A copy that gets out still can't be looked at.
define internal void @stores_it_uncaptured(ptr captures(none) %p, ptr %to) {
  store ptr %p, ptr %to, align 8
  ret void
}

define i64 @captures_none_looked_at_after(i32 %x) {
  %a = alloca i32, align 4
  %slot = alloca ptr, align 8
  call void @stores_it_uncaptured(ptr %a, ptr %slot)
  %q = load ptr, ptr %slot, align 8
  %v = ptrtoint ptr %q to i64
  ret i64 %v
}

; It doesn't matter which side of the comparison it's on.
define internal i1 @compares_uncaptured_on_the_right(ptr %q, ptr captures(none) %p) {
  %c = icmp eq ptr %q, %p
  ret i1 %c
}

define i32 @captures_none_compared_on_the_right(i32 %x) {
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %c = call i1 @compares_uncaptured_on_the_right(ptr %a, ptr %b)
  ret i32 %x
}
