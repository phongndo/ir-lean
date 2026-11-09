; Memory errors the model must stop on, through the emitter: accesses out of bounds, after a free, through a dangling
; stack pointer or the wrong provenance, and frees of what `malloc` didn't return. Comparing with native code can't
; show these, so they run with `tests/differential.py --expect-ub`. `tests/proofs/MemoryModel.lean` proves, for every
; memory, which undefined behavior each kind is. `malloc` never fails in these runs.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare ptr @malloc(i64)
declare void @free(ptr)
declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)

@seven = constant i32 7

; Eight bytes from a four-byte alloca.
define i32 @load_past_end(i32 %x) {
  %a = alloca i32, align 4
  store i32 %x, ptr %a, align 4
  %v = load i64, ptr %a, align 4
  %t = trunc i64 %v to i32
  ret i32 %t
}

; One element past the end, without `inbounds`, so the pointer is fine and only the store is undefined.
define i32 @store_past_end(i32 %x) {
  %a = alloca [4 x i32], align 4
  %p = getelementptr i32, ptr %a, i64 4
  store i32 %x, ptr %p, align 4
  ret i32 %x
}

define i32 @heap_past_end(i32 %x) {
  %p = call ptr @malloc(i64 4)
  %q = getelementptr i8, ptr %p, i64 4
  store i32 %x, ptr %q, align 1
  call void @free(ptr %p)
  ret i32 %x
}

; Offsets are unsigned, so one byte before the start is past the end.
define i32 @load_before_start(i32 %x) {
  %a = alloca [2 x i32], align 4
  store i32 %x, ptr %a, align 4
  %p = getelementptr i8, ptr %a, i64 -1
  %v = load i8, ptr %p, align 1
  %z = zext i8 %v to i32
  ret i32 %z
}

define i32 @use_after_free(i32 %x) {
  %p = call ptr @malloc(i64 4)
  store i32 %x, ptr %p, align 4
  call void @free(ptr %p)
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

define i32 @double_free(i32 %x) {
  %p = call ptr @malloc(i64 4)
  call void @free(ptr %p)
  call void @free(ptr %p)
  ret i32 %x
}

define i32 @free_stack(i32 %x) {
  %a = alloca i32, align 4
  call void @free(ptr %a)
  ret i32 %x
}

define i32 @free_interior(i32 %x) {
  %p = call ptr @malloc(i64 8)
  %q = getelementptr i8, ptr %p, i64 4
  call void @free(ptr %q)
  ret i32 %x
}

; A pointer to an alloca outlives its function. Storing through it is undefined however LangRef's lifetime rules are
; read. Loading through it is undefined in the model too, where LangRef would give poison for a dead stack object.
define internal ptr @escapes(i32 %x) {
  %a = alloca i32, align 4
  store i32 %x, ptr %a, align 4
  ret ptr %a
}

define i32 @dangling_stack(i32 %x) {
  %p = call ptr @escapes(i32 %x)
  store i32 %x, ptr %p, align 4
  ret i32 %x
}

define i32 @store_to_constant(i32 %x) {
  store i32 %x, ptr @seven, align 4
  ret i32 %x
}

define i32 @load_null(i32 %x) {
  %v = load i32, ptr null, align 4
  %r = add i32 %v, %x
  ret i32 %r
}

; Ranges that overlap without being the same.
define i32 @memcpy_overlapping(i32 %x) {
  %a = alloca [8 x i8], align 1
  %q = getelementptr inbounds i8, ptr %a, i64 2
  call void @llvm.memcpy.p0.p0.i64(ptr %q, ptr %a, i64 4, i1 false)
  ret i32 %x
}

; `align 8` at an address four bytes into an 8-aligned object.
define i32 @load_misaligned(i32 %x) {
  %a = alloca [2 x i64], align 8
  store i64 0, ptr %a, align 8
  %p = getelementptr inbounds i8, ptr %a, i64 4
  %v = load i32, ptr %p, align 8
  ret i32 %v
}

; The right address, the wrong provenance: `%p` has `%b`'s address, but it's based on `%a`, so it can only reach `%a`.
define i32 @wrong_provenance(i32 %x) {
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  store i32 %x, ptr %b, align 4
  %ia = ptrtoint ptr %a to i64
  %ib = ptrtoint ptr %b to i64
  %d = sub i64 %ib, %ia
  %p = getelementptr i8, ptr %a, i64 %d
  %v = load i32, ptr %p, align 4
  ret i32 %v
}
