; Code the model must stop on, because LLVM says it's undefined. Comparing with native code can't
; show this, so these run with `tests/differential.py --expect-ub`.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare void @llvm.lifetime.start.p0(ptr)
declare void @llvm.lifetime.end.p0(ptr)
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)
declare i32 @llvm.ctpop.i32(i32)
declare i32 @llvm.expect.i32(i32, i32)

; The index times 8 wraps to 0, and `inbounds` makes that poison, so the load is undefined.
define i32 @gep_constant_wraps(i32 %x) {
  %a = alloca i64, align 8
  store i32 %x, ptr %a, align 4
  %p = getelementptr inbounds i64, ptr %a, i64 2305843009213693952
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; Each index fits, but adding them wraps to 0.
define i32 @gep_constant_sum_wraps(i32 %x) {
  %a = alloca [2 x i64], align 8
  store i32 %x, ptr %a, align 4
  %p = getelementptr inbounds [2 x i64], ptr %a, i64 -576460752303423488, i64 -1152921504606846976
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; The total is 0, but the first two offsets already overflow.
define i32 @gep_partial_sum_wraps(i32 %x) {
  %a = alloca i64, align 8
  store i32 %x, ptr %a, align 4
  %i = add i64 0, 1
  %p = getelementptr nusw [1 x [1 x i8]], ptr %a, i64 9223372036854775807, i64 %i, i64 -9223372036854775808
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

define i32 @store_after_lifetime_end(i32 %x) {
  %a = alloca i32, align 4
  call void @llvm.lifetime.start.p0(ptr %a)
  call void @llvm.lifetime.end.p0(ptr %a)
  store i32 %x, ptr %a, align 4
  ret i32 %x
}

; An alloca with `lifetime.start` is dead until it runs.
define i32 @store_before_lifetime_start(i32 %x) {
  %a = alloca i32, align 4
  store i32 %x, ptr %a, align 4
  call void @llvm.lifetime.start.p0(ptr %a)
  ret i32 %x
}

; `align 8` makes the misaligned pointer poison.
define i32 @memset_misaligned(i32 %x) {
  %a = alloca i64, align 8
  %p = getelementptr inbounds i8, ptr %a, i64 1
  call void @llvm.memset.p0.i64(ptr align 8 %p, i8 0, i64 1, i1 false)
  ret i32 %x
}

define i32 @memcpy_misaligned(i32 %x) {
  %a = alloca [2 x i64], align 8
  %p = getelementptr inbounds i8, ptr %a, i64 1
  %q = getelementptr inbounds i8, ptr %a, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr %q, ptr align 8 %p, i64 1, i1 false)
  ret i32 %x
}

; `expect` returns its first argument, but the second one's attributes still count.
define i32 @unused_argument_out_of_range(i32 %x) {
  %r = call i32 @llvm.expect.i32(i32 %x, i32 noundef range(i32 1, 2) 0)
  ret i32 %r
}

; Zero bits are set, which the return attributes make undefined.
define i32 @intrinsic_result_out_of_range(i32 %x) {
  %r = call noundef range(i32 1, 2) i32 @llvm.ctpop.i32(i32 0)
  ret i32 %r
}
