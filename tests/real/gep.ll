; `getelementptr` that LLVM defines, so the checks on the flags must leave it alone. These run against
; native code, failing if any input is skipped.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%pair = type { i32, [2 x i32] }

; Every step of a multi-index `inbounds` stays in the object.
define i32 @multi_index_inside(i32 %x) {
  %a = alloca [2 x [2 x i32]], align 4
  %i = and i32 %x, 1
  %p = getelementptr inbounds [2 x [2 x i32]], ptr %a, i64 0, i32 %i, i64 1
  store i32 %x, ptr %p, align 4
  %r = getelementptr inbounds [2 x i32], ptr %a, i32 %i, i64 1
  %v = load i32, ptr %r, align 4
  ret i32 %v
}

define i32 @struct_field(i32 %x) {
  %a = alloca %pair, align 4
  %i = and i32 %x, 1
  %p = getelementptr inbounds nuw %pair, ptr %a, i64 0, i32 1, i32 %i
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; One past the end is in bounds, on the way there and as a base.
define i32 @one_past_the_end(i32 %x) {
  %a = alloca [2 x i32], align 4
  %end = getelementptr inbounds [2 x i32], ptr %a, i64 1
  %p = getelementptr inbounds i32, ptr %end, i64 -1
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; Each step counts, not what's between them: a step can pass through the end without stopping there.
define i32 @multi_index_to_the_end_and_back(i32 %x) {
  %a = alloca [2 x i32], align 4
  %p = getelementptr inbounds [2 x i32], ptr %a, i64 1, i64 -1
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; All-zero indices are always `inbounds`, whatever the base is.
define i32 @zero_indices_out_of_bounds(i32 %x) {
  %a = alloca i64, align 8
  %q = getelementptr i8, ptr %a, i64 100
  %z = getelementptr inbounds i8, ptr %q, i64 0
  %y = getelementptr inbounds [2 x i32], ptr %z, i64 0, i64 0
  %p = getelementptr i8, ptr %y, i64 -100
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; With no flags, a pointer can go anywhere so long as it's back by the time it's used.
define i32 @no_flags_out_and_back(i32 %x) {
  %a = alloca i64, align 8
  %p = getelementptr [2 x i64], ptr %a, i64 1, i64 -2
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; `nusw` lets an offset be negative, so long as the address doesn't go below zero.
define i32 @nusw_negative(i32 %x) {
  %a = alloca i64, align 8
  %end = getelementptr nusw i8, ptr %a, i64 8
  %p = getelementptr nusw i8, ptr %end, i64 -8
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

define i32 @nuw_forward(i32 %x) {
  %a = alloca [2 x i32], align 4
  %p = getelementptr nuw i32, ptr %a, i64 1
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; `nuw` alone says nothing about staying in the object.
define i32 @nuw_out_and_back(i32 %x) {
  %a = alloca i64, align 8
  %q = getelementptr nuw i8, ptr %a, i64 100
  %p = getelementptr i8, ptr %q, i64 -100
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  ret i32 %v
}
