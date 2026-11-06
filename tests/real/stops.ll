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
