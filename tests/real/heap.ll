; `malloc` and `free`, in IR so the optimizer can't remove `free` of null, reachable from functions
; that only take integers so tests/differential.py can call them.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare ptr @malloc(i64)
declare void @free(ptr)

; Frees null when `x` is 0, and a real allocation otherwise.
define i32 @free_maybe_null(i32 %x) {
  %is_zero = icmp eq i32 %x, 0
  br i1 %is_zero, label %done, label %alloc

alloc:
  %p = call ptr @malloc(i64 16)
  %failed = icmp eq ptr %p, null
  br i1 %failed, label %out, label %use

use:
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  br label %done

done:
  %q = phi ptr [ null, %0 ], [ %p, %use ]
  %r = phi i32 [ 1, %0 ], [ %v, %use ]
  call void @free(ptr %q)
  ret i32 %r

out:
  ret i32 -1
}
