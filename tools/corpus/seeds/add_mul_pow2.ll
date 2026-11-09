; An add of zero, and a multiply by a power of two (instcombine).
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @f(i32 noundef %x) {
  %a = add i32 %x, 0
  %m = mul i32 %a, 8
  ret i32 %m
}
