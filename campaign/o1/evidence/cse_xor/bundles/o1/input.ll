; O1 pilot: the same xor twice (early-cse), then x + x (instcombine).
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @f(i32 noundef %x, i32 noundef %y) {
  %a = xor i32 %x, %y
  %b = xor i32 %x, %y
  %c = add i32 %a, %b
  ret i32 %c
}
