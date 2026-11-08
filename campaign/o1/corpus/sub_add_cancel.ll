; O1 pilot: (x - y) + y, masked with -1 and or-ed with 0 (instcombine).
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i8 @f(i8 noundef %x, i8 noundef %y) {
  %d = sub i8 %x, %y
  %e = add i8 %d, %y
  %m = and i8 %e, -1
  %o = or i8 %m, 0
  ret i8 %o
}
