; O1 pilot: values nothing uses (dead code elimination in instcombine, adce, bdce).
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i16 @f(i16 noundef %x, i16 noundef %y) {
  %a = mul i16 %x, %y
  %b = udiv i16 %a, 7
  %c = xor i16 %x, 255
  %d = and i16 %c, 15
  ret i16 %d
}
