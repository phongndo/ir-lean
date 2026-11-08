; O1 pilot: a loop O1 cannot remove, so its target keeps no willreturn (loop passes).
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @f(i32 noundef %n) {
entry:
  br label %h
h:
  %x = phi i32 [ %n, %entry ], [ %y, %b ]
  %k = phi i32 [ 0, %entry ], [ %k1, %b ]
  %c = icmp ule i32 %x, 1
  br i1 %c, label %done, label %b
b:
  %odd = and i32 %x, 1
  %isodd = icmp ne i32 %odd, 0
  %t3 = mul i32 %x, 3
  %t31 = add i32 %t3, 1
  %half = lshr i32 %x, 1
  %y = select i1 %isodd, i32 %t31, i32 %half
  %k1 = add i32 %k, 1
  br label %h
done:
  ret i32 %k
}
