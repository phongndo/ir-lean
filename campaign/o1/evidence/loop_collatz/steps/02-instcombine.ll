; ModuleID = '<stdin>'
source_filename = "<stdin>"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @f(i32 noundef %n) local_unnamed_addr {
entry:
  br label %h

h:                                                ; preds = %b, %entry
  %x = phi i32 [ %n, %entry ], [ %y, %b ]
  %k = phi i32 [ 0, %entry ], [ %k1, %b ]
  %c = icmp ult i32 %x, 2
  br i1 %c, label %done, label %b

b:                                                ; preds = %h
  %odd = and i32 %x, 1
  %isodd.not = icmp eq i32 %odd, 0
  %t3 = mul i32 %x, 3
  %t31 = add i32 %t3, 1
  %half = lshr i32 %x, 1
  %y = select i1 %isodd.not, i32 %half, i32 %t31
  %k1 = add i32 %k, 1
  br label %h

done:                                             ; preds = %h
  ret i32 %k
}
