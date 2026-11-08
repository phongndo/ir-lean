; ModuleID = '<stdin>'
source_filename = "<stdin>"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @f(i32 noundef %n) local_unnamed_addr {
entry:
  %c1 = icmp ult i32 %n, 2
  br i1 %c1, label %done, label %b.lr.ph

b.lr.ph:                                          ; preds = %entry
  br label %b

b:                                                ; preds = %b.lr.ph, %b
  %k3 = phi i32 [ 0, %b.lr.ph ], [ %k1, %b ]
  %x2 = phi i32 [ %n, %b.lr.ph ], [ %y, %b ]
  %odd = and i32 %x2, 1
  %isodd.not = icmp eq i32 %odd, 0
  %t3 = mul i32 %x2, 3
  %t31 = add i32 %t3, 1
  %half = lshr i32 %x2, 1
  %y = select i1 %isodd.not, i32 %half, i32 %t31
  %k1 = add i32 %k3, 1
  %c = icmp ult i32 %y, 2
  br i1 %c, label %h.done_crit_edge, label %b

h.done_crit_edge:                                 ; preds = %b
  %split = phi i32 [ %k1, %b ]
  br label %done

done:                                             ; preds = %h.done_crit_edge, %entry
  %k.lcssa = phi i32 [ %split, %h.done_crit_edge ], [ 0, %entry ]
  ret i32 %k.lcssa
}
