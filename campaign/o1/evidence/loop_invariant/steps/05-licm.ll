; ModuleID = '<stdin>'
source_filename = "<stdin>"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @f(i32 noundef %n, i32 noundef %a, i32 noundef %b) local_unnamed_addr {
entry:
  %c1 = icmp eq i32 0, %n
  br i1 %c1, label %done, label %body.lr.ph

body.lr.ph:                                       ; preds = %entry
  %p = mul i32 %b, %a
  br label %body

body:                                             ; preds = %body.lr.ph, %body
  %s3 = phi i32 [ 0, %body.lr.ph ], [ %s1, %body ]
  %i2 = phi i32 [ 0, %body.lr.ph ], [ %i1, %body ]
  %q = xor i32 %s3, %p
  %s1 = add i32 %q, %i2
  %i1 = add i32 %i2, 1
  %c = icmp eq i32 %i1, %n
  br i1 %c, label %h.done_crit_edge, label %body

h.done_crit_edge:                                 ; preds = %body
  %split = phi i32 [ %s1, %body ]
  br label %done

done:                                             ; preds = %h.done_crit_edge, %entry
  %s.lcssa = phi i32 [ %split, %h.done_crit_edge ], [ 0, %entry ]
  ret i32 %s.lcssa
}
