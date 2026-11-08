; ModuleID = '<stdin>'
source_filename = "<stdin>"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @f(i32 noundef %x, i1 noundef %c) {
entry:
  br i1 %c, label %t, label %e

t:                                                ; preds = %entry
  %a = add i32 %x, 1
  br label %j

e:                                                ; preds = %entry
  %b = sub i32 %x, 1
  br label %j

j:                                                ; preds = %e, %t
  %r = phi i32 [ %a, %t ], [ %b, %e ]
  ret i32 %r
}
