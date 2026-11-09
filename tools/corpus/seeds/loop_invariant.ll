; A loop with an invariant product inside it (licm, loop-rotate, indvars).
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @f(i32 noundef %n, i32 noundef %a, i32 noundef %b) {
entry:
  br label %h
h:
  %i = phi i32 [ 0, %entry ], [ %i1, %body ]
  %s = phi i32 [ 0, %entry ], [ %s1, %body ]
  %c = icmp eq i32 %i, %n
  br i1 %c, label %done, label %body
body:
  %p = mul i32 %a, %b
  %q = xor i32 %s, %p
  %s1 = add i32 %q, %i
  %i1 = add i32 %i, 1
  br label %h
done:
  ret i32 %s
}
