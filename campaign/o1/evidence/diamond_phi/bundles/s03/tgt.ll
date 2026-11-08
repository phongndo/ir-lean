; ModuleID = '<stdin>'
source_filename = "<stdin>"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @f(i32 noundef %x, i1 noundef %c) local_unnamed_addr {
entry:
  %r.v = select i1 %c, i32 1, i32 -1
  %r = add i32 %x, %r.v
  ret i32 %r
}
