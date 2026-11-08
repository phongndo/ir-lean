; ModuleID = '<stdin>'
source_filename = "<stdin>"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none)
define noundef i32 @f(i32 noundef %x, i32 noundef %y) local_unnamed_addr #0 {
  %b = add i32 %x, 8
  %c = add i32 %b, %y
  ret i32 %c
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind willreturn memory(none) }
