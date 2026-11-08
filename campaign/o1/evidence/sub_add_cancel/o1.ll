; ModuleID = '<stdin>'
source_filename = "<stdin>"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none)
define noundef i8 @f(i8 noundef returned %x, i8 noundef %y) local_unnamed_addr #0 {
  ret i8 %x
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind willreturn memory(none) }
