; ModuleID = '<stdin>'
source_filename = "<stdin>"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none)
define range(i16 0, 16) i16 @f(i16 noundef %x, i16 noundef %y) local_unnamed_addr #0 {
  %c = and i16 %x, 15
  %d = xor i16 %c, 15
  ret i16 %d
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind willreturn memory(none) }
