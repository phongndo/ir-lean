; correct
; alive2: unknown: Alive2 doesn't take `nofree`, which clang puts on the pointer, so it has no verdict on this one
; The cut lemma on a function as clang compiled it: tests/cut/clang_sum.c's loop, which adds up three times each word
; it loads, at -O1. @src is clang's IR for it, as tests/cut.sh checks by compiling it again: its attributes, the
; promises on its pointer, and its loop's `llvm.loop.mustprogress` are clang's. @tgt is @src with the multiply
; replaced, `mul %x, 3` by `add (shl %x, 1), %x`, and @cut_src and @cut_tgt are those two as functions of the word.
; tests/cut/ClangSum.lean proves @tgt refines @src from the cut's proof. docs/refinement.md.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @cut_src(i32 %x) {
  %y = mul i32 %x, 3
  ret i32 %y
}

define i32 @cut_tgt(i32 %x) {
  %twice = shl i32 %x, 1
  %y = add i32 %twice, %x
  ret i32 %y
}

define i32 @src(ptr nofree noundef readonly captures(none) %0, i32 noundef %1) local_unnamed_addr #0 {
  %3 = icmp eq i32 %1, 0
  br i1 %3, label %6, label %4

4:                                                ; preds = %2
  %5 = zext i32 %1 to i64
  br label %8

6:                                                ; preds = %8, %2
  %7 = phi i32 [ 0, %2 ], [ %14, %8 ]
  ret i32 %7

8:                                                ; preds = %4, %8
  %9 = phi i64 [ 0, %4 ], [ %15, %8 ]
  %10 = phi i32 [ 0, %4 ], [ %14, %8 ]
  %11 = getelementptr inbounds nuw [4 x i8], ptr %0, i64 %9
  %12 = load i32, ptr %11, align 4
  %13 = mul i32 %12, 3
  %14 = add i32 %13, %10
  %15 = add nuw nsw i64 %9, 1
  %16 = icmp eq i64 %15, %5
  br i1 %16, label %6, label %8, !llvm.loop !5
}

define i32 @tgt(ptr nofree noundef readonly captures(none) %0, i32 noundef %1) local_unnamed_addr #0 {
  %3 = icmp eq i32 %1, 0
  br i1 %3, label %6, label %4

4:                                                ; preds = %2
  %5 = zext i32 %1 to i64
  br label %8

6:                                                ; preds = %8, %2
  %7 = phi i32 [ 0, %2 ], [ %14, %8 ]
  ret i32 %7

8:                                                ; preds = %4, %8
  %9 = phi i64 [ 0, %4 ], [ %15, %8 ]
  %10 = phi i32 [ 0, %4 ], [ %14, %8 ]
  %11 = getelementptr inbounds nuw [4 x i8], ptr %0, i64 %9
  %12 = load i32, ptr %11, align 4
  %twice = shl i32 %12, 1
  %13 = add i32 %twice, %12
  %14 = add i32 %13, %10
  %15 = add nuw nsw i64 %9, 1
  %16 = icmp eq i64 %15, %5
  br i1 %16, label %6, label %8, !llvm.loop !8
}

attributes #0 = { nofree norecurse nosync nounwind sspstrong memory(argmem: read) uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}
!0 = !{i32 4, !"probe-stack", !"inline-asm"}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{i32 7, !"frame-pointer", i32 2}
!4 = !{!"clang version 23.1.3"}
!5 = distinct !{!5, !6, !7}
!6 = !{!"llvm.loop.mustprogress"}
!7 = !{!"llvm.loop.unroll.disable"}
!8 = distinct !{!8, !6, !7}
