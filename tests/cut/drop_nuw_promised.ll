; correct
; The cut lemma under a promise to progress: tests/cut/drop_nuw_loop.ll's loops, each marked
; `llvm.loop.mustprogress`, as clang marks a C loop. The cut is `add nuw` to `add`, and the two loops promise the
; same, so they're in step under the promise too.
define i8 @cut_src(i8 %x) {
  %y = add nuw i8 %x, 3
  ret i8 %y
}

define i8 @cut_tgt(i8 %x) {
  %y = add i8 %x, 3
  ret i8 %y
}

define i8 @src(i8 %a, i8 %n) {
entry:
  br label %head

head:
  %i = phi i8 [ 0, %entry ], [ %i1, %body ]
  %acc = phi i8 [ %a, %entry ], [ %acc1, %body ]
  %more = icmp ult i8 %i, %n
  br i1 %more, label %body, label %exit

body:
  %y = add nuw i8 %acc, 3
  %d = udiv i8 %y, 3
  %acc1 = xor i8 %d, %i
  %i1 = add i8 %i, 1
  br label %head, !llvm.loop !0

exit:
  ret i8 %acc
}

define i8 @tgt(i8 %a, i8 %n) {
entry:
  br label %head

head:
  %i = phi i8 [ 0, %entry ], [ %i1, %body ]
  %acc = phi i8 [ %a, %entry ], [ %acc1, %body ]
  %more = icmp ult i8 %i, %n
  br i1 %more, label %body, label %exit

body:
  %y = add i8 %acc, 3
  %d = udiv i8 %y, 3
  %acc1 = xor i8 %d, %i
  %i1 = add i8 %i, 1
  br label %head, !llvm.loop !2

exit:
  ret i8 %acc
}

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.mustprogress"}
!2 = distinct !{!2, !1}
