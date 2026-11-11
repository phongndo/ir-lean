; correct
; A cut that's refined and not equal, inside a loop: `add nuw` to `add`. @cut_src and @cut_tgt are the cut and its
; replacement, each as a function of the value that goes in, and @src and @tgt are the loop with each. Where a round's
; sum wraps, the source's is poison from then on and the target's is a value, so from the next round the two cuts get
; different inputs, and the rest of the round, a division and an `xor`, runs on a value where the source had poison.
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
  br label %head

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
  br label %head

exit:
  ret i8 %acc
}
