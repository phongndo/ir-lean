; tests/binding.py's input for a promise the model checks: a loop with no side effects, whose result nothing uses, in a
; function marked mustprogress. It never ends for an odd %n, which the promise makes undefined, so loop-deletion
; deletes it. Without mustprogress, loop-deletion leaves it.
define i32 @f(i32 noundef %n) mustprogress {
entry:
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %next, %loop ]
  %next = add i32 %i, 2
  %done = icmp eq i32 %i, %n
  br i1 %done, label %exit, label %loop
exit:
  ret i32 0
}
