; Deleting a loop that never ends, in a function without mustprogress: wrong. At x = 0 src runs forever, and
; tgt returns.
define i8 @src(i8 %x) {
entry:
  %c = icmp eq i8 %x, 0
  br i1 %c, label %loop, label %done
loop:
  br label %loop
done:
  ret i8 %x
}

define i8 @tgt(i8 %x) {
entry:
  ret i8 %x
}
