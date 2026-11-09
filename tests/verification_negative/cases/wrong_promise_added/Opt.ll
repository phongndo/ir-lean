; Adding mustprogress to a function whose loop never ends at x = 0: wrong. There src never returns, which LLVM
; allows, and tgt is undefined.
define i8 @src(i8 %x) {
entry:
  %c = icmp eq i8 %x, 0
  br i1 %c, label %loop, label %done
loop:
  br label %loop
done:
  ret i8 %x
}

define i8 @tgt(i8 %x) mustprogress {
entry:
  %c = icmp eq i8 %x, 0
  br i1 %c, label %loop, label %done
loop:
  br label %loop
done:
  ret i8 %x
}
