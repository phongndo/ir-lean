; incorrect
; Dropping the `freeze` of a branch condition: at poison the source branches one way or the other, and the target's
; branch on poison is undefined.
define i8 @src(i1 %c) {
entry:
  %f = freeze i1 %c
  br i1 %f, label %a, label %b
a:
  ret i8 1
b:
  ret i8 2
}
define i8 @tgt(i1 %c) {
entry:
  br i1 %c, label %a, label %b
a:
  ret i8 1
b:
  ret i8 2
}
