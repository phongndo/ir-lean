; correct
; Two calls that only read, with no call with effects between, merged: the source picks the target's answer for both.
; What early-cse does.
declare i8 @peek(i8) memory(read)

define i8 @src(i8 %x) {
  %a = call i8 @peek(i8 %x)
  %b = call i8 @peek(i8 %x)
  %c = sub i8 %a, %b
  ret i8 %c
}

define i8 @tgt(i8 %x) {
  %a = call i8 @peek(i8 %x)
  ret i8 0
}
