; Duplicating a freeze: wrong. src freezes x once, so a - a is 0. tgt freezes it twice, and for a poison x
; the two can differ, so tgt can return anything. The model stops at both freezes of a poison x.
define i8 @src(i8 %x) {
  %a = freeze i8 %x
  %r = sub i8 %a, %a
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  %a = freeze i8 %x
  %b = freeze i8 %x
  %r = sub i8 %a, %b
  ret i8 %r
}
