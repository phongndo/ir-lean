; Functions whose runs make choices, through `freeze`, against native code. A result Lean gives under one choice
; matches native code where the model allows what it did, and otherwise is skipped, since another choice could give
; what native code did. Two choices that agree don't show a result doesn't depend on them: here both 0 and 1 make
; `icmp ult %f, 2` true, while native code may have frozen the poison to anything.
define i8 @frozen_compare(i8 %x) {
  %v = add nuw i8 %x, 10
  %f = freeze i8 %v
  %c = icmp ult i8 %f, 2
  %r = zext i1 %c to i8
  ret i8 %r
}

; Poison for every x but 0, which gives 255.
define i8 @frozen_compare_mostly_poison(i8 %x) {
  %v = add nuw i8 %x, 255
  %f = freeze i8 %v
  %c = icmp ult i8 %f, 2
  %r = zext i1 %c to i8
  ret i8 %r
}

; A freeze that never sees poison is compared like any other function.
define i8 @frozen_value(i8 %x) {
  %f = freeze i8 %x
  %r = add i8 %f, 1
  ret i8 %r
}
