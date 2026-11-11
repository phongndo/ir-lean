; tests/rules_test.py's input for certify mode: the states of a chain of three rule applications, as IR, with nothing
; from a matcher. `or_zero` takes @s0 to @s1, `and_allOnes` @s1 to @s2, and `add_sub_cancel` @s2 to @s3.
target triple = "x86_64-unknown-linux-gnu"

define i8 @s0(i8 %x, i8 %y) {
  %d = sub i8 %x, %y
  %e = add i8 %d, %y
  %m = and i8 %e, -1
  %o = or i8 %m, 0
  ret i8 %o
}

define i8 @s1(i8 %x, i8 %y) {
  %d = sub i8 %x, %y
  %e = add i8 %d, %y
  %m = and i8 %e, -1
  ret i8 %m
}

define i8 @s2(i8 %x, i8 %y) {
  %d = sub i8 %x, %y
  %e = add i8 %d, %y
  ret i8 %e
}

define i8 @s3(i8 %x, i8 %y) {
  ret i8 %x
}
