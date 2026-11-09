; tests/binding.py's input for a claim the model can't judge: instcombine drops the add and keeps the freeze,
; which is right in LLVM. For x of 8 or more the shift is poison, and the model stops at the frozen poison, on both
; sides, so the two are equal there, and that says nothing about LLVM.
define i8 @f(i8 noundef %x) {
  %y = shl i8 1, %x
  %a = freeze i8 %y
  %r = add i8 %a, 0
  ret i8 %r
}
