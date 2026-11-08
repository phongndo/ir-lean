; tests/binding.py's input for a claim the model can't judge: instcombine drops the add and keeps the freeze,
; which is right in LLVM. The model stops at a frozen poison, on both sides, so the two are equal there, and that
; says nothing about LLVM.
define i8 @f(i8 %x) {
  %a = freeze i8 %x
  %r = add i8 %a, 0
  ret i8 %r
}
