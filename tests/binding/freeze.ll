; tests/binding.py's input for `freeze` in the model: instcombine drops the add and keeps the freeze, which is right in
; LLVM. For x of 8 or more the shift is poison, and both sides freeze it to the value the run chooses, the same one
; through the same place, so the target refines the source. Until F3 the model stopped there, on both sides, so the
; two were equal and no claim held.
define i8 @f(i8 noundef %x) {
  %y = shl i8 1, %x
  %a = freeze i8 %y
  %r = add i8 %a, 0
  ret i8 %r
}
