; tests/binding.py's input with a promise outside the function: an intrinsic's declaration, which LLVM prints with
; willreturn. The function makes no promise, and instcombine folds the add away, as in add_zero.ll.
declare i32 @llvm.abs.i32(i32, i1 immarg)

define i8 @f(i8 noundef %x) {
  %r = add i8 %x, 0
  ret i8 %r
}
