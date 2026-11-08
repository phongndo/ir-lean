; tests/binding.py's input: instcombine folds the add away.
define i8 @f(i8 noundef %x) {
  %r = add i8 %x, 0
  ret i8 %r
}
