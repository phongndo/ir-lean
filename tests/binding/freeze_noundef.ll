; tests/binding.py's input: instcombine drops a freeze of a noundef argument, which poison would have made undefined.
define i8 @f(i8 noundef %x) {
  %a = freeze i8 %x
  ret i8 %a
}
