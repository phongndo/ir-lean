; tests/binding.py's input: instcombine replaces a frozen poison with 0, a value the source can choose.
define i8 @f(i8 noundef %x) {
  %a = freeze i8 poison
  ret i8 %a
}
