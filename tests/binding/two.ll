; tests/binding.py's input where the pass changes a function the claim isn't about: g.
define i8 @f(i8 noundef %x) {
  %r = add i8 %x, 0
  ret i8 %r
}

define i8 @g(i8 %x) {
  %r = mul i8 %x, 1
  ret i8 %r
}
