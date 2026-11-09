; tests/binding.py's input: instcombine turns `freeze (freeze y)` into `freeze y`, since the outer freeze keeps the
; value the inner one gave. For x of 8 or more `y` is poison.
define i8 @f(i8 noundef %x) {
  %y = shl i8 1, %x
  %a = freeze i8 %y
  %b = freeze i8 %a
  ret i8 %b
}
