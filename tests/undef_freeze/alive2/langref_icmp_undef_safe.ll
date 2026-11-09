; correct
define i1 @src() {
  %e = icmp slt i8 undef, 4
  ret i1 %e
}
define i1 @tgt() {
  ret i1 undef
}
