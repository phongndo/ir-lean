; Removing a freeze of a noundef argument: right. A poison x is undefined behavior on entry to both.
define i8 @src(i8 noundef %x) {
  %r = freeze i8 %x
  ret i8 %r
}

define i8 @tgt(i8 noundef %x) {
  ret i8 %x
}
