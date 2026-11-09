; incorrect
; alive2: unknown: Alive2 unrolls a loop a fixed number of times, and drops the runs that go on, which is every run here
; Dropping a call with effects before a loop that never ends: neither side finishes, and where the call never comes
; back, the source ends in it and the target runs forever.
declare void @use(i8)

define void @src(i8 %x) {
entry:
  call void @use(i8 %x)
  br label %loop
loop:
  br label %loop
}

define void @tgt(i8 %x) {
entry:
  br label %loop
loop:
  br label %loop
}
