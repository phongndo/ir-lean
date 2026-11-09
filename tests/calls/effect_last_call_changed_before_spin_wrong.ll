; incorrect
; alive2: correct: Alive2 unrolls a loop a fixed number of times, and drops the runs that go on, which is every run of the target, so it has none to refute
; A source that chooses between use(1) then spinning and use(2) then returning, for a target that does use(2) then
; spins. Watched for no calls, a source that spins is cut off at use(1) and the target at use(2), and watched for one,
; a source that returns does and the target spins.
declare void @use(i8) willreturn nounwind

define void @src() {
entry:
  %p = freeze i1 poison
  br i1 %p, label %first, label %second
first:
  call void @use(i8 1)
  br label %spin
spin:
  br label %spin
second:
  call void @use(i8 2)
  ret void
}

define void @tgt() {
entry:
  call void @use(i8 2)
  br label %spin
spin:
  br label %spin
}
