; incorrect
; alive2: correct: Alive2 unrolls a loop a fixed number of times, and drops the runs that go on, which is every run of the target, so it has none to refute
; A source that chooses between spinning silently and calling @use then returning, for a target that calls @use then
; spins. Every prefix of the target's trace is one of some source run's, but no one source run does what the target
; does: watched for no calls, the target is cut off and the spinning source isn't, and watched for one, the target
; spins and the calling source returns.
declare void @use(i8)

define void @src(i8 %x) {
entry:
  %p = freeze i1 poison
  br i1 %p, label %spin, label %call
spin:
  br label %spin
call:
  call void @use(i8 %x)
  ret void
}

define void @tgt(i8 %x) {
entry:
  call void @use(i8 %x)
  br label %spin
spin:
  br label %spin
}
