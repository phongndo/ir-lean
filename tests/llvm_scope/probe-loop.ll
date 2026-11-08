; A loop over memory, a call, a switch and a select, to show more of each target's codegen pipeline than an empty
; function does. tests/llvm_scope.py reads it. Passes that only run for some CPU, feature or construct still won't
; show, so what llc lists for this is a lower bound.
define internal i32 @g(i32 %x) {
  %y = mul i32 %x, 3
  ret i32 %y
}

define i32 @f(ptr %p, i32 %n, i32 %k) {
entry:
  %empty = icmp sle i32 %n, 0
  br i1 %empty, label %exit, label %loop

loop:
  %i = phi i32 [ 0, %entry ], [ %next, %latch ]
  %acc = phi i32 [ 0, %entry ], [ %sum, %latch ]
  %slot = getelementptr inbounds i32, ptr %p, i32 %i
  %v = load i32, ptr %slot, align 4
  switch i32 %k, label %other [
    i32 0, label %zero
    i32 1, label %one
  ]

zero:
  %a = call i32 @g(i32 %v)
  br label %latch

one:
  %b = shl i32 %v, 2
  br label %latch

other:
  %c = add i32 %v, %k
  br label %latch

latch:
  %t = phi i32 [ %a, %zero ], [ %b, %one ], [ %c, %other ]
  %neg = icmp slt i32 %t, 0
  %abs = select i1 %neg, i32 0, i32 %t
  store i32 %abs, ptr %slot, align 4
  %sum = add i32 %acc, %abs
  %next = add nuw nsw i32 %i, 1
  %done = icmp eq i32 %next, %n
  br i1 %done, label %exit, label %loop

exit:
  %r = phi i32 [ 0, %entry ], [ %sum, %latch ]
  ret i32 %r
}
