; Functions tests/prooftest_test.py runs tier-1 proof tests on. Each is small, and each takes one path through
; tools/prooftest/prooftest.py.

; Keeps the low 16 bits, where a wrong spec says it returns its input: false first at 0x10000.
define i32 @low16(i32 %x) {
  %r = and i32 %x, 65535
  ret i32 %r
}

; Multiplies by 4, where its spec says by 2.
define i8 @times2(i8 %x) {
  %r = shl i8 %x, 2
  ret i8 %r
}

; Counts set bits in a loop, but steps two bits at a time: a bug. The kernel confirms it through runFuel.
define i32 @count(i32 %x) {
entry:
  %zero = icmp eq i32 %x, 0
  br i1 %zero, label %exit, label %loop

loop:
  %v = phi i32 [ %x, %entry ], [ %v2, %loop ]
  %c = phi i32 [ 0, %entry ], [ %c2, %loop ]
  %b = and i32 %v, 1
  %c2 = add i32 %c, %b
  %v2 = lshr i32 %v, 2
  %done = icmp eq i32 %v2, 0
  br i1 %done, label %exit, label %loop

exit:
  %r = phi i32 [ 0, %entry ], [ %c2, %loop ]
  ret i32 %r
}

; The same loop, under the promises clang leaves on it: `promised (run ...)` in the model, which the kernel follows too.
define i32 @count_promised(i32 %x) mustprogress willreturn {
entry:
  %zero = icmp eq i32 %x, 0
  br i1 %zero, label %exit, label %loop

loop:
  %v = phi i32 [ %x, %entry ], [ %v2, %loop ]
  %c = phi i32 [ 0, %entry ], [ %c2, %loop ]
  %b = and i32 %v, 1
  %c2 = add i32 %c, %b
  %v2 = lshr i32 %v, 2
  %done = icmp eq i32 %v2, 0
  br i1 %done, label %exit, label %loop

exit:
  %r = phi i32 [ 0, %entry ], [ %c2, %loop ]
  ret i32 %r
}

; Never returns, under a promise to progress, which makes that undefined. Running it can't show that.
define i8 @spin_promised(i8 %x) mustprogress {
entry:
  br label %loop

loop:
  br label %loop
}

; Returns its argument, which `noundef` makes undefined for poison.
define i8 @ident(i8 noundef %x) {
  ret i8 %x
}

; Calls a function that runs blocks of its own, which the kernel can't follow, so tools/verify.py confirms instead.
define i8 @inner(i8 %x) noinline {
  %r = add i8 %x, 1
  ret i8 %r
}

define i8 @outer(i8 %x) {
  %r = call i8 @inner(i8 %x)
  ret i8 %r
}

; Never returns.
define i8 @spin(i8 %x) {
entry:
  br label %loop

loop:
  br label %loop
}

; Reads memory, which tier 1 can't generate.
define i8 @load(ptr %p) {
  %r = load i8, ptr %p
  ret i8 %r
}

; Floating point, which the emitter refuses.
define float @fadd(float %x) {
  %r = fadd float %x, 1.0
  ret float %r
}
