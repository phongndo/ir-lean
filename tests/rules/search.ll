; tests/rules_test.py's input for the rule search: small functions written for it, each a case of what the search
; and certify mode do. docs/rule-search.md.
target triple = "x86_64-unknown-linux-gnu"

declare i32 @llvm.umax.i32(i32, i32)
declare i32 @llvm.umin.i32(i32, i32)

; One block, so the whole function is certified too: (x - y) + y, masked with -1 and or-ed with 0, is x.
define i32 @masked(i32 noundef %x, i32 noundef %y) {
  %d = sub i32 %x, %y
  %e = add i32 %d, %y
  %m = and i32 %e, -1
  %o = or i32 %m, 0
  ret i32 %o
}

; A loop that reads memory, so only the slice is certified: umin(umax(a, k), a) is a, and a ^ k ^ k is a.
define i32 @sum(ptr %p, i32 %n, i32 %k) {
entry:
  br label %loop

loop:
  %i = phi i32 [ 0, %entry ], [ %next, %loop ]
  %acc = phi i32 [ 0, %entry ], [ %acc.next, %loop ]
  %q = getelementptr inbounds i32, ptr %p, i32 %i
  %a = load i32, ptr %q, align 4
  %hi = call i32 @llvm.umax.i32(i32 %a, i32 %k)
  %lo = call i32 @llvm.umin.i32(i32 %hi, i32 %a)
  %t = xor i32 %lo, %k
  %u = xor i32 %t, %k
  %acc.next = add i32 %acc, %u
  %next = add nuw i32 %i, 1
  %done = icmp eq i32 %next, %n
  br i1 %done, label %exit, label %loop

exit:
  ret i32 %acc.next
}

; A side condition on a constant: 7 - (a ^ 7) without unsigned wrap is a, since 7 is a low mask.
define i8 @mask(i8 %a) {
  %x = xor i8 %a, 7
  %s = sub nuw i8 7, %x
  ret i8 %s
}

; The same with 6, which isn't a low mask: the rule's side condition fails, and nothing is found.
define i8 @notmask(i8 %a) {
  %x = xor i8 %a, 6
  %s = sub nuw i8 6, %x
  ret i8 %s
}

; Two widths: truncating a zero extension back.
define i16 @widths(i16 %a, i16 %b) {
  %z = zext i16 %a to i64
  %t = trunc i64 %z to i16
  %r = mul i16 %t, %b
  ret i16 %r
}

; One instruction read twice: both uses are rewritten by one step.
define i32 @twice(i32 %x) {
  %a = or i32 %x, 0
  %r = mul i32 %a, %a
  ret i32 %r
}

; Nothing to find.
define i32 @plain(i32 %x, i32 %y) {
  %r = mul i32 %x, %y
  ret i32 %r
}
