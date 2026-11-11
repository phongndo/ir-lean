; Functions over byte buffers that tests/prooftest_memory_test.py runs tier-1 proof tests on: a scalar reference and
; a vector version of the same thing, as a SIMD kernel and its C fallback are, and a vector version with one lane
; wrong, which an equivalence property has to refute. Each loads 4 bytes at a time with no alignment, then finishes
; byte by byte.

; Sums the bytes of p[0..n).
define i32 @sum_scalar(ptr %p, i64 %n) {
entry:
  %z = icmp eq i64 %n, 0
  br i1 %z, label %exit, label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %i2, %loop ]
  %s = phi i32 [ 0, %entry ], [ %s2, %loop ]
  %q = getelementptr inbounds i8, ptr %p, i64 %i
  %b = load i8, ptr %q, align 1
  %w = zext i8 %b to i32
  %s2 = add i32 %s, %w
  %i2 = add i64 %i, 1
  %d = icmp eq i64 %i2, %n
  br i1 %d, label %exit, label %loop

exit:
  %r = phi i32 [ 0, %entry ], [ %s2, %loop ]
  ret i32 %r
}

; The same, four lanes at a time.
define i32 @sum_vec(ptr %p, i64 %n) {
entry:
  br label %vhead

vhead:
  %i = phi i64 [ 0, %entry ], [ %i4, %vbody ]
  %acc = phi <4 x i32> [ zeroinitializer, %entry ], [ %acc2, %vbody ]
  %i4 = add i64 %i, 4
  %fits = icmp ule i64 %i4, %n
  br i1 %fits, label %vbody, label %reduce

vbody:
  %q = getelementptr inbounds i8, ptr %p, i64 %i
  %v = load <4 x i8>, ptr %q, align 1
  %w = zext <4 x i8> %v to <4 x i32>
  %acc2 = add <4 x i32> %acc, %w
  br label %vhead

reduce:
  %e0 = extractelement <4 x i32> %acc, i64 0
  %e1 = extractelement <4 x i32> %acc, i64 1
  %e2 = extractelement <4 x i32> %acc, i64 2
  %e3 = extractelement <4 x i32> %acc, i64 3
  %s01 = add i32 %e0, %e1
  %s23 = add i32 %e2, %e3
  %s = add i32 %s01, %s23
  br label %thead

thead:
  %j = phi i64 [ %i, %reduce ], [ %j2, %tbody ]
  %t = phi i32 [ %s, %reduce ], [ %t2, %tbody ]
  %more = icmp ult i64 %j, %n
  br i1 %more, label %tbody, label %done

tbody:
  %r = getelementptr inbounds i8, ptr %p, i64 %j
  %b = load i8, ptr %r, align 1
  %bw = zext i8 %b to i32
  %t2 = add i32 %t, %bw
  %j2 = add i64 %j, 1
  br label %thead

done:
  ret i32 %t
}

; sum_vec with lane 2 masked off: wrong whenever a byte the vector loop reads, at 2 modulo 4, isn't zero.
define i32 @sum_vec_bad(ptr %p, i64 %n) {
entry:
  br label %vhead

vhead:
  %i = phi i64 [ 0, %entry ], [ %i4, %vbody ]
  %acc = phi <4 x i32> [ zeroinitializer, %entry ], [ %acc2, %vbody ]
  %i4 = add i64 %i, 4
  %fits = icmp ule i64 %i4, %n
  br i1 %fits, label %vbody, label %reduce

vbody:
  %q = getelementptr inbounds i8, ptr %p, i64 %i
  %v = load <4 x i8>, ptr %q, align 1
  %w = zext <4 x i8> %v to <4 x i32>
  %wm = and <4 x i32> %w, <i32 -1, i32 -1, i32 0, i32 -1>
  %acc2 = add <4 x i32> %acc, %wm
  br label %vhead

reduce:
  %e0 = extractelement <4 x i32> %acc, i64 0
  %e1 = extractelement <4 x i32> %acc, i64 1
  %e2 = extractelement <4 x i32> %acc, i64 2
  %e3 = extractelement <4 x i32> %acc, i64 3
  %s01 = add i32 %e0, %e1
  %s23 = add i32 %e2, %e3
  %s = add i32 %s01, %s23
  br label %thead

thead:
  %j = phi i64 [ %i, %reduce ], [ %j2, %tbody ]
  %t = phi i32 [ %s, %reduce ], [ %t2, %tbody ]
  %more = icmp ult i64 %j, %n
  br i1 %more, label %tbody, label %done

tbody:
  %r = getelementptr inbounds i8, ptr %p, i64 %j
  %b = load i8, ptr %r, align 1
  %bw = zext i8 %b to i32
  %t2 = add i32 %t, %bw
  %j2 = add i64 %j, 1
  br label %thead

done:
  ret i32 %t
}

; XORs each byte of p[0..n) with k, in place.
define void @xor_scalar(ptr %p, i64 %n, i8 %k) {
entry:
  %z = icmp eq i64 %n, 0
  br i1 %z, label %exit, label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %i2, %loop ]
  %q = getelementptr inbounds i8, ptr %p, i64 %i
  %b = load i8, ptr %q, align 1
  %x = xor i8 %b, %k
  store i8 %x, ptr %q, align 1
  %i2 = add i64 %i, 1
  %d = icmp eq i64 %i2, %n
  br i1 %d, label %exit, label %loop

exit:
  ret void
}

; The same, four lanes at a time.
define void @xor_vec(ptr %p, i64 %n, i8 %k) {
entry:
  %k0 = insertelement <4 x i8> poison, i8 %k, i64 0
  %kv = shufflevector <4 x i8> %k0, <4 x i8> poison, <4 x i32> zeroinitializer
  br label %vhead

vhead:
  %i = phi i64 [ 0, %entry ], [ %i4, %vbody ]
  %i4 = add i64 %i, 4
  %fits = icmp ule i64 %i4, %n
  br i1 %fits, label %vbody, label %thead

vbody:
  %q = getelementptr inbounds i8, ptr %p, i64 %i
  %v = load <4 x i8>, ptr %q, align 1
  %x = xor <4 x i8> %v, %kv
  store <4 x i8> %x, ptr %q, align 1
  br label %vhead

thead:
  %j = phi i64 [ %i, %vhead ], [ %j2, %tbody ]
  %more = icmp ult i64 %j, %n
  br i1 %more, label %tbody, label %done

tbody:
  %r = getelementptr inbounds i8, ptr %p, i64 %j
  %b = load i8, ptr %r, align 1
  %bx = xor i8 %b, %k
  store i8 %bx, ptr %r, align 1
  %j2 = add i64 %j, 1
  br label %thead

done:
  ret void
}

; xor_vec storing lane 2's byte in lane 3 too: it returns what xor_vec does, and leaves different memory.
define void @xor_vec_bad(ptr %p, i64 %n, i8 %k) {
entry:
  %k0 = insertelement <4 x i8> poison, i8 %k, i64 0
  %kv = shufflevector <4 x i8> %k0, <4 x i8> poison, <4 x i32> zeroinitializer
  br label %vhead

vhead:
  %i = phi i64 [ 0, %entry ], [ %i4, %vbody ]
  %i4 = add i64 %i, 4
  %fits = icmp ule i64 %i4, %n
  br i1 %fits, label %vbody, label %thead

vbody:
  %q = getelementptr inbounds i8, ptr %p, i64 %i
  %v = load <4 x i8>, ptr %q, align 1
  %x = xor <4 x i8> %v, %kv
  %y = shufflevector <4 x i8> %x, <4 x i8> poison, <4 x i32> <i32 0, i32 1, i32 2, i32 2>
  store <4 x i8> %y, ptr %q, align 1
  br label %vhead

thead:
  %j = phi i64 [ %i, %vhead ], [ %j2, %tbody ]
  %more = icmp ult i64 %j, %n
  br i1 %more, label %tbody, label %done

tbody:
  %r = getelementptr inbounds i8, ptr %p, i64 %j
  %b = load i8, ptr %r, align 1
  %bx = xor i8 %b, %k
  store i8 %bx, ptr %r, align 1
  %j2 = add i64 %j, 1
  br label %thead

done:
  ret void
}

; Reads one byte past the end of what it's given: undefined when the buffer ends there, where sum_scalar isn't.
define i32 @sum_overread(ptr %p, i64 %n) {
entry:
  %s = call i32 @sum_scalar(ptr %p, i64 %n)
  %q = getelementptr inbounds i8, ptr %p, i64 %n
  %b = load i8, ptr %q, align 1
  %w = zext i8 %b to i32
  %m = and i32 %w, 0
  %r = add i32 %s, %m
  ret i32 %r
}
