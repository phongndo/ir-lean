; correct
; The cut lemma on a function with memory: the loop of tests/cut/q5_kernel.ll, loading each round's word of high bits
; through a pointer, as llama.cpp's q5_0 kernel does, and storing what it adds up through another. The body holds
; the instructions of tests/real/llama_q5_bitspread.ll's @src, word for word, and @tgt its replacement's.
; tests/cut/Q5KernelMemory.lean proves @tgt refines @src on every memory the model has an answer for, from the
; slice's own proof. docs/refinement.md.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define void @src(ptr %dst, ptr %qh, i32 %n) {
entry:
  br label %head

head:
  %i = phi i32 [ 0, %entry ], [ %i1, %body ]
  %acc = phi <32 x i8> [ zeroinitializer, %entry ], [ %acc1, %body ]
  %more = icmp ult i32 %i, %n
  br i1 %more, label %body, label %exit

body:
  %at = zext i32 %i to i64
  %word = getelementptr inbounds i32, ptr %qh, i64 %at
  %x = load i32, ptr %word, align 4
  %insert = insertelement <8 x i32> poison, i32 %x, i64 0
  %bytes = bitcast <8 x i32> %insert to <32 x i8>
  %shuffle = shufflevector <32 x i8> %bytes, <32 x i8> poison, <32 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 1, i32 1, i32 1, i32 1, i32 1, i32 1, i32 1, i32 1, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 3, i32 3, i32 3, i32 3, i32 3, i32 3, i32 3, i32 3>
  %or = or <32 x i8> %shuffle, <i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127, i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127, i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127, i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127>
  %mask = icmp eq <32 x i8> %or, splat (i8 -1)
  %out = select <32 x i1> %mask, <32 x i8> zeroinitializer, <32 x i8> splat (i8 -16)
  %acc1 = add <32 x i8> %acc, %out
  %i1 = add i32 %i, 1
  br label %head

exit:
  store <32 x i8> %acc, ptr %dst, align 1
  ret void
}

define void @tgt(ptr %dst, ptr %qh, i32 %n) {
entry:
  br label %head

head:
  %i = phi i32 [ 0, %entry ], [ %i1, %body ]
  %acc = phi <32 x i8> [ zeroinitializer, %entry ], [ %acc1, %body ]
  %more = icmp ult i32 %i, %n
  br i1 %more, label %body, label %exit

body:
  %at = zext i32 %i to i64
  %word = getelementptr inbounds i32, ptr %qh, i64 %at
  %x = load i32, ptr %word, align 4
  %mask = bitcast i32 %x to <32 x i1>
  %out = select <32 x i1> %mask, <32 x i8> zeroinitializer, <32 x i8> splat (i8 -16)
  %acc1 = add <32 x i8> %acc, %out
  %i1 = add i32 %i, 1
  br label %head

exit:
  store <32 x i8> %acc, ptr %dst, align 1
  ret void
}
