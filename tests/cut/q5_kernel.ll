; correct
; The cut lemma's one use: a loop whose body holds llama.cpp's q5_0 bit-spreading slice, the instructions of
; tests/real/llama_q5_bitspread.ll's @src, word for word, and the same loop with the slice's replacement, @tgt's. It
; has the kernel's shape without its loads and its floating point: each round takes a word of high bits, spreads it to
; a byte a bit, joins the low nibbles, and adds the bytes up. tests/cut.sh checks the slices are the fixture's lines,
; and tests/cut/Q5Kernel.lean proves @tgt refines @src, from the slice's own proof. docs/refinement.md.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define <32 x i8> @src(i32 %qh, i32 %n, <32 x i8> %q) {
entry:
  br label %head

head:
  %i = phi i32 [ 0, %entry ], [ %i1, %body ]
  %acc = phi <32 x i8> [ zeroinitializer, %entry ], [ %acc1, %body ]
  %more = icmp ult i32 %i, %n
  br i1 %more, label %body, label %exit

body:
  %x = add i32 %qh, %i
  %insert = insertelement <8 x i32> poison, i32 %x, i64 0
  %bytes = bitcast <8 x i32> %insert to <32 x i8>
  %shuffle = shufflevector <32 x i8> %bytes, <32 x i8> poison, <32 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 1, i32 1, i32 1, i32 1, i32 1, i32 1, i32 1, i32 1, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 3, i32 3, i32 3, i32 3, i32 3, i32 3, i32 3, i32 3>
  %or = or <32 x i8> %shuffle, <i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127, i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127, i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127, i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127>
  %mask = icmp eq <32 x i8> %or, splat (i8 -1)
  %out = select <32 x i1> %mask, <32 x i8> zeroinitializer, <32 x i8> splat (i8 -16)
  %bx = or <32 x i8> %out, %q
  %acc1 = add <32 x i8> %acc, %bx
  %i1 = add i32 %i, 1
  br label %head

exit:
  ret <32 x i8> %acc
}

define <32 x i8> @tgt(i32 %qh, i32 %n, <32 x i8> %q) {
entry:
  br label %head

head:
  %i = phi i32 [ 0, %entry ], [ %i1, %body ]
  %acc = phi <32 x i8> [ zeroinitializer, %entry ], [ %acc1, %body ]
  %more = icmp ult i32 %i, %n
  br i1 %more, label %body, label %exit

body:
  %x = add i32 %qh, %i
  %mask = bitcast i32 %x to <32 x i1>
  %out = select <32 x i1> %mask, <32 x i8> zeroinitializer, <32 x i8> splat (i8 -16)
  %bx = or <32 x i8> %out, %q
  %acc1 = add <32 x i8> %acc, %bx
  %i1 = add i32 %i, 1
  br label %head

exit:
  ret <32 x i8> %acc
}
