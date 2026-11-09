target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define <32 x i8> @src(i32 %x) {
entry:
  %insert = insertelement <8 x i32> poison, i32 %x, i64 0
  %bytes = bitcast <8 x i32> %insert to <32 x i8>
  %shuffle = shufflevector <32 x i8> %bytes, <32 x i8> poison, <32 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 1, i32 1, i32 1, i32 1, i32 1, i32 1, i32 1, i32 1, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 3, i32 3, i32 3, i32 3, i32 3, i32 3, i32 3, i32 3>
  %or = or <32 x i8> %shuffle, <i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127, i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127, i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127, i8 -2, i8 -3, i8 -5, i8 -9, i8 -17, i8 -33, i8 -65, i8 127>
  %mask = icmp eq <32 x i8> %or, splat (i8 -1)
  %out = select <32 x i1> %mask, <32 x i8> zeroinitializer, <32 x i8> splat (i8 -16)
  ret <32 x i8> %out
}

define <32 x i8> @tgt(i32 %x) {
entry:
  %mask = bitcast i32 %x to <32 x i1>
  %out = select <32 x i1> %mask, <32 x i8> zeroinitializer, <32 x i8> splat (i8 -16)
  ret <32 x i8> %out
}
