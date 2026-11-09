; Lane intrinsics against native code, on fixed-width vectors: `llvm.vector.reverse` and `llvm.stepvector`,
; which neither Alive2 nor LLVM's constant folder knows at the pin, and `llvm.vector.insert` and
; `llvm.vector.extract`. tests/scalablecheck.py ties their scalable forms to these.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare <4 x i32> @llvm.vector.reverse.v4i32(<4 x i32>)
declare <8 x i8> @llvm.stepvector.v8i8()
declare <264 x i8> @llvm.stepvector.v264i8()

; Lane `i` of four arguments, reversed.
define i32 @reverse_lane(i32 %a, i32 %b, i32 %c, i32 %d, i32 %i) {
  %v0 = insertelement <4 x i32> poison, i32 %a, i64 0
  %v1 = insertelement <4 x i32> %v0, i32 %b, i64 1
  %v2 = insertelement <4 x i32> %v1, i32 %c, i64 2
  %v3 = insertelement <4 x i32> %v2, i32 %d, i64 3
  %r = call <4 x i32> @llvm.vector.reverse.v4i32(<4 x i32> %v3)
  %k = and i32 %i, 3
  %x = extractelement <4 x i32> %r, i32 %k
  ret i32 %x
}

; Lane `i` of 0, 1, 2, ...
define i32 @stepvector_lane(i32 %i) {
  %s = call <8 x i8> @llvm.stepvector.v8i8()
  %k = and i32 %i, 7
  %x = extractelement <8 x i8> %s, i32 %k
  %r = zext i8 %x to i32
  ret i32 %r
}

; Past 255, a lane of i8 is truncated, as LangRef says: lane 260 is 4.
define i32 @stepvector_truncated(i32 %i) {
  %s = call <264 x i8> @llvm.stepvector.v264i8()
  %k = urem i32 %i, 264
  %x = extractelement <264 x i8> %s, i32 %k
  %r = zext i8 %x to i32
  ret i32 %r
}

declare <4 x i32> @llvm.vector.insert.v4i32.v2i32(<4 x i32>, <2 x i32>, i64)
declare <2 x i32> @llvm.vector.extract.v2i32.v4i32(<4 x i32>, i64)

; Lane `i` of four arguments with the last two replaced by two more.
define i32 @insert_lane(i32 %a, i32 %b, i32 %c, i32 %d, i32 %x, i32 %y, i32 %i) {
  %v0 = insertelement <4 x i32> poison, i32 %a, i64 0
  %v1 = insertelement <4 x i32> %v0, i32 %b, i64 1
  %v2 = insertelement <4 x i32> %v1, i32 %c, i64 2
  %v3 = insertelement <4 x i32> %v2, i32 %d, i64 3
  %s0 = insertelement <2 x i32> poison, i32 %x, i64 0
  %s1 = insertelement <2 x i32> %s0, i32 %y, i64 1
  %r = call <4 x i32> @llvm.vector.insert.v4i32.v2i32(<4 x i32> %v3, <2 x i32> %s1, i64 2)
  %k = and i32 %i, 3
  %e = extractelement <4 x i32> %r, i32 %k
  ret i32 %e
}

; Lane `i` of the last two of four arguments.
define i32 @extract_lane(i32 %a, i32 %b, i32 %c, i32 %d, i32 %i) {
  %v0 = insertelement <4 x i32> poison, i32 %a, i64 0
  %v1 = insertelement <4 x i32> %v0, i32 %b, i64 1
  %v2 = insertelement <4 x i32> %v1, i32 %c, i64 2
  %v3 = insertelement <4 x i32> %v2, i32 %d, i64 3
  %r = call <2 x i32> @llvm.vector.extract.v2i32.v4i32(<4 x i32> %v3, i64 2)
  %k = and i32 %i, 1
  %e = extractelement <2 x i32> %r, i32 %k
  ret i32 %e
}
