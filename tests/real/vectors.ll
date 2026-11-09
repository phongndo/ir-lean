; Each vector operation, reachable from functions that only take integers so tests/differential.py can
; call them. The values go through memory, so the optimizer can't fold them away in the native build.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare <4 x i32> @llvm.usub.sat.v4i32(<4 x i32>, <4 x i32>)
declare <4 x i32> @llvm.umin.v4i32(<4 x i32>, <4 x i32>)

; Which lane of a vector built from four arguments comes out, through a stack slot.
define i32 @lanes(i32 %a, i32 %b, i32 %c, i32 %d, i32 %i) {
  %slot = alloca <4 x i32>, align 16
  %v0 = insertelement <4 x i32> poison, i32 %a, i64 0
  %v1 = insertelement <4 x i32> %v0, i32 %b, i64 1
  %v2 = insertelement <4 x i32> %v1, i32 %c, i64 2
  %v3 = insertelement <4 x i32> %v2, i32 %d, i64 3
  store <4 x i32> %v3, ptr %slot, align 16
  %l = load <4 x i32>, ptr %slot, align 16
  %k = and i32 %i, 3
  %r = extractelement <4 x i32> %l, i32 %k
  ret i32 %r
}

; Lanes go into memory in order, lowest address first.
define i32 @lane_order(i16 %a, i16 %b, i32 %which) {
  %slot = alloca <2 x i16>, align 4
  %v0 = insertelement <2 x i16> poison, i16 %a, i64 0
  %v1 = insertelement <2 x i16> %v0, i16 %b, i64 1
  store <2 x i16> %v1, ptr %slot, align 4
  %k = and i32 %which, 3
  %idx = zext i32 %k to i64
  %p = getelementptr inbounds i8, ptr %slot, i64 %idx
  %byte = load i8, ptr %p, align 1
  %r = zext i8 %byte to i32
  ret i32 %r
}

; A byte vector read back as one integer, and the other way around.
define i32 @bytes_as_int(i32 %x, i32 %which) {
  %slot = alloca i32, align 4
  store i32 %x, ptr %slot, align 4
  %v = load <4 x i8>, ptr %slot, align 1
  %k = and i32 %which, 3
  %r = extractelement <4 x i8> %v, i32 %k
  %z = zext i8 %r to i32
  ret i32 %z
}

define i32 @int_as_bytes(i8 %a, i8 %b, i8 %c, i8 %d) {
  %slot = alloca <4 x i8>, align 4
  %v0 = insertelement <4 x i8> poison, i8 %a, i64 0
  %v1 = insertelement <4 x i8> %v0, i8 %b, i64 1
  %v2 = insertelement <4 x i8> %v1, i8 %c, i64 2
  %v3 = insertelement <4 x i8> %v2, i8 %d, i64 3
  store <4 x i8> %v3, ptr %slot, align 4
  %r = load i32, ptr %slot, align 4
  ret i32 %r
}

; Integer bitcasts split and join lanes in little-endian order, including sub-byte lanes.
define i32 @bitcast_split(i32 %a, i32 %b, i32 %which) {
  %v0 = insertelement <2 x i32> poison, i32 %a, i64 0
  %v = insertelement <2 x i32> %v0, i32 %b, i64 1
  %bytes = bitcast <2 x i32> %v to <8 x i8>
  %k = and i32 %which, 7
  %byte = extractelement <8 x i8> %bytes, i32 %k
  %r = zext i8 %byte to i32
  ret i32 %r
}

define i32 @bitcast_join(i8 %a, i8 %b, i8 %c, i8 %d, i32 %which) {
  %v0 = insertelement <4 x i8> poison, i8 %a, i64 0
  %v1 = insertelement <4 x i8> %v0, i8 %b, i64 1
  %v2 = insertelement <4 x i8> %v1, i8 %c, i64 2
  %v = insertelement <4 x i8> %v2, i8 %d, i64 3
  %words = bitcast <4 x i8> %v to <2 x i16>
  %k = and i32 %which, 1
  %word = extractelement <2 x i16> %words, i32 %k
  %r = zext i16 %word to i32
  ret i32 %r
}

define i32 @bitcast_scalar_bits(i32 %a, i32 %which) {
  %bits = bitcast i32 %a to <32 x i1>
  %k = and i32 %which, 31
  %bit = extractelement <32 x i1> %bits, i32 %k
  %r = zext i1 %bit to i32
  ret i32 %r
}

define i32 @bitcast_bits_scalar(i32 %a) {
  %bits = bitcast i32 %a to <32 x i1>
  %flip = xor <32 x i1> %bits, <i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0, i1 1, i1 0>
  %r = bitcast <32 x i1> %flip to i32
  ret i32 %r
}

; Shuffles that take lanes from both operands, and a shorter and a longer result.
define i32 @shuffle_mixed(i32 %a, i32 %b, i32 %c, i32 %d) {
  %x0 = insertelement <2 x i32> poison, i32 %a, i64 0
  %x = insertelement <2 x i32> %x0, i32 %b, i64 1
  %y0 = insertelement <2 x i32> poison, i32 %c, i64 0
  %y = insertelement <2 x i32> %y0, i32 %d, i64 1
  %s = shufflevector <2 x i32> %x, <2 x i32> %y, <2 x i32> <i32 3, i32 0>
  %e0 = extractelement <2 x i32> %s, i64 0
  %e1 = extractelement <2 x i32> %s, i64 1
  %r = sub i32 %e0, %e1
  ret i32 %r
}

define i32 @shuffle_widen(i32 %a, i32 %b, i32 %i) {
  %x0 = insertelement <2 x i32> poison, i32 %a, i64 0
  %x = insertelement <2 x i32> %x0, i32 %b, i64 1
  %s = shufflevector <2 x i32> %x, <2 x i32> poison, <4 x i32> <i32 1, i32 0, i32 1, i32 1>
  %k = and i32 %i, 3
  %r = extractelement <4 x i32> %s, i32 %k
  ret i32 %r
}

define i32 @splat_sub(i32 %a, i32 %b, i32 %i) {
  %x = insertelement <4 x i32> poison, i32 %a, i64 0
  %s = shufflevector <4 x i32> %x, <4 x i32> poison, <4 x i32> zeroinitializer
  %y = sub <4 x i32> %s, <i32 1, i32 2, i32 3, i32 4>
  %z = add <4 x i32> %y, zeroinitializer
  %w = xor <4 x i32> %z, <i32 -1, i32 0, i32 -1, i32 0>
  %k = and i32 %i, 3
  %r = extractelement <4 x i32> %w, i32 %k
  %t = add i32 %r, %b
  ret i32 %t
}

define i32 @casts(i8 %a, i8 %b, i32 %i) {
  %x0 = insertelement <2 x i8> poison, i8 %a, i64 0
  %x = insertelement <2 x i8> %x0, i8 %b, i64 1
  %z = zext <2 x i8> %x to <2 x i32>
  %s = sext <2 x i8> %x to <2 x i32>
  %m = mul <2 x i32> %z, %s
  %t = trunc <2 x i32> %m to <2 x i16>
  %k = and i32 %i, 1
  %r = extractelement <2 x i16> %t, i32 %k
  %w = zext i16 %r to i32
  ret i32 %w
}

define i32 @saturating(i32 %a, i32 %b, i32 %i) {
  %x = insertelement <4 x i32> <i32 7, i32 1000, i32 0, i32 -1>, i32 %a, i64 2
  %y = insertelement <4 x i32> <i32 9, i32 1, i32 0, i32 -1>, i32 %b, i64 2
  %s = call <4 x i32> @llvm.usub.sat.v4i32(<4 x i32> %x, <4 x i32> %y)
  %u = call <4 x i32> @llvm.umin.v4i32(<4 x i32> %s, <4 x i32> %y)
  %k = and i32 %i, 3
  %r = extractelement <4 x i32> %u, i32 %k
  ret i32 %r
}

define i32 @compare_select(i32 %a, i32 %b, i32 %i) {
  %x = insertelement <4 x i32> <i32 5, i32 -5, i32 0, i32 9>, i32 %a, i64 2
  %y = insertelement <4 x i32> <i32 3, i32 3, i32 3, i32 3>, i32 %b, i64 3
  %c = icmp slt <4 x i32> %x, %y
  %s = select <4 x i1> %c, <4 x i32> %x, <4 x i32> %y
  %k = and i32 %i, 3
  %r = extractelement <4 x i32> %s, i32 %k
  ret i32 %r
}

define i32 @select_whole(i1 %c, i32 %a, i32 %b, i32 %i) {
  %x = insertelement <2 x i32> <i32 1, i32 2>, i32 %a, i64 0
  %y = insertelement <2 x i32> <i32 3, i32 4>, i32 %b, i64 1
  %s = select i1 %c, <2 x i32> %x, <2 x i32> %y
  %k = and i32 %i, 1
  %r = extractelement <2 x i32> %s, i32 %k
  ret i32 %r
}

; Unaligned vector access, through an offset into a byte array.
define i32 @unaligned(i32 %a, i32 %b, i32 %off) {
  %slot = alloca [16 x i8], align 16
  call void @llvm.memset.p0.i64(ptr %slot, i8 0, i64 16, i1 false)
  %v0 = insertelement <2 x i32> poison, i32 %a, i64 0
  %v1 = insertelement <2 x i32> %v0, i32 %b, i64 1
  %k = and i32 %off, 7
  %idx = zext i32 %k to i64
  %p = getelementptr inbounds i8, ptr %slot, i64 %idx
  store <2 x i32> %v1, ptr %p, align 1
  %r = load i32, ptr %slot, align 16
  ret i32 %r
}
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)

; Past the end of a vector gives poison, which skips the comparison, so check an index in range.
define i32 @insert_variable(i32 %a, i32 %i, i32 %j) {
  %ki = and i32 %i, 3
  %kj = and i32 %j, 3
  %v = insertelement <4 x i32> <i32 10, i32 20, i32 30, i32 40>, i32 %a, i32 %ki
  %r = extractelement <4 x i32> %v, i32 %kj
  ret i32 %r
}
