; x86's integer dot products and vector bitcasts, reachable from functions that only take integers, so
; tests/differential.py can run each against the processor. Building native code needs AVX-512 VNNI.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8>, <16 x i8>)
declare <16 x i16> @llvm.x86.avx2.pmadd.ub.sw(<32 x i8>, <32 x i8>)
declare <32 x i16> @llvm.x86.avx512.pmaddubs.w.512(<64 x i8>, <64 x i8>)
declare <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16>, <8 x i16>)
declare <8 x i32> @llvm.x86.avx2.pmadd.wd(<16 x i16>, <16 x i16>)
declare <16 x i32> @llvm.x86.avx512.pmaddw.d.512(<32 x i16>, <32 x i16>)
declare <4 x i32> @llvm.x86.avx512.vpdpbusd.128(<4 x i32>, <16 x i8>, <16 x i8>)
declare <8 x i32> @llvm.x86.avx512.vpdpbusd.256(<8 x i32>, <32 x i8>, <32 x i8>)
declare <16 x i32> @llvm.x86.avx512.vpdpbusd.512(<16 x i32>, <64 x i8>, <64 x i8>)

; Lane %i of PMADDUBSW on 128-bit vectors of bytes.
define i32 @pmaddubsw128(i64 %a0, i64 %a1, i64 %b0, i64 %b1, i32 %i) #0 {
  %a.v0 = insertelement <2 x i64> poison, i64 %a0, i64 0
  %a.v1 = insertelement <2 x i64> %a.v0, i64 %a1, i64 1
  %a = bitcast <2 x i64> %a.v1 to <16 x i8>
  %b.v0 = insertelement <2 x i64> poison, i64 %b0, i64 0
  %b.v1 = insertelement <2 x i64> %b.v0, i64 %b1, i64 1
  %b = bitcast <2 x i64> %b.v1 to <16 x i8>
  %p = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %a, <16 x i8> %b)
  %k = and i32 %i, 7
  %r = extractelement <8 x i16> %p, i32 %k
  %z = sext i16 %r to i32
  ret i32 %z
}

; PMADDUBSW with every byte of each operand the same, which saturates at the extremes.
define i32 @pmaddubsw128_splat(i8 %x, i8 %y, i32 %i) #0 {
  %a.i = insertelement <16 x i8> poison, i8 %x, i64 0
  %a = shufflevector <16 x i8> %a.i, <16 x i8> poison, <16 x i32> zeroinitializer
  %b.i = insertelement <16 x i8> poison, i8 %y, i64 0
  %b = shufflevector <16 x i8> %b.i, <16 x i8> poison, <16 x i32> zeroinitializer
  %p = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %a, <16 x i8> %b)
  %k = and i32 %i, 7
  %r = extractelement <8 x i16> %p, i32 %k
  %z = sext i16 %r to i32
  ret i32 %z
}

; Lane %i of PMADDWD on 128-bit vectors of 16-bit lanes.
define i32 @pmaddwd128(i64 %a0, i64 %a1, i64 %b0, i64 %b1, i32 %i) #0 {
  %a.v0 = insertelement <2 x i64> poison, i64 %a0, i64 0
  %a.v1 = insertelement <2 x i64> %a.v0, i64 %a1, i64 1
  %a = bitcast <2 x i64> %a.v1 to <8 x i16>
  %b.v0 = insertelement <2 x i64> poison, i64 %b0, i64 0
  %b.v1 = insertelement <2 x i64> %b.v0, i64 %b1, i64 1
  %b = bitcast <2 x i64> %b.v1 to <8 x i16>
  %p = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %a, <8 x i16> %b)
  %k = and i32 %i, 3
  %r = extractelement <4 x i32> %p, i32 %k
  ret i32 %r
}

; PMADDWD with every lane of each operand the same: -32768 four times is the one case that wraps.
define i32 @pmaddwd128_splat(i16 %x, i16 %y, i32 %i) #0 {
  %a.i = insertelement <8 x i16> poison, i16 %x, i64 0
  %a = shufflevector <8 x i16> %a.i, <8 x i16> poison, <8 x i32> zeroinitializer
  %b.i = insertelement <8 x i16> poison, i16 %y, i64 0
  %b = shufflevector <8 x i16> %b.i, <8 x i16> poison, <8 x i32> zeroinitializer
  %p = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %a, <8 x i16> %b)
  %k = and i32 %i, 3
  %r = extractelement <4 x i32> %p, i32 %k
  ret i32 %r
}

; Lane %i of VPDPBUSD on 128-bit vectors.
define i32 @vpdpbusd128(i64 %c0, i64 %c1, i64 %a0, i64 %a1, i64 %b0, i64 %b1, i32 %i) #0 {
  %c.v0 = insertelement <2 x i64> poison, i64 %c0, i64 0
  %c.v1 = insertelement <2 x i64> %c.v0, i64 %c1, i64 1
  %c = bitcast <2 x i64> %c.v1 to <4 x i32>
  %a.v0 = insertelement <2 x i64> poison, i64 %a0, i64 0
  %a.v1 = insertelement <2 x i64> %a.v0, i64 %a1, i64 1
  %a = bitcast <2 x i64> %a.v1 to <16 x i8>
  %b.v0 = insertelement <2 x i64> poison, i64 %b0, i64 0
  %b.v1 = insertelement <2 x i64> %b.v0, i64 %b1, i64 1
  %b = bitcast <2 x i64> %b.v1 to <16 x i8>
  %p = call <4 x i32> @llvm.x86.avx512.vpdpbusd.128(<4 x i32> %c, <16 x i8> %a, <16 x i8> %b)
  %k = and i32 %i, 3
  %r = extractelement <4 x i32> %p, i32 %k
  ret i32 %r
}

; VPDPBUSD with every byte the same, and the accumulator, which wraps at the extremes.
define i32 @vpdpbusd128_splat(i32 %s, i8 %x, i8 %y, i32 %i) #0 {
  %c.i = insertelement <4 x i32> poison, i32 %s, i64 0
  %c = shufflevector <4 x i32> %c.i, <4 x i32> poison, <4 x i32> zeroinitializer
  %a.i = insertelement <16 x i8> poison, i8 %x, i64 0
  %a = shufflevector <16 x i8> %a.i, <16 x i8> poison, <16 x i32> zeroinitializer
  %b.i = insertelement <16 x i8> poison, i8 %y, i64 0
  %b = shufflevector <16 x i8> %b.i, <16 x i8> poison, <16 x i32> zeroinitializer
  %p = call <4 x i32> @llvm.x86.avx512.vpdpbusd.128(<4 x i32> %c, <16 x i8> %a, <16 x i8> %b)
  %k = and i32 %i, 3
  %r = extractelement <4 x i32> %p, i32 %k
  ret i32 %r
}

; Lane %i of PMADDUBSW on 256-bit vectors of bytes.
define i32 @pmaddubsw256(i64 %a0, i64 %a1, i64 %a2, i64 %a3, i64 %b0, i64 %b1, i64 %b2, i64 %b3, i32 %i) #0 {
  %a.v0 = insertelement <4 x i64> poison, i64 %a0, i64 0
  %a.v1 = insertelement <4 x i64> %a.v0, i64 %a1, i64 1
  %a.v2 = insertelement <4 x i64> %a.v1, i64 %a2, i64 2
  %a.v3 = insertelement <4 x i64> %a.v2, i64 %a3, i64 3
  %a = bitcast <4 x i64> %a.v3 to <32 x i8>
  %b.v0 = insertelement <4 x i64> poison, i64 %b0, i64 0
  %b.v1 = insertelement <4 x i64> %b.v0, i64 %b1, i64 1
  %b.v2 = insertelement <4 x i64> %b.v1, i64 %b2, i64 2
  %b.v3 = insertelement <4 x i64> %b.v2, i64 %b3, i64 3
  %b = bitcast <4 x i64> %b.v3 to <32 x i8>
  %p = call <16 x i16> @llvm.x86.avx2.pmadd.ub.sw(<32 x i8> %a, <32 x i8> %b)
  %k = and i32 %i, 15
  %r = extractelement <16 x i16> %p, i32 %k
  %z = sext i16 %r to i32
  ret i32 %z
}

; PMADDUBSW with every byte of each operand the same, which saturates at the extremes.
define i32 @pmaddubsw256_splat(i8 %x, i8 %y, i32 %i) #0 {
  %a.i = insertelement <32 x i8> poison, i8 %x, i64 0
  %a = shufflevector <32 x i8> %a.i, <32 x i8> poison, <32 x i32> zeroinitializer
  %b.i = insertelement <32 x i8> poison, i8 %y, i64 0
  %b = shufflevector <32 x i8> %b.i, <32 x i8> poison, <32 x i32> zeroinitializer
  %p = call <16 x i16> @llvm.x86.avx2.pmadd.ub.sw(<32 x i8> %a, <32 x i8> %b)
  %k = and i32 %i, 15
  %r = extractelement <16 x i16> %p, i32 %k
  %z = sext i16 %r to i32
  ret i32 %z
}

; Lane %i of PMADDWD on 256-bit vectors of 16-bit lanes.
define i32 @pmaddwd256(i64 %a0, i64 %a1, i64 %a2, i64 %a3, i64 %b0, i64 %b1, i64 %b2, i64 %b3, i32 %i) #0 {
  %a.v0 = insertelement <4 x i64> poison, i64 %a0, i64 0
  %a.v1 = insertelement <4 x i64> %a.v0, i64 %a1, i64 1
  %a.v2 = insertelement <4 x i64> %a.v1, i64 %a2, i64 2
  %a.v3 = insertelement <4 x i64> %a.v2, i64 %a3, i64 3
  %a = bitcast <4 x i64> %a.v3 to <16 x i16>
  %b.v0 = insertelement <4 x i64> poison, i64 %b0, i64 0
  %b.v1 = insertelement <4 x i64> %b.v0, i64 %b1, i64 1
  %b.v2 = insertelement <4 x i64> %b.v1, i64 %b2, i64 2
  %b.v3 = insertelement <4 x i64> %b.v2, i64 %b3, i64 3
  %b = bitcast <4 x i64> %b.v3 to <16 x i16>
  %p = call <8 x i32> @llvm.x86.avx2.pmadd.wd(<16 x i16> %a, <16 x i16> %b)
  %k = and i32 %i, 7
  %r = extractelement <8 x i32> %p, i32 %k
  ret i32 %r
}

; PMADDWD with every lane of each operand the same: -32768 four times is the one case that wraps.
define i32 @pmaddwd256_splat(i16 %x, i16 %y, i32 %i) #0 {
  %a.i = insertelement <16 x i16> poison, i16 %x, i64 0
  %a = shufflevector <16 x i16> %a.i, <16 x i16> poison, <16 x i32> zeroinitializer
  %b.i = insertelement <16 x i16> poison, i16 %y, i64 0
  %b = shufflevector <16 x i16> %b.i, <16 x i16> poison, <16 x i32> zeroinitializer
  %p = call <8 x i32> @llvm.x86.avx2.pmadd.wd(<16 x i16> %a, <16 x i16> %b)
  %k = and i32 %i, 7
  %r = extractelement <8 x i32> %p, i32 %k
  ret i32 %r
}

; Lane %i of VPDPBUSD on 256-bit vectors.
define i32 @vpdpbusd256(i64 %c0, i64 %c1, i64 %c2, i64 %c3, i64 %a0, i64 %a1, i64 %a2, i64 %a3, i64 %b0, i64 %b1, i64 %b2, i64 %b3, i32 %i) #0 {
  %c.v0 = insertelement <4 x i64> poison, i64 %c0, i64 0
  %c.v1 = insertelement <4 x i64> %c.v0, i64 %c1, i64 1
  %c.v2 = insertelement <4 x i64> %c.v1, i64 %c2, i64 2
  %c.v3 = insertelement <4 x i64> %c.v2, i64 %c3, i64 3
  %c = bitcast <4 x i64> %c.v3 to <8 x i32>
  %a.v0 = insertelement <4 x i64> poison, i64 %a0, i64 0
  %a.v1 = insertelement <4 x i64> %a.v0, i64 %a1, i64 1
  %a.v2 = insertelement <4 x i64> %a.v1, i64 %a2, i64 2
  %a.v3 = insertelement <4 x i64> %a.v2, i64 %a3, i64 3
  %a = bitcast <4 x i64> %a.v3 to <32 x i8>
  %b.v0 = insertelement <4 x i64> poison, i64 %b0, i64 0
  %b.v1 = insertelement <4 x i64> %b.v0, i64 %b1, i64 1
  %b.v2 = insertelement <4 x i64> %b.v1, i64 %b2, i64 2
  %b.v3 = insertelement <4 x i64> %b.v2, i64 %b3, i64 3
  %b = bitcast <4 x i64> %b.v3 to <32 x i8>
  %p = call <8 x i32> @llvm.x86.avx512.vpdpbusd.256(<8 x i32> %c, <32 x i8> %a, <32 x i8> %b)
  %k = and i32 %i, 7
  %r = extractelement <8 x i32> %p, i32 %k
  ret i32 %r
}

; VPDPBUSD with every byte the same, and the accumulator, which wraps at the extremes.
define i32 @vpdpbusd256_splat(i32 %s, i8 %x, i8 %y, i32 %i) #0 {
  %c.i = insertelement <8 x i32> poison, i32 %s, i64 0
  %c = shufflevector <8 x i32> %c.i, <8 x i32> poison, <8 x i32> zeroinitializer
  %a.i = insertelement <32 x i8> poison, i8 %x, i64 0
  %a = shufflevector <32 x i8> %a.i, <32 x i8> poison, <32 x i32> zeroinitializer
  %b.i = insertelement <32 x i8> poison, i8 %y, i64 0
  %b = shufflevector <32 x i8> %b.i, <32 x i8> poison, <32 x i32> zeroinitializer
  %p = call <8 x i32> @llvm.x86.avx512.vpdpbusd.256(<8 x i32> %c, <32 x i8> %a, <32 x i8> %b)
  %k = and i32 %i, 7
  %r = extractelement <8 x i32> %p, i32 %k
  ret i32 %r
}

; Lane %i of PMADDUBSW on 512-bit vectors of bytes.
define i32 @pmaddubsw512(i64 %a0, i64 %a1, i64 %a2, i64 %a3, i64 %a4, i64 %a5, i64 %a6, i64 %a7, i64 %b0, i64 %b1, i64 %b2, i64 %b3, i64 %b4, i64 %b5, i64 %b6, i64 %b7, i32 %i) #0 {
  %a.v0 = insertelement <8 x i64> poison, i64 %a0, i64 0
  %a.v1 = insertelement <8 x i64> %a.v0, i64 %a1, i64 1
  %a.v2 = insertelement <8 x i64> %a.v1, i64 %a2, i64 2
  %a.v3 = insertelement <8 x i64> %a.v2, i64 %a3, i64 3
  %a.v4 = insertelement <8 x i64> %a.v3, i64 %a4, i64 4
  %a.v5 = insertelement <8 x i64> %a.v4, i64 %a5, i64 5
  %a.v6 = insertelement <8 x i64> %a.v5, i64 %a6, i64 6
  %a.v7 = insertelement <8 x i64> %a.v6, i64 %a7, i64 7
  %a = bitcast <8 x i64> %a.v7 to <64 x i8>
  %b.v0 = insertelement <8 x i64> poison, i64 %b0, i64 0
  %b.v1 = insertelement <8 x i64> %b.v0, i64 %b1, i64 1
  %b.v2 = insertelement <8 x i64> %b.v1, i64 %b2, i64 2
  %b.v3 = insertelement <8 x i64> %b.v2, i64 %b3, i64 3
  %b.v4 = insertelement <8 x i64> %b.v3, i64 %b4, i64 4
  %b.v5 = insertelement <8 x i64> %b.v4, i64 %b5, i64 5
  %b.v6 = insertelement <8 x i64> %b.v5, i64 %b6, i64 6
  %b.v7 = insertelement <8 x i64> %b.v6, i64 %b7, i64 7
  %b = bitcast <8 x i64> %b.v7 to <64 x i8>
  %p = call <32 x i16> @llvm.x86.avx512.pmaddubs.w.512(<64 x i8> %a, <64 x i8> %b)
  %k = and i32 %i, 31
  %r = extractelement <32 x i16> %p, i32 %k
  %z = sext i16 %r to i32
  ret i32 %z
}

; PMADDUBSW with every byte of each operand the same, which saturates at the extremes.
define i32 @pmaddubsw512_splat(i8 %x, i8 %y, i32 %i) #0 {
  %a.i = insertelement <64 x i8> poison, i8 %x, i64 0
  %a = shufflevector <64 x i8> %a.i, <64 x i8> poison, <64 x i32> zeroinitializer
  %b.i = insertelement <64 x i8> poison, i8 %y, i64 0
  %b = shufflevector <64 x i8> %b.i, <64 x i8> poison, <64 x i32> zeroinitializer
  %p = call <32 x i16> @llvm.x86.avx512.pmaddubs.w.512(<64 x i8> %a, <64 x i8> %b)
  %k = and i32 %i, 31
  %r = extractelement <32 x i16> %p, i32 %k
  %z = sext i16 %r to i32
  ret i32 %z
}

; Lane %i of PMADDWD on 512-bit vectors of 16-bit lanes.
define i32 @pmaddwd512(i64 %a0, i64 %a1, i64 %a2, i64 %a3, i64 %a4, i64 %a5, i64 %a6, i64 %a7, i64 %b0, i64 %b1, i64 %b2, i64 %b3, i64 %b4, i64 %b5, i64 %b6, i64 %b7, i32 %i) #0 {
  %a.v0 = insertelement <8 x i64> poison, i64 %a0, i64 0
  %a.v1 = insertelement <8 x i64> %a.v0, i64 %a1, i64 1
  %a.v2 = insertelement <8 x i64> %a.v1, i64 %a2, i64 2
  %a.v3 = insertelement <8 x i64> %a.v2, i64 %a3, i64 3
  %a.v4 = insertelement <8 x i64> %a.v3, i64 %a4, i64 4
  %a.v5 = insertelement <8 x i64> %a.v4, i64 %a5, i64 5
  %a.v6 = insertelement <8 x i64> %a.v5, i64 %a6, i64 6
  %a.v7 = insertelement <8 x i64> %a.v6, i64 %a7, i64 7
  %a = bitcast <8 x i64> %a.v7 to <32 x i16>
  %b.v0 = insertelement <8 x i64> poison, i64 %b0, i64 0
  %b.v1 = insertelement <8 x i64> %b.v0, i64 %b1, i64 1
  %b.v2 = insertelement <8 x i64> %b.v1, i64 %b2, i64 2
  %b.v3 = insertelement <8 x i64> %b.v2, i64 %b3, i64 3
  %b.v4 = insertelement <8 x i64> %b.v3, i64 %b4, i64 4
  %b.v5 = insertelement <8 x i64> %b.v4, i64 %b5, i64 5
  %b.v6 = insertelement <8 x i64> %b.v5, i64 %b6, i64 6
  %b.v7 = insertelement <8 x i64> %b.v6, i64 %b7, i64 7
  %b = bitcast <8 x i64> %b.v7 to <32 x i16>
  %p = call <16 x i32> @llvm.x86.avx512.pmaddw.d.512(<32 x i16> %a, <32 x i16> %b)
  %k = and i32 %i, 15
  %r = extractelement <16 x i32> %p, i32 %k
  ret i32 %r
}

; PMADDWD with every lane of each operand the same: -32768 four times is the one case that wraps.
define i32 @pmaddwd512_splat(i16 %x, i16 %y, i32 %i) #0 {
  %a.i = insertelement <32 x i16> poison, i16 %x, i64 0
  %a = shufflevector <32 x i16> %a.i, <32 x i16> poison, <32 x i32> zeroinitializer
  %b.i = insertelement <32 x i16> poison, i16 %y, i64 0
  %b = shufflevector <32 x i16> %b.i, <32 x i16> poison, <32 x i32> zeroinitializer
  %p = call <16 x i32> @llvm.x86.avx512.pmaddw.d.512(<32 x i16> %a, <32 x i16> %b)
  %k = and i32 %i, 15
  %r = extractelement <16 x i32> %p, i32 %k
  ret i32 %r
}

; Lane %i of VPDPBUSD on 512-bit vectors.
define i32 @vpdpbusd512(i64 %c0, i64 %c1, i64 %c2, i64 %c3, i64 %c4, i64 %c5, i64 %c6, i64 %c7, i64 %a0, i64 %a1, i64 %a2, i64 %a3, i64 %a4, i64 %a5, i64 %a6, i64 %a7, i64 %b0, i64 %b1, i64 %b2, i64 %b3, i64 %b4, i64 %b5, i64 %b6, i64 %b7, i32 %i) #0 {
  %c.v0 = insertelement <8 x i64> poison, i64 %c0, i64 0
  %c.v1 = insertelement <8 x i64> %c.v0, i64 %c1, i64 1
  %c.v2 = insertelement <8 x i64> %c.v1, i64 %c2, i64 2
  %c.v3 = insertelement <8 x i64> %c.v2, i64 %c3, i64 3
  %c.v4 = insertelement <8 x i64> %c.v3, i64 %c4, i64 4
  %c.v5 = insertelement <8 x i64> %c.v4, i64 %c5, i64 5
  %c.v6 = insertelement <8 x i64> %c.v5, i64 %c6, i64 6
  %c.v7 = insertelement <8 x i64> %c.v6, i64 %c7, i64 7
  %c = bitcast <8 x i64> %c.v7 to <16 x i32>
  %a.v0 = insertelement <8 x i64> poison, i64 %a0, i64 0
  %a.v1 = insertelement <8 x i64> %a.v0, i64 %a1, i64 1
  %a.v2 = insertelement <8 x i64> %a.v1, i64 %a2, i64 2
  %a.v3 = insertelement <8 x i64> %a.v2, i64 %a3, i64 3
  %a.v4 = insertelement <8 x i64> %a.v3, i64 %a4, i64 4
  %a.v5 = insertelement <8 x i64> %a.v4, i64 %a5, i64 5
  %a.v6 = insertelement <8 x i64> %a.v5, i64 %a6, i64 6
  %a.v7 = insertelement <8 x i64> %a.v6, i64 %a7, i64 7
  %a = bitcast <8 x i64> %a.v7 to <64 x i8>
  %b.v0 = insertelement <8 x i64> poison, i64 %b0, i64 0
  %b.v1 = insertelement <8 x i64> %b.v0, i64 %b1, i64 1
  %b.v2 = insertelement <8 x i64> %b.v1, i64 %b2, i64 2
  %b.v3 = insertelement <8 x i64> %b.v2, i64 %b3, i64 3
  %b.v4 = insertelement <8 x i64> %b.v3, i64 %b4, i64 4
  %b.v5 = insertelement <8 x i64> %b.v4, i64 %b5, i64 5
  %b.v6 = insertelement <8 x i64> %b.v5, i64 %b6, i64 6
  %b.v7 = insertelement <8 x i64> %b.v6, i64 %b7, i64 7
  %b = bitcast <8 x i64> %b.v7 to <64 x i8>
  %p = call <16 x i32> @llvm.x86.avx512.vpdpbusd.512(<16 x i32> %c, <64 x i8> %a, <64 x i8> %b)
  %k = and i32 %i, 15
  %r = extractelement <16 x i32> %p, i32 %k
  ret i32 %r
}

; VPDPBUSD with every byte the same, and the accumulator, which wraps at the extremes.
define i32 @vpdpbusd512_splat(i32 %s, i8 %x, i8 %y, i32 %i) #0 {
  %c.i = insertelement <16 x i32> poison, i32 %s, i64 0
  %c = shufflevector <16 x i32> %c.i, <16 x i32> poison, <16 x i32> zeroinitializer
  %a.i = insertelement <64 x i8> poison, i8 %x, i64 0
  %a = shufflevector <64 x i8> %a.i, <64 x i8> poison, <64 x i32> zeroinitializer
  %b.i = insertelement <64 x i8> poison, i8 %y, i64 0
  %b = shufflevector <64 x i8> %b.i, <64 x i8> poison, <64 x i32> zeroinitializer
  %p = call <16 x i32> @llvm.x86.avx512.vpdpbusd.512(<16 x i32> %c, <64 x i8> %a, <64 x i8> %b)
  %k = and i32 %i, 15
  %r = extractelement <16 x i32> %p, i32 %k
  ret i32 %r
}

; Eight bytes joined into two 32-bit lanes, and four 16-bit lanes into one 64-bit lane.
define i32 @join_bytes(i8 %b0, i8 %b1, i8 %b2, i8 %b3, i8 %b4, i8 %b5, i8 %b6, i8 %b7, i32 %i) #0 {
  %v0 = insertelement <8 x i8> poison, i8 %b0, i64 0
  %v1 = insertelement <8 x i8> %v0, i8 %b1, i64 1
  %v2 = insertelement <8 x i8> %v1, i8 %b2, i64 2
  %v3 = insertelement <8 x i8> %v2, i8 %b3, i64 3
  %v4 = insertelement <8 x i8> %v3, i8 %b4, i64 4
  %v5 = insertelement <8 x i8> %v4, i8 %b5, i64 5
  %v6 = insertelement <8 x i8> %v5, i8 %b6, i64 6
  %v7 = insertelement <8 x i8> %v6, i8 %b7, i64 7
  %w = bitcast <8 x i8> %v7 to <2 x i32>
  %k = and i32 %i, 1
  %r = extractelement <2 x i32> %w, i32 %k
  ret i32 %r
}

define i64 @join_halves(i16 %h0, i16 %h1, i16 %h2, i16 %h3) #0 {
  %v0 = insertelement <4 x i16> poison, i16 %h0, i64 0
  %v1 = insertelement <4 x i16> %v0, i16 %h1, i64 1
  %v2 = insertelement <4 x i16> %v1, i16 %h2, i64 2
  %v3 = insertelement <4 x i16> %v2, i16 %h3, i64 3
  %w = bitcast <4 x i16> %v3 to <1 x i64>
  %r = extractelement <1 x i64> %w, i32 0
  ret i64 %r
}

; Lane %i of a 64-bit lane split into bytes, and of 32-bit lanes split into 16-bit ones.
define i32 @split_bytes(i64 %x, i64 %y, i32 %i) #0 {
  %v0 = insertelement <2 x i64> poison, i64 %x, i64 0
  %v1 = insertelement <2 x i64> %v0, i64 %y, i64 1
  %w = bitcast <2 x i64> %v1 to <16 x i8>
  %k = and i32 %i, 15
  %r = extractelement <16 x i8> %w, i32 %k
  %z = zext i8 %r to i32
  ret i32 %z
}

define i32 @split_halves(i32 %x, i32 %y, i32 %i) #0 {
  %v0 = insertelement <2 x i32> poison, i32 %x, i64 0
  %v1 = insertelement <2 x i32> %v0, i32 %y, i64 1
  %w = bitcast <2 x i32> %v1 to <4 x i16>
  %k = and i32 %i, 3
  %r = extractelement <4 x i16> %w, i32 %k
  %z = zext i16 %r to i32
  ret i32 %z
}

attributes #0 = { "target-features"="+avx2,+avx512f,+avx512bw,+avx512vl,+avx512vnni,+ssse3,+sse2" }
