; The hand-written probes tests/ir_features.py runs the emitter on, one for each item they name. This isn't one
; module: each `; probe: KIND / NAME` line starts a module of its own, whose function `@probe` uses the item and as
; little else as it can. A `; or:` line starts another version of the same probe, tried when LLVM's verifier
; rejects the one before. Probes for attributes, calling conventions and most metadata are built from templates in
; tests/ir_features.py, and those for intrinsics by build/ir-lean-probe, from src/Probe.cpp.

; probe: instruction / Ret
define i32 @probe(i32 %a) {
  ret i32 %a
}

; probe: instruction / UncondBr
define i32 @probe(i32 %a) {
  br label %b
b:
  ret i32 %a
}

; probe: instruction / CondBr
define i32 @probe(i1 %c, i32 %a) {
  br i1 %c, label %t, label %f
t:
  ret i32 %a
f:
  ret i32 0
}

; probe: instruction / Switch
define i32 @probe(i32 %a) {
  switch i32 %a, label %d [
    i32 0, label %z
  ]
z:
  ret i32 1
d:
  ret i32 %a
}

; probe: instruction / IndirectBr
define i32 @probe() {
  indirectbr ptr blockaddress(@probe, %a), [label %a]
a:
  ret i32 0
}

; probe: instruction / Invoke
declare i32 @__gxx_personality_v0(...)
define void @callee() {
  ret void
}
define void @probe() personality ptr @__gxx_personality_v0 {
  invoke void @callee() to label %ok unwind label %lp
ok:
  ret void
lp:
  %x = landingpad { ptr, i32 } cleanup
  resume { ptr, i32 } %x
}

; probe: instruction / Resume
declare i32 @__gxx_personality_v0(...)
define void @callee() {
  ret void
}
define void @probe() personality ptr @__gxx_personality_v0 {
  invoke void @callee() to label %ok unwind label %lp
ok:
  ret void
lp:
  %x = landingpad { ptr, i32 } cleanup
  resume { ptr, i32 } %x
}

; probe: instruction / LandingPad
declare i32 @__gxx_personality_v0(...)
define void @callee() {
  ret void
}
define void @probe() personality ptr @__gxx_personality_v0 {
  invoke void @callee() to label %ok unwind label %lp
ok:
  ret void
lp:
  %x = landingpad { ptr, i32 } cleanup
  resume { ptr, i32 } %x
}

; probe: instruction / Unreachable
define void @probe() {
  unreachable
}

; probe: instruction / CleanupRet
declare i32 @__CxxFrameHandler3(...)
define void @callee() {
  ret void
}
define void @probe() personality ptr @__CxxFrameHandler3 {
entry:
  invoke void @callee() to label %exit unwind label %cl
cl:
  %c = cleanuppad within none []
  cleanupret from %c unwind to caller
exit:
  ret void
}

; probe: instruction / CleanupPad
declare i32 @__CxxFrameHandler3(...)
define void @callee() {
  ret void
}
define void @probe() personality ptr @__CxxFrameHandler3 {
entry:
  invoke void @callee() to label %exit unwind label %cl
cl:
  %c = cleanuppad within none []
  cleanupret from %c unwind to caller
exit:
  ret void
}

; probe: instruction / CatchRet
declare i32 @__CxxFrameHandler3(...)
define void @callee() {
  ret void
}
define void @probe() personality ptr @__CxxFrameHandler3 {
entry:
  invoke void @callee() to label %exit unwind label %cs
cs:
  %s = catchswitch within none [label %catch] unwind to caller
catch:
  %p = catchpad within %s [ptr null, i32 64, ptr null]
  catchret from %p to label %exit
exit:
  ret void
}

; probe: instruction / CatchSwitch
declare i32 @__CxxFrameHandler3(...)
define void @callee() {
  ret void
}
define void @probe() personality ptr @__CxxFrameHandler3 {
entry:
  invoke void @callee() to label %exit unwind label %cs
cs:
  %s = catchswitch within none [label %catch] unwind to caller
catch:
  %p = catchpad within %s [ptr null, i32 64, ptr null]
  catchret from %p to label %exit
exit:
  ret void
}

; probe: instruction / CatchPad
declare i32 @__CxxFrameHandler3(...)
define void @callee() {
  ret void
}
define void @probe() personality ptr @__CxxFrameHandler3 {
entry:
  invoke void @callee() to label %exit unwind label %cs
cs:
  %s = catchswitch within none [label %catch] unwind to caller
catch:
  %p = catchpad within %s [ptr null, i32 64, ptr null]
  catchret from %p to label %exit
exit:
  ret void
}

; probe: instruction / CallBr
define i32 @probe() {
  callbr void asm "", "!i"() to label %a [label %b]
a:
  ret i32 0
b:
  ret i32 1
}

; probe: instruction / FNeg
define float @probe(float %a) {
  %r = fneg float %a
  ret float %r
}

; probe: instruction / FAdd
define float @probe(float %a, float %b) {
  %r = fadd float %a, %b
  ret float %r
}

; probe: instruction / FSub
define float @probe(float %a, float %b) {
  %r = fsub float %a, %b
  ret float %r
}

; probe: instruction / FMul
define float @probe(float %a, float %b) {
  %r = fmul float %a, %b
  ret float %r
}

; probe: instruction / FDiv
define float @probe(float %a, float %b) {
  %r = fdiv float %a, %b
  ret float %r
}

; probe: instruction / FRem
define float @probe(float %a, float %b) {
  %r = frem float %a, %b
  ret float %r
}

; probe: instruction / Add
define i32 @probe(i32 %a, i32 %b) {
  %r = add i32 %a, %b
  ret i32 %r
}

; probe: instruction / Sub
define i32 @probe(i32 %a, i32 %b) {
  %r = sub i32 %a, %b
  ret i32 %r
}

; probe: instruction / Mul
define i32 @probe(i32 %a, i32 %b) {
  %r = mul i32 %a, %b
  ret i32 %r
}

; probe: instruction / UDiv
define i32 @probe(i32 %a, i32 %b) {
  %r = udiv i32 %a, %b
  ret i32 %r
}

; probe: instruction / SDiv
define i32 @probe(i32 %a, i32 %b) {
  %r = sdiv i32 %a, %b
  ret i32 %r
}

; probe: instruction / URem
define i32 @probe(i32 %a, i32 %b) {
  %r = urem i32 %a, %b
  ret i32 %r
}

; probe: instruction / SRem
define i32 @probe(i32 %a, i32 %b) {
  %r = srem i32 %a, %b
  ret i32 %r
}

; probe: instruction / Shl
define i32 @probe(i32 %a, i32 %b) {
  %r = shl i32 %a, %b
  ret i32 %r
}

; probe: instruction / LShr
define i32 @probe(i32 %a, i32 %b) {
  %r = lshr i32 %a, %b
  ret i32 %r
}

; probe: instruction / AShr
define i32 @probe(i32 %a, i32 %b) {
  %r = ashr i32 %a, %b
  ret i32 %r
}

; probe: instruction / And
define i32 @probe(i32 %a, i32 %b) {
  %r = and i32 %a, %b
  ret i32 %r
}

; probe: instruction / Or
define i32 @probe(i32 %a, i32 %b) {
  %r = or i32 %a, %b
  ret i32 %r
}

; probe: instruction / Xor
define i32 @probe(i32 %a, i32 %b) {
  %r = xor i32 %a, %b
  ret i32 %r
}

; probe: instruction / Alloca
define i32 @probe() {
  %p = alloca i32
  store i32 1, ptr %p
  %v = load i32, ptr %p
  ret i32 %v
}

; probe: instruction / Load
define i32 @probe(ptr %p) {
  %v = load i32, ptr %p
  ret i32 %v
}

; probe: instruction / Store
define void @probe(ptr %p, i32 %v) {
  store i32 %v, ptr %p
  ret void
}

; probe: instruction / GetElementPtr
define ptr @probe(ptr %p, i64 %i) {
  %q = getelementptr i32, ptr %p, i64 %i
  ret ptr %q
}

; probe: instruction / Fence
define void @probe() {
  fence seq_cst
  ret void
}

; probe: instruction / AtomicCmpXchg
define i32 @probe(ptr %p) {
  %r = cmpxchg ptr %p, i32 0, i32 1 seq_cst seq_cst
  %v = extractvalue { i32, i1 } %r, 0
  ret i32 %v
}

; probe: instruction / AtomicRMW
define i32 @probe(ptr %p) {
  %r = atomicrmw add ptr %p, i32 1 seq_cst
  ret i32 %r
}

; probe: instruction / Trunc
define i8 @probe(i32 %a) {
  %r = trunc i32 %a to i8
  ret i8 %r
}

; probe: instruction / ZExt
define i64 @probe(i32 %a) {
  %r = zext i32 %a to i64
  ret i64 %r
}

; probe: instruction / SExt
define i64 @probe(i32 %a) {
  %r = sext i32 %a to i64
  ret i64 %r
}

; probe: instruction / FPToUI
define i32 @probe(float %a) {
  %r = fptoui float %a to i32
  ret i32 %r
}

; probe: instruction / FPToSI
define i32 @probe(float %a) {
  %r = fptosi float %a to i32
  ret i32 %r
}

; probe: instruction / UIToFP
define float @probe(i32 %a) {
  %r = uitofp i32 %a to float
  ret float %r
}

; probe: instruction / SIToFP
define float @probe(i32 %a) {
  %r = sitofp i32 %a to float
  ret float %r
}

; probe: instruction / FPTrunc
define float @probe(double %a) {
  %r = fptrunc double %a to float
  ret float %r
}

; probe: instruction / FPExt
define double @probe(float %a) {
  %r = fpext float %a to double
  ret double %r
}

; probe: instruction / PtrToInt
define i64 @probe(ptr %p) {
  %r = ptrtoint ptr %p to i64
  ret i64 %r
}

; probe: instruction / PtrToAddr
define i64 @probe(ptr %p) {
  %r = ptrtoaddr ptr %p to i64
  ret i64 %r
}

; probe: instruction / IntToPtr
define ptr @probe(i64 %a) {
  %r = inttoptr i64 %a to ptr
  ret ptr %r
}

; probe: instruction / BitCast
define i64 @probe(<2 x i32> %a) {
  %r = bitcast <2 x i32> %a to i64
  ret i64 %r
}

; probe: instruction / AddrSpaceCast
define ptr addrspace(1) @probe(ptr %p) {
  %r = addrspacecast ptr %p to ptr addrspace(1)
  ret ptr addrspace(1) %r
}

; probe: instruction / ICmp
define i1 @probe(i32 %a, i32 %b) {
  %r = icmp slt i32 %a, %b
  ret i1 %r
}

; probe: instruction / FCmp
define i1 @probe(float %a, float %b) {
  %r = fcmp olt float %a, %b
  ret i1 %r
}

; probe: instruction / PHI
define i32 @probe(i1 %c, i32 %a) {
entry:
  br i1 %c, label %t, label %j
t:
  br label %j
j:
  %r = phi i32 [ %a, %entry ], [ 0, %t ]
  ret i32 %r
}

; probe: instruction / Call
define i32 @callee(i32 %a) {
  ret i32 %a
}
define i32 @probe(i32 %a) {
  %r = call i32 @callee(i32 %a)
  ret i32 %r
}

; probe: instruction / Select
define i32 @probe(i1 %c, i32 %a, i32 %b) {
  %r = select i1 %c, i32 %a, i32 %b
  ret i32 %r
}

; probe: instruction / VAArg
define i32 @probe(ptr %ap) {
  %r = va_arg ptr %ap, i32
  ret i32 %r
}

; probe: instruction / ExtractElement
define i32 @probe(<4 x i32> %v) {
  %r = extractelement <4 x i32> %v, i64 1
  ret i32 %r
}

; probe: instruction / InsertElement
define <4 x i32> @probe(<4 x i32> %v, i32 %a) {
  %r = insertelement <4 x i32> %v, i32 %a, i64 1
  ret <4 x i32> %r
}

; probe: instruction / ShuffleVector
define <4 x i32> @probe(<4 x i32> %v, <4 x i32> %w) {
  %r = shufflevector <4 x i32> %v, <4 x i32> %w, <4 x i32> <i32 0, i32 5, i32 2, i32 7>
  ret <4 x i32> %r
}

; probe: instruction / ExtractValue
define i32 @probe({ i32, i8 } %s) {
  %r = extractvalue { i32, i8 } %s, 0
  ret i32 %r
}

; probe: instruction / InsertValue
define { i32, i8 } @probe({ i32, i8 } %s, i8 %b) {
  %r = insertvalue { i32, i8 } %s, i8 %b, 1
  ret { i32, i8 } %r
}

; probe: instruction / Freeze
define i32 @probe(i32 %a) {
  %r = freeze i32 %a
  ret i32 %r
}

; probe: type / Half
define void @probe(half %x) {
  ret void
}

; probe: type / BFloat
define void @probe(bfloat %x) {
  ret void
}

; probe: type / Float
define void @probe(float %x) {
  ret void
}

; probe: type / Double
define void @probe(double %x) {
  ret void
}

; probe: type / X86_FP80
define void @probe(x86_fp80 %x) {
  ret void
}

; probe: type / FP128
define void @probe(fp128 %x) {
  ret void
}

; probe: type / PPC_FP128
define void @probe(ppc_fp128 %x) {
  ret void
}

; probe: type / Integer
define void @probe(i37 %x) {
  ret void
}

; probe: type / Byte
define void @probe(b8 %x) {
  ret void
}

; probe: type / Struct
define void @probe({ i32, i8 } %x) {
  ret void
}

; probe: type / Array
define void @probe([2 x i32] %x) {
  ret void
}

; probe: type / FixedVector
define void @probe(<4 x i32> %x) {
  ret void
}

; probe: type / ScalableVector
define void @probe(<vscale x 4 x i32> %x) {
  ret void
}

; probe: type / TargetExt
define void @probe(target("aarch64.svcount") %x) {
  ret void
}

; probe: type / Pointer
define ptr @probe(ptr %p) {
  ret ptr %p
}

; probe: type / Void
define void @probe() {
  ret void
}

; probe: type / Label
define void @probe() {
  br label %a
a:
  ret void
}

; probe: type / Function
define void @callee() {
  ret void
}
define void @probe() {
  call void @callee()
  ret void
}

; probe: type / Token
define void @probe() {
  %t = call token @llvm.experimental.convergence.anchor()
  ret void
}

; probe: type / X86_AMX
define void @probe(ptr %p) {
  %t = call x86_amx @llvm.x86.tileloadd64.internal(i16 8, i16 8, ptr %p, i64 8)
  ret void
}

; probe: intrinsic / llvm.dbg.value
define i32 @probe(i32 %a) !dbg !5 {
  call void @llvm.dbg.value(metadata i32 %a, metadata !9, metadata !DIExpression()), !dbg !8
  ret i32 %a, !dbg !8
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4}
!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "p", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug)
!1 = !DIFile(filename: "p.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 7, !"Dwarf Version", i32 5}
!5 = distinct !DISubprogram(name: "probe", scope: !1, file: !1, line: 1, type: !6, scopeLine: 1, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !7)
!6 = !DISubroutineType(types: !7)
!7 = !{}
!8 = !DILocation(line: 1, column: 1, scope: !5)
!9 = !DILocalVariable(name: "a", arg: 1, scope: !5, file: !1, line: 1, type: !10)
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !DILabel(scope: !5, name: "l", file: !1, line: 1)
!12 = distinct !DIAssignID()

; probe: intrinsic / llvm.dbg.declare
define i32 @probe(i32 %a) !dbg !5 {
  call void @llvm.dbg.declare(metadata ptr null, metadata !9, metadata !DIExpression()), !dbg !8
  ret i32 %a, !dbg !8
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4}
!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "p", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug)
!1 = !DIFile(filename: "p.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 7, !"Dwarf Version", i32 5}
!5 = distinct !DISubprogram(name: "probe", scope: !1, file: !1, line: 1, type: !6, scopeLine: 1, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !7)
!6 = !DISubroutineType(types: !7)
!7 = !{}
!8 = !DILocation(line: 1, column: 1, scope: !5)
!9 = !DILocalVariable(name: "a", arg: 1, scope: !5, file: !1, line: 1, type: !10)
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !DILabel(scope: !5, name: "l", file: !1, line: 1)
!12 = distinct !DIAssignID()

; probe: intrinsic / llvm.dbg.label
define i32 @probe(i32 %a) !dbg !5 {
  call void @llvm.dbg.label(metadata !11), !dbg !8
  ret i32 %a, !dbg !8
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4}
!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "p", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug)
!1 = !DIFile(filename: "p.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 7, !"Dwarf Version", i32 5}
!5 = distinct !DISubprogram(name: "probe", scope: !1, file: !1, line: 1, type: !6, scopeLine: 1, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !7)
!6 = !DISubroutineType(types: !7)
!7 = !{}
!8 = !DILocation(line: 1, column: 1, scope: !5)
!9 = !DILocalVariable(name: "a", arg: 1, scope: !5, file: !1, line: 1, type: !10)
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !DILabel(scope: !5, name: "l", file: !1, line: 1)
!12 = distinct !DIAssignID()

; probe: intrinsic / llvm.dbg.assign
define i32 @probe(i32 %a) !dbg !5 {
  call void @llvm.dbg.assign(metadata i32 %a, metadata !9, metadata !DIExpression(), metadata !12, metadata ptr null, metadata !DIExpression()), !dbg !8
  ret i32 %a, !dbg !8
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4}
!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "p", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug)
!1 = !DIFile(filename: "p.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 7, !"Dwarf Version", i32 5}
!5 = distinct !DISubprogram(name: "probe", scope: !1, file: !1, line: 1, type: !6, scopeLine: 1, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !7)
!6 = !DISubroutineType(types: !7)
!7 = !{}
!8 = !DILocation(line: 1, column: 1, scope: !5)
!9 = !DILocalVariable(name: "a", arg: 1, scope: !5, file: !1, line: 1, type: !10)
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !DILabel(scope: !5, name: "l", file: !1, line: 1)
!12 = distinct !DIAssignID()

; probe: intrinsic / llvm.x86.avx512.broadcastmb.128
declare <2 x i64> @llvm.x86.avx512.broadcastmb.128(i8)
define <2 x i64> @probe(i8 %a) {
  %r = call <2 x i64> @llvm.x86.avx512.broadcastmb.128(i8 %a)
  ret <2 x i64> %r
}

; probe: intrinsic / llvm.x86.avx512.broadcastmb.256
declare <4 x i64> @llvm.x86.avx512.broadcastmb.256(i8)
define <4 x i64> @probe(i8 %a) {
  %r = call <4 x i64> @llvm.x86.avx512.broadcastmb.256(i8 %a)
  ret <4 x i64> %r
}

; probe: intrinsic / llvm.x86.avx512.broadcastmb.512
declare <8 x i64> @llvm.x86.avx512.broadcastmb.512(i8)
define <8 x i64> @probe(i8 %a) {
  %r = call <8 x i64> @llvm.x86.avx512.broadcastmb.512(i8 %a)
  ret <8 x i64> %r
}

; probe: intrinsic / llvm.x86.avx512.broadcastmw.128
declare <4 x i32> @llvm.x86.avx512.broadcastmw.128(i16)
define <4 x i32> @probe(i16 %a) {
  %r = call <4 x i32> @llvm.x86.avx512.broadcastmw.128(i16 %a)
  ret <4 x i32> %r
}

; probe: intrinsic / llvm.x86.avx512.broadcastmw.256
declare <8 x i32> @llvm.x86.avx512.broadcastmw.256(i16)
define <8 x i32> @probe(i16 %a) {
  %r = call <8 x i32> @llvm.x86.avx512.broadcastmw.256(i16 %a)
  ret <8 x i32> %r
}

; probe: intrinsic / llvm.x86.avx512.broadcastmw.512
declare <16 x i32> @llvm.x86.avx512.broadcastmw.512(i16)
define <16 x i32> @probe(i16 %a) {
  %r = call <16 x i32> @llvm.x86.avx512.broadcastmw.512(i16 %a)
  ret <16 x i32> %r
}

; probe: metadata / dbg
define i32 @probe(i32 %a) !dbg !5 {
  %r = add i32 %a, 1, !dbg !8
  ret i32 %r, !dbg !8
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4}
!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "p", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug)
!1 = !DIFile(filename: "p.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 7, !"Dwarf Version", i32 5}
!5 = distinct !DISubprogram(name: "probe", scope: !1, file: !1, line: 1, type: !6, scopeLine: 1, spFlags: DISPFlagDefinition, unit: !0)
!6 = !DISubroutineType(types: !7)
!7 = !{}
!8 = !DILocation(line: 1, column: 1, scope: !5)

; probe: metadata / memprof
define void @callee() {
  ret void
}
define void @probe() {
  call void @callee(), !memprof !0, !callsite !3
  ret void
}
!0 = !{!1}
!1 = !{!2, !"notcold"}
!2 = !{i64 1, i64 2}
!3 = !{i64 1}

; probe: metadata / callee_type
define void @probe(ptr %f) {
  call void %f(), !callee_type !0
  ret void
}
!0 = !{!1}
!1 = !{!"_ZTSFvvE.generalized"}

; probe: metadata / DIAssignID
define void @probe(ptr %p, i32 %a) !dbg !5 {
  store i32 %a, ptr %p, !DIAssignID !12, !dbg !8
  call void @llvm.dbg.assign(metadata i32 %a, metadata !9, metadata !DIExpression(), metadata !12, metadata ptr %p, metadata !DIExpression()), !dbg !8
  ret void, !dbg !8
}
declare void @llvm.dbg.assign(metadata, metadata, metadata, metadata, metadata, metadata)
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4}
!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "p", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug)
!1 = !DIFile(filename: "p.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 7, !"Dwarf Version", i32 5}
!5 = distinct !DISubprogram(name: "probe", scope: !1, file: !1, line: 1, type: !6, scopeLine: 1, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !7)
!6 = !DISubroutineType(types: !7)
!7 = !{}
!8 = !DILocation(line: 1, column: 1, scope: !5)
!9 = !DILocalVariable(name: "a", arg: 1, scope: !5, file: !1, line: 1, type: !10)
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!12 = distinct !DIAssignID()

; probe: metadata / nofree
define ptr @probe(i64 %a) {
  %r = inttoptr i64 %a to ptr, !nofree !0
  ret ptr %r
}
!0 = !{}

; probe: metadata / captures
define void @probe(ptr %p, ptr %q) {
  store ptr %q, ptr %p, !captures !0
  ret void
}
!0 = !{!"address"}

; probe: metadata / nofpclass
define float @probe(ptr %p) {
  %v = load float, ptr %p, !nofpclass !0
  ret float %v
}
!0 = !{i32 3}

; probe: metadata / alloc_token
define void @callee() {
  ret void
}
define void @probe() {
  call void @callee(), !alloc_token !0
  ret void
}
!0 = !{!"t", i64 1}

; probe: metadata / mem.cache_hint
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
define void @probe(ptr %p) {
  call void @llvm.memset.p0.i64(ptr %p, i8 0, i64 4, i1 false), !mem.cache_hint !0
  ret void
}
!0 = !{i32 0, !1}
!1 = !{!"x", i32 1}

; probe: metadata / inline_history
define void @callee() {
  ret void
}
define void @probe() {
  call void @callee(), !inline_history !0
  ret void
}
!0 = !{ptr @callee}

; probe: metadata / heapallocsite
define void @callee() {
  ret void
}
define void @probe() {
  call void @callee(), !heapallocsite !0
  ret void
}
!0 = !{}

; probe: linkage / External
define i32 @probe(i32 %a) {
  ret i32 %a
}

; probe: linkage / Internal
define internal i32 @probe(i32 %a) {
  ret i32 %a
}

; probe: linkage / Private
define private i32 @probe(i32 %a) {
  ret i32 %a
}

; probe: linkage / LinkOnceODR
define linkonce_odr i32 @probe(i32 %a) {
  ret i32 %a
}

; probe: linkage / WeakODR
define weak_odr i32 @probe(i32 %a) {
  ret i32 %a
}

; probe: linkage / LinkOnceAny
define linkonce i32 @probe(i32 %a) {
  ret i32 %a
}

; probe: linkage / WeakAny
define weak i32 @probe(i32 %a) {
  ret i32 %a
}

; probe: linkage / AvailableExternally
define available_externally i32 @probe(i32 %a) {
  ret i32 %a
}

; probe: linkage / Appending
@a = appending global [1 x i32] [i32 1]
define i32 @probe() {
  %v = load i32, ptr @a
  ret i32 %v
}

; probe: linkage / Common
@c = common global i32 0
define i32 @probe() {
  %v = load i32, ptr @c
  ret i32 %v
}

; probe: linkage / ExternalWeak
declare extern_weak i32 @f(i32)
define i32 @probe(i32 %a) {
  %r = call i32 @f(i32 %a)
  ret i32 %r
}

; probe: constant / ConstantInt
define i32 @probe() {
  ret i32 7
}

; probe: constant / PoisonValue
define i32 @probe() {
  ret i32 poison
}

; probe: constant / UndefValue
define i32 @probe() {
  ret i32 undef
}

; probe: constant / ConstantPointerNull
define ptr @probe() {
  ret ptr null
}

; probe: constant / ConstantAggregateZero
define <4 x i32> @probe() {
  ret <4 x i32> zeroinitializer
}

; probe: constant / ConstantDataVector
define <2 x i32> @probe() {
  ret <2 x i32> <i32 1, i32 2>
}

; probe: constant / ConstantVector
define <2 x i32> @probe() {
  ret <2 x i32> <i32 1, i32 poison>
}

; probe: constant / ConstantStruct
define { i32, i8 } @probe() {
  ret { i32, i8 } { i32 1, i8 2 }
}

; probe: constant / GlobalVariable
@g = global i32 1
define i32 @probe() {
  %v = load i32, ptr @g
  ret i32 %v
}

; probe: constant / ConstantDataArray
@g = global [2 x i32] [i32 1, i32 2]
define i32 @probe() {
  %v = load i32, ptr @g
  ret i32 %v
}

; probe: constant / ConstantArray
@h = global i32 0
@g = global [2 x ptr] [ptr @h, ptr @h]
define ptr @probe() {
  %v = load ptr, ptr @g
  ret ptr %v
}

; probe: constant / Function
define void @callee() {
  ret void
}
define ptr @probe() {
  ret ptr @callee
}

; probe: constant / ConstantFP
define float @probe() {
  ret float 1.0
}

; probe: constant / ConstantByte
define b8 @probe() {
  ret b8 1
}

; probe: constant / ConstantExpr
@g = global i32 0
define i64 @probe() {
  ret i64 ptrtoint (ptr @g to i64)
}

; probe: constant / GlobalAlias
@g = global i32 1
@a = alias i32, ptr @g
define i32 @probe() {
  %v = load i32, ptr @a
  ret i32 %v
}

; probe: constant / GlobalIFunc
define ptr @resolver() {
  ret ptr null
}
@i = ifunc void (), ptr @resolver
define void @probe() {
  call void @i()
  ret void
}

; probe: constant / DSOLocalEquivalent
declare void @f()
define ptr @probe() {
  ret ptr dso_local_equivalent @f
}

; probe: constant / NoCFIValue
define void @callee() {
  ret void
}
define ptr @probe() {
  ret ptr no_cfi @callee
}

; probe: constant / ConstantTokenNone
define void @probe() {
  %t = call token @llvm.experimental.convergence.anchor()
  ret void
}

; probe: constant / ConstantTargetNone
define target("spirv.Event") @probe() {
  ret target("spirv.Event") zeroinitializer
}

; probe: constant / ConstantPtrAuth
define void @callee() {
  ret void
}
define ptr @probe() {
  ret ptr ptrauth (ptr @callee, i32 0)
}

; probe: constant / BlockAddress
define ptr @probe() {
entry:
  br label %b
b:
  ret ptr blockaddress(@probe, %b)
}

; probe: operand bundle / deopt
define void @callee() {
  ret void
}
define void @probe() {
  call void @callee() [ "deopt"() ]
  ret void
}

; probe: operand bundle / gc-transition
define void @callee() {
  ret void
}
define void @probe() {
  call void @callee() [ "gc-transition"() ]
  ret void
}

; probe: operand bundle / gc-live
define void @callee() {
  ret void
}
define void @probe() {
  call void @callee() [ "gc-live"() ]
  ret void
}

; probe: operand bundle / cfguardtarget
define void @callee() {
  ret void
}
define void @probe(ptr %f) {
  call void %f() [ "cfguardtarget"(ptr @callee) ]
  ret void
}

; probe: operand bundle / kcfi
define void @probe(ptr %f) {
  call void %f() [ "kcfi"(i32 1) ]
  ret void
}

; probe: operand bundle / ptrauth
define void @probe(ptr %f) {
  call void %f() [ "ptrauth"(i32 0, i64 0) ]
  ret void
}

; probe: operand bundle / deactivation-symbol
define void @callee() {
  ret void
}
@s = global i8 0
define void @probe() {
  call void @callee() [ "deactivation-symbol"(ptr @s) ]
  ret void
}

; probe: operand bundle / funclet
declare i32 @__CxxFrameHandler3(...)
define void @callee() {
  ret void
}
define void @probe() personality ptr @__CxxFrameHandler3 {
entry:
  invoke void @callee() to label %exit unwind label %cl
cl:
  %c = cleanuppad within none []
  call void @callee() [ "funclet"(token %c) ]
  cleanupret from %c unwind to caller
exit:
  ret void
}

; probe: operand bundle / preallocated
define void @callee(ptr preallocated(i32) %a) {
  ret void
}
define void @probe() {
  %t = call token @llvm.call.preallocated.setup(i32 1)
  %a = call ptr @llvm.call.preallocated.arg(token %t, i32 0) preallocated(i32)
  call void @callee(ptr preallocated(i32) %a) [ "preallocated"(token %t) ]
  ret void
}

; probe: operand bundle / clang.arc.attachedcall
declare ptr @objc_retainAutoreleasedReturnValue(ptr)
define ptr @callee() {
  ret ptr null
}
define void @probe() {
  %r = call ptr @callee() [ "clang.arc.attachedcall"(ptr @objc_retainAutoreleasedReturnValue) ]
  ret void
}

; probe: operand bundle / convergencectrl
define void @callee() convergent {
  ret void
}
define void @probe() convergent {
  %t = call token @llvm.experimental.convergence.entry()
  call void @callee() [ "convergencectrl"(token %t) ]
  ret void
}

; probe: operand bundle / assume:align
define void @probe(ptr %p) {
  call void @llvm.assume(i1 true) [ "align"(ptr %p, i64 8) ]
  ret void
}

; probe: operand bundle / assume:dereferenceable
define void @probe(ptr %p) {
  call void @llvm.assume(i1 true) [ "dereferenceable"(ptr %p, i64 8) ]
  ret void
}

; probe: operand bundle / assume:dereferenceable_or_null
define void @probe(ptr %p) {
  call void @llvm.assume(i1 true) [ "dereferenceable_or_null"(ptr %p, i64 8) ]
  ret void
}

; probe: operand bundle / assume:nonnull
define void @probe(ptr %p) {
  call void @llvm.assume(i1 true) [ "nonnull"(ptr %p) ]
  ret void
}

; probe: operand bundle / assume:noundef
define void @probe(ptr %p) {
  call void @llvm.assume(i1 true) [ "noundef"(ptr %p) ]
  ret void
}

; probe: operand bundle / assume:separate_storage
define void @probe(ptr %p) {
  call void @llvm.assume(i1 true) [ "separate_storage"(ptr %p, ptr %p) ]
  ret void
}

; probe: operand bundle / assume:ignore
define void @probe(ptr %p) {
  call void @llvm.assume(i1 true) [ "ignore"(ptr %p) ]
  ret void
}

; probe: operand bundle / assume:cold
define void @probe(ptr %p) {
  call void @llvm.assume(i1 true) [ "cold"() ]
  ret void
}

; probe: form / udiv-of-vectors
define <4 x i32> @probe(<4 x i32> %a, <4 x i32> %b) {
  %r = udiv <4 x i32> %a, %b
  ret <4 x i32> %r
}

; probe: form / sdiv-of-vectors
define <4 x i32> @probe(<4 x i32> %a, <4 x i32> %b) {
  %r = sdiv <4 x i32> %a, %b
  ret <4 x i32> %r
}

; probe: form / urem-of-vectors
define <4 x i32> @probe(<4 x i32> %a, <4 x i32> %b) {
  %r = urem <4 x i32> %a, %b
  ret <4 x i32> %r
}

; probe: form / srem-of-vectors
define <4 x i32> @probe(<4 x i32> %a, <4 x i32> %b) {
  %r = srem <4 x i32> %a, %b
  ret <4 x i32> %r
}

; probe: form / freeze-of-a-vector
define <4 x i32> @probe(<4 x i32> %a) {
  %r = freeze <4 x i32> %a
  ret <4 x i32> %r
}

; probe: form / freeze-of-a-pointer
define ptr @probe(ptr %a) {
  %r = freeze ptr %a
  ret ptr %r
}

; probe: form / freeze-of-a-struct
define { i32, i8 } @probe({ i32, i8 } %a) {
  %r = freeze { i32, i8 } %a
  ret { i32, i8 } %r
}

; probe: form / array-value
define i32 @probe([2 x i32] %a) {
  %r = extractvalue [2 x i32] %a, 0
  ret i32 %r
}

; probe: form / insertvalue-nested
define { { i32, i8 }, i8 } @probe({ { i32, i8 }, i8 } %s, i32 %a) {
  %r = insertvalue { { i32, i8 }, i8 } %s, i32 %a, 0, 0
  ret { { i32, i8 }, i8 } %r
}

; probe: form / integer-bitcast-nondividing
define <2 x i24> @probe(<3 x i16> %a) {
  %r = bitcast <3 x i16> %a to <2 x i24>
  ret <2 x i24> %r
}

; probe: form / pointer-in-address-space
define ptr addrspace(1) @probe(ptr addrspace(1) %p) {
  ret ptr addrspace(1) %p
}

; probe: form / vector-of-pointers
define <2 x ptr> @probe(<2 x ptr> %p) {
  ret <2 x ptr> %p
}

; probe: form / getelementptr-of-vectors
define <2 x ptr> @probe(ptr %p, <2 x i64> %i) {
  %r = getelementptr i32, ptr %p, <2 x i64> %i
  ret <2 x ptr> %r
}

; probe: form / data-layout-32-bit-pointers-with-memory
target datalayout = "e-p:32:32"
define i32 @probe(ptr %p) {
  %v = load i32, ptr %p
  ret i32 %v
}

; probe: form / data-layout-explicit-64-bit
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
define i32 @probe(ptr %p) {
  %v = load i32, ptr %p
  ret i32 %v
}

; probe: form / big-endian-bitcast
target datalayout = "E"
define i64 @probe(<2 x i32> %a) {
  %r = bitcast <2 x i32> %a to i64
  ret i64 %r
}

; probe: form / store-of-i1
define void @probe(ptr %p, i1 %v) {
  store i1 %v, ptr %p
  ret void
}

; probe: form / load-of-i1
define i1 @probe(ptr %p) {
  %v = load i1, ptr %p
  ret i1 %v
}

; probe: form / volatile-load
define i32 @probe(ptr %p) {
  %v = load volatile i32, ptr %p
  ret i32 %v
}

; probe: form / volatile-store
define void @probe(ptr %p) {
  store volatile i32 1, ptr %p
  ret void
}

; probe: form / atomic-load
define i32 @probe(ptr %p) {
  %v = load atomic i32, ptr %p seq_cst, align 4
  ret i32 %v
}

; probe: form / atomic-store
define void @probe(ptr %p) {
  store atomic i32 1, ptr %p seq_cst, align 4
  ret void
}

; probe: form / call-to-a-declaration
declare i32 @f(i32)
define i32 @probe(i32 %a) {
  %r = call i32 @f(i32 %a)
  ret i32 %r
}

; probe: form / call-to-an-odr-definition
define linkonce_odr i32 @f(i32 %a) {
  ret i32 %a
}
define i32 @probe(i32 %a) {
  %r = call i32 @f(i32 %a)
  ret i32 %r
}

; probe: form / variadic-call
define void @f(i32 %a, ...) {
  ret void
}
define void @probe(i32 %a) {
  call void (i32, ...) @f(i32 %a, i32 %a)
  ret void
}

; probe: form / variadic-function
define i32 @probe(i32 %a, ...) {
  ret i32 %a
}

; probe: form / alias-the-linker-may-replace
@g = global i32 1
@a = weak alias i32, ptr @g
define i32 @probe() {
  %v = load i32, ptr @a
  ret i32 %v
}

; probe: form / external-global
@g = external global i32
define i32 @probe() {
  %v = load i32, ptr @g
  ret i32 %v
}

; probe: form / personality-function
declare i32 @__gxx_personality_v0(...)
define i32 @probe(i32 %a) personality ptr @__gxx_personality_v0 {
  ret i32 %a
}

; probe: form / inline-asm-call
define i32 @probe(i32 %a) {
  %r = call i32 asm "mov $1, $0", "=r,r"(i32 %a)
  ret i32 %r
}

; probe: form / function-with-gc
define i32 @probe(i32 %a) gc "statepoint-example" {
  ret i32 %a
}

; probe: form / prefix-or-prologue-data
define i32 @probe(i32 %a) prefix i32 1 {
  ret i32 %a
}

; probe: form / calling-convention-mismatch
define fastcc i32 @callee(i32 %a) {
  ret i32 %a
}
define i32 @probe(i32 %a) {
  %r = call i32 @callee(i32 %a)
  ret i32 %r
}

; probe: form / abi-attribute-mismatch
define internal i32 @callee(i32 %a) {
  ret i32 %a
}
define i32 @probe(i32 %a) {
  %r = call i32 @callee(i32 inreg %a)
  ret i32 %r
}

; probe: form / indirect-call
define i32 @callee(i32 %a) {
  ret i32 %a
}
@fp = global ptr @callee
define i32 @probe(ptr %f, i32 %a) {
  %r = call i32 %f(i32 %a)
  ret i32 %r
}

; probe: form / tail-call
define i32 @callee(i32 %a) {
  ret i32 %a
}
define i32 @probe(i32 %a) {
  %r = tail call i32 @callee(i32 %a)
  ret i32 %r
}

; probe: form / musttail-call
define i32 @callee(i32 %a) {
  ret i32 %a
}
define i32 @probe(i32 %a) {
  %r = musttail call i32 @callee(i32 %a)
  ret i32 %r
}

; probe: form / notail-call
define i32 @callee(i32 %a) {
  ret i32 %a
}
define i32 @probe(i32 %a) {
  %r = notail call i32 @callee(i32 %a)
  ret i32 %r
}

; probe: form / noundef-on-a-vector
define <4 x i32> @probe(<4 x i32> noundef %a) {
  ret <4 x i32> %a
}

; probe: form / range-on-a-vector
define <4 x i32> @probe(<4 x i32> range(i32 0, 10) %a) {
  ret <4 x i32> %a
}

; probe: form / undef-in-a-vector
define <2 x i32> @probe() {
  ret <2 x i32> <i32 1, i32 undef>
}

; probe: form / getelementptr-constant-expression
@g = global [4 x i32] zeroinitializer
define ptr @probe() {
  ret ptr getelementptr inbounds ([4 x i32], ptr @g, i64 0, i64 1)
}

; probe: form / noundef-on-a-struct
define { i32, i8 } @probe({ i32, i8 } noundef %s) {
  ret { i32, i8 } %s
}

; probe: form / vector-constant-expression
define <2 x i64> @probe() {
  ret <2 x i64> bitcast (<4 x i32> <i32 1, i32 2, i32 3, i32 4> to <2 x i64>)
}

; probe: form / getelementptr-over-a-scalable-type
define ptr @probe(ptr %p, i64 %i) {
  %q = getelementptr <vscale x 4 x i32>, ptr %p, i64 %i
  ret ptr %q
}

; probe: form / speculatable-with-memory
define i32 @probe(ptr %p) speculatable {
  %v = load i32, ptr %p
  ret i32 %v
}

; probe: form / call-to-a-speculatable-function
define i32 @callee(i32 %a) speculatable {
  ret i32 %a
}
define i32 @probe(i32 %a) {
  %r = call i32 @callee(i32 %a)
  ret i32 %r
}

; probe: form / scalable-vector-in-a-recursive-function
define <vscale x 4 x i32> @probe(<vscale x 4 x i32> %a, i32 %n) {
entry:
  %z = icmp eq i32 %n, 0
  br i1 %z, label %done, label %again
again:
  %m = sub i32 %n, 1
  %r = call <vscale x 4 x i32> @probe(<vscale x 4 x i32> %a, i32 %m)
  ret <vscale x 4 x i32> %r
done:
  ret <vscale x 4 x i32> %a
}

; probe: form / load-of-a-scalable-vector
define <vscale x 4 x i32> @probe(ptr %p) {
  %v = load <vscale x 4 x i32>, ptr %p
  ret <vscale x 4 x i32> %v
}

; probe: form / intrinsic-lane-count-mismatch
define <4 x i32> @probe(float %a) {
  %r = call <4 x i32> @llvm.fptosi.sat.v4i32.f32(float %a)
  ret <4 x i32> %r
}
declare <4 x i32> @llvm.fptosi.sat.v4i32.f32(float)
