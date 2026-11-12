; Code the model must stop on, because LLVM says it's undefined. Comparing with native code can't
; show this, so these run with `tests/differential.py --expect-ub`.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare void @llvm.lifetime.start.p0(ptr)
declare void @llvm.lifetime.end.p0(ptr)
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)
declare void @llvm.assume(i1)
declare i32 @llvm.ctpop.i32(i32)
declare i32 @llvm.expect.i32(i32, i32)

; The index times 8 wraps to 0, and `inbounds` makes that poison, so the load is undefined.
define i32 @gep_constant_wraps(i32 %x) {
  %a = alloca i64, align 8
  store i32 %x, ptr %a, align 4
  %p = getelementptr inbounds i64, ptr %a, i64 2305843009213693952
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; Each index fits, but adding them wraps to 0.
define i32 @gep_constant_sum_wraps(i32 %x) {
  %a = alloca [2 x i64], align 8
  store i32 %x, ptr %a, align 4
  %p = getelementptr inbounds [2 x i64], ptr %a, i64 -576460752303423488, i64 -1152921504606846976
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; The total is 0, but the first two offsets already overflow.
define i32 @gep_partial_sum_wraps(i32 %x) {
  %a = alloca i64, align 8
  store i32 %x, ptr %a, align 4
  %i = add i64 0, 1
  %p = getelementptr nusw [1 x [1 x i8]], ptr %a, i64 9223372036854775807, i64 %i, i64 -9223372036854775808
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

define i32 @store_after_lifetime_end(i32 %x) {
  %a = alloca i32, align 4
  call void @llvm.lifetime.start.p0(ptr %a)
  call void @llvm.lifetime.end.p0(ptr %a)
  store i32 %x, ptr %a, align 4
  ret i32 %x
}

; An alloca with `lifetime.start` is dead until it runs.
define i32 @store_before_lifetime_start(i32 %x) {
  %a = alloca i32, align 4
  store i32 %x, ptr %a, align 4
  call void @llvm.lifetime.start.p0(ptr %a)
  ret i32 %x
}

; `align 8` makes the misaligned pointer poison.
define i32 @memset_misaligned(i32 %x) {
  %a = alloca i64, align 8
  %p = getelementptr inbounds i8, ptr %a, i64 1
  call void @llvm.memset.p0.i64(ptr align 8 %p, i8 0, i64 1, i1 false)
  ret i32 %x
}

define i32 @memcpy_misaligned(i32 %x) {
  %a = alloca [2 x i64], align 8
  %p = getelementptr inbounds i8, ptr %a, i64 1
  %q = getelementptr inbounds i8, ptr %a, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr %q, ptr align 8 %p, i64 1, i1 false)
  ret i32 %x
}

; `expect` returns its first argument, but the second one's attributes still count.
define i32 @unused_argument_out_of_range(i32 %x) {
  %r = call i32 @llvm.expect.i32(i32 %x, i32 noundef range(i32 1, 2) 0)
  ret i32 %r
}

; Zero bits are set, which the return attributes make undefined.
define i32 @intrinsic_result_out_of_range(i32 %x) {
  %r = call noundef range(i32 1, 2) i32 @llvm.ctpop.i32(i32 0)
  ret i32 %r
}

; `inbounds` checks each step. Here the first leaves the alloca, and the second comes all the way back.
define i32 @gep_out_and_back(i32 %x) {
  %a = alloca i64, align 8
  store i32 %x, ptr %a, align 4
  %p = getelementptr inbounds [2 x i64], ptr %a, i64 1, i64 -2
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; The same, ending somewhere else inside the alloca.
define i32 @gep_out_and_partly_back(i32 %x) {
  %a = alloca i64, align 8
  store i64 0, ptr %a, align 8
  %p = getelementptr inbounds [16 x i8], ptr %a, i64 1, i64 -12
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; The same, with an index that isn't a constant.
define i32 @gep_out_and_back_variable(i32 %x) {
  %a = alloca i64, align 8
  store i32 %x, ptr %a, align 4
  %i = add i64 0, 1
  %p = getelementptr inbounds [2 x i64], ptr %a, i64 %i, i64 -2
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; A non-zero `inbounds` needs its base in bounds, even if the result is.
define i32 @gep_base_out_of_bounds(i32 %x) {
  %a = alloca i64, align 8
  store i32 %x, ptr %a, align 4
  %q = getelementptr i8, ptr %a, i64 100
  %p = getelementptr inbounds i8, ptr %q, i64 -100
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; `nusw`: adding this to the address goes below zero, so %q is poison, and so is what comes from it.
define i32 @gep_nusw_address_wraps(i32 %x) {
  %a = alloca i64, align 8
  store i32 %x, ptr %a, align 4
  %q = getelementptr nusw i8, ptr %a, i64 -9223372036854775808
  %p = getelementptr i8, ptr %q, i64 -9223372036854775808
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; `nuw`: as an unsigned number, -1 wraps the address. It doesn't wrap the offset into the allocation.
define i32 @gep_nuw_address_wraps(i32 %x) {
  %a = alloca i64, align 8
  store i32 %x, ptr %a, align 4
  %q = getelementptr nuw i8, ptr %a, i64 -1
  %p = getelementptr i8, ptr %q, i64 1
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; The offset is always zero here, but a poison index still makes the result poison.
define i32 @gep_zero_size_poison_index(i32 %x) {
  %a = alloca i64, align 8
  store i32 %x, ptr %a, align 4
  %i = add nuw i64 -1, 1
  %p = getelementptr [0 x i8], ptr %a, i64 %i
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; `nuw`: the index times 8 wraps to 0 as an unsigned number, even though no address does.
define i32 @gep_nuw_constant_multiplication_wraps(i32 %x) {
  %a = alloca i64, align 8
  store i32 %x, ptr %a, align 4
  %p = getelementptr nuw i64, ptr %a, i64 2305843009213693952
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

; From here on, promises the code breaks. The helpers are `internal`, so only the callers run.

; `nonnull` in an assume is a promise like any other.
define i32 @assume_nonnull_of_null(i32 %x) {
  call void @llvm.assume(i1 true) [ "nonnull"(ptr null) ]
  ret i32 %x
}

; So is `align`: a byte past an 8-aligned allocation isn't 8-aligned.
define i32 @assume_align_misaligned(i32 %x) {
  %a = alloca i64, align 8
  %p = getelementptr inbounds i8, ptr %a, i64 1
  call void @llvm.assume(i1 true) [ "align"(ptr %p, i64 8) ]
  ret i32 %x
}

; With an offset, it's the pointer less the offset that has to be aligned: here that's the allocation plus 2.
define i32 @assume_align_offset_misaligned(i32 %x) {
  %a = alloca i64, align 8
  %p = getelementptr inbounds i8, ptr %a, i64 4
  call void @llvm.assume(i1 true) [ "align"(ptr %p, i64 4, i64 2) ]
  ret i32 %x
}

; An alignment that isn't a power of two needs a null pointer.
define i32 @assume_align_not_a_power_of_two(i32 %x) {
  %a = alloca i64, align 8
  call void @llvm.assume(i1 true) [ "align"(ptr %a, i64 6) ]
  ret i32 %x
}

; With an offset, it's the pointer less the offset that has to be null: null itself, less 4, isn't.
define i32 @assume_align_not_a_power_of_two_offset(i32 %x) {
  call void @llvm.assume(i1 true) [ "align"(ptr null, i64 3, i64 4) ]
  ret i32 %x
}

; The same for an alignment of zero.
define i32 @assume_align_zero_offset(i32 %x) {
  call void @llvm.assume(i1 true) [ "align"(ptr null, i64 0, i64 4) ]
  ret i32 %x
}

; `noundef` on poison.
define i32 @assume_noundef_of_poison(i32 %x) {
  call void @llvm.assume(i1 true) [ "noundef"(i32 poison) ]
  ret i32 %x
}

define internal void @writes_readonly(ptr readonly %p) {
  store i32 1, ptr %p, align 4
  ret void
}

define i32 @readonly_written(i32 %x) {
  %a = alloca i32, align 4
  call void @writes_readonly(ptr %a)
  ret i32 %x
}

; A copy through memory is still based on the argument.
define internal void @writes_readonly_through_memory(ptr readonly %p) {
  %slot = alloca ptr, align 8
  store ptr %p, ptr %slot, align 8
  %q = load ptr, ptr %slot, align 8
  %r = getelementptr i8, ptr %q, i64 0
  store i32 1, ptr %r, align 4
  ret void
}

define i32 @readonly_written_through_a_copy(i32 %x) {
  %a = alloca i32, align 4
  call void @writes_readonly_through_memory(ptr %a)
  ret i32 %x
}

define internal i32 @reads_readnone(ptr readnone %p) {
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

define i32 @readnone_read(i32 %x) {
  %a = alloca i32, align 4
  store i32 %x, ptr %a, align 4
  %r = call i32 @reads_readnone(ptr %a)
  ret i32 %r
}

; `writeonly`: reading before writing gives poison, which `noundef` makes undefined here.
define internal noundef i32 @reads_writeonly_first(ptr writeonly %p) {
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

define i32 @writeonly_read_first(i32 %x) {
  %a = alloca i32, align 4
  store i32 %x, ptr %a, align 4
  %r = call i32 @reads_writeonly_first(ptr %a)
  ret i32 %r
}

define internal noundef i32 @reads_initializes_first(ptr initializes((0, 4)) %p) {
  %v = load i32, ptr %p, align 4
  store i32 0, ptr %p, align 4
  ret i32 %v
}

define i32 @initializes_read_first(i32 %x) {
  %a = alloca i32, align 4
  store i32 %x, ptr %a, align 4
  %r = call i32 @reads_initializes_first(ptr %a)
  ret i32 %r
}

; What `initializes` didn't write is `undef` afterwards, which the model reads as poison.
define internal void @leaves_initializes_unwritten(ptr initializes((0, 4)) %p) {
  ret void
}

define i32 @initializes_not_written(i32 %x) {
  %a = alloca i32, align 4
  store i32 %x, ptr %a, align 4
  call void @leaves_initializes_unwritten(ptr %a)
  %v = load i32, ptr %a, align 4
  %c = icmp eq i32 %v, 0
  br i1 %c, label %yes, label %no
yes:
  ret i32 1
no:
  ret i32 %x
}

; Provenance that wasn't captured is gone once the function returns, however the pointer got out.
define internal ptr @returns_uncaptured(ptr captures(address) %p) {
  ret ptr %p
}

define i32 @captures_address_used_after(i32 %x) {
  %a = alloca i32, align 4
  store i32 %x, ptr %a, align 4
  %q = call ptr @returns_uncaptured(ptr %a)
  %v = load i32, ptr %q, align 4
  ret i32 %v
}

define internal void @stores_uncaptured(ptr captures(none) %p, ptr %to) {
  store ptr %p, ptr %to, align 8
  ret void
}

define i32 @captures_none_stored_and_used_after(i32 %x) {
  %a = alloca i32, align 4
  %slot = alloca ptr, align 8
  store i32 %x, ptr %a, align 4
  call void @stores_uncaptured(ptr %a, ptr %slot)
  %q = load ptr, ptr %slot, align 8
  %v = load i32, ptr %q, align 4
  ret i32 %v
}

define internal ptr @returns_for_reading(ptr captures(address, read_provenance) %p) {
  ret ptr %p
}

define i32 @read_provenance_written_after(i32 %x) {
  %a = alloca i32, align 4
  %q = call ptr @returns_for_reading(ptr %a)
  store i32 %x, ptr %q, align 4
  ret i32 %x
}

; `memory(read)`: writing is undefined at once, even a write of the same value.
@shared = global i32 7

define internal void @writes_in_memory_read() memory(read) {
  %v = load i32, ptr @shared, align 4
  store i32 %v, ptr @shared, align 4
  ret void
}

define i32 @memory_read_written(i32 %x) {
  call void @writes_in_memory_read()
  ret i32 %x
}

; `memory(argmem: read)` covers what's based on an argument, and this isn't.
define internal void @writes_argument_read_only(ptr %p) memory(argmem: read, inaccessiblemem: none) {
  store i32 1, ptr %p, align 4
  ret void
}

define i32 @memory_argmem_read_written(i32 %x) {
  %a = alloca i32, align 4
  call void @writes_argument_read_only(ptr %a)
  ret i32 %x
}

; `memory(write)`: reading before writing gives poison.
define internal noundef i32 @reads_in_memory_write() memory(write) {
  %v = load i32, ptr @shared, align 4
  ret i32 %v
}

define i32 @memory_write_read_first(i32 %x) {
  %r = call i32 @reads_in_memory_write()
  ret i32 %r
}

; A callee is held to what its caller promised.
define internal void @writes_shared() {
  store i32 1, ptr @shared, align 4
  ret void
}

define internal void @calls_a_writer() memory(read) {
  call void @writes_shared()
  ret void
}

define i32 @memory_read_callee_writes(i32 %x) {
  call void @calls_a_writer()
  ret i32 %x
}

declare ptr @malloc(i64)
declare void @free(ptr)

define internal void @frees_nofree(ptr nofree %p) {
  call void @free(ptr %p)
  ret void
}

define i32 @nofree_argument_freed(i32 %x) {
  %p = call ptr @malloc(i64 4)
  call void @frees_nofree(ptr %p)
  ret i32 %x
}

; Every kind of access is held to the same rules, not just loads and stores of integers.
define internal void @stores_pointer_through_readonly(ptr readonly %p) {
  store ptr null, ptr %p, align 8
  ret void
}

define i32 @readonly_pointer_written(i32 %x) {
  %a = alloca ptr, align 8
  call void @stores_pointer_through_readonly(ptr %a)
  ret i32 %x
}

define internal void @loads_pointer_through_readnone(ptr readnone %p) {
  %q = load ptr, ptr %p, align 8
  ret void
}

define i32 @readnone_pointer_read(i32 %x) {
  %a = alloca ptr, align 8
  store ptr null, ptr %a, align 8
  call void @loads_pointer_through_readnone(ptr %a)
  ret i32 %x
}

define internal void @memset_through_readonly(ptr readonly %p) {
  call void @llvm.memset.p0.i64(ptr %p, i8 0, i64 4, i1 false)
  ret void
}

define i32 @readonly_memset(i32 %x) {
  %a = alloca i32, align 4
  call void @memset_through_readonly(ptr %a)
  ret i32 %x
}

define internal void @memcpy_to_readonly(ptr readonly %p, ptr %q) {
  call void @llvm.memcpy.p0.p0.i64(ptr %p, ptr %q, i64 4, i1 false)
  ret void
}

define i32 @readonly_memcpy_destination(i32 %x) {
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  store i32 %x, ptr %b, align 4
  call void @memcpy_to_readonly(ptr %a, ptr %b)
  ret i32 %x
}

define internal void @memcpy_from_readnone(ptr %p, ptr readnone %q) {
  call void @llvm.memcpy.p0.p0.i64(ptr %p, ptr %q, i64 4, i1 false)
  ret void
}

define i32 @readnone_memcpy_source(i32 %x) {
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  store i32 %x, ptr %b, align 4
  call void @memcpy_from_readnone(ptr %a, ptr %b)
  ret i32 %x
}

declare i64 @strlen(ptr)

define internal i64 @strlen_through_readnone(ptr readnone %p) {
  %n = call i64 @strlen(ptr %p)
  ret i64 %n
}

define i32 @readnone_strlen(i32 %x) {
  %a = alloca i8, align 1
  store i8 0, ptr %a, align 1
  %n = call i64 @strlen_through_readnone(ptr %a)
  ret i32 %x
}

; `free` and `malloc` write what the allocator owns, which `memory(read)` rules out.
define internal void @frees_in_memory_read(ptr %p) memory(read) {
  call void @free(ptr %p)
  ret void
}

define i32 @memory_read_frees(i32 %x) {
  %p = call ptr @malloc(i64 4)
  call void @frees_in_memory_read(ptr %p)
  ret i32 %x
}

define internal void @mallocs_in_memory_read() memory(read) {
  %p = call ptr @malloc(i64 4)
  ret void
}

define i32 @memory_read_mallocs(i32 %x) {
  call void @mallocs_in_memory_read()
  ret i32 %x
}

; A callee that has its own promises is held to its caller's as well.
define internal void @writes_with_its_own_promise() memory(write) {
  store i32 1, ptr @shared, align 4
  ret void
}

define internal void @calls_a_promising_writer() memory(read) {
  call void @writes_with_its_own_promise()
  ret void
}

define i32 @memory_read_callee_with_promises_writes(i32 %x) {
  call void @calls_a_promising_writer()
  ret i32 %x
}

; `memory(write)` only remembers what was really written.
define internal noundef i32 @writes_one_reads_another(ptr %p) memory(argmem: write) {
  store i32 1, ptr %p, align 4
  %q = getelementptr i8, ptr %p, i64 4
  %v = load i32, ptr %q, align 4
  ret i32 %v
}

define i32 @memory_write_reads_elsewhere(i32 %x) {
  %a = alloca [2 x i32], align 4
  %b = getelementptr i32, ptr %a, i64 1
  store i32 %x, ptr %b, align 4
  %r = call i32 @writes_one_reads_another(ptr %a)
  ret i32 %r
}

; `memory(read, argmem: readwrite)` only lets arguments be written.
define internal void @writes_global_not_argument(ptr %p) memory(read, argmem: readwrite) {
  store i32 1, ptr @shared, align 4
  ret void
}

define i32 @memory_write_outside_the_arguments(i32 %x) {
  %a = alloca i32, align 4
  call void @writes_global_not_argument(ptr %a)
  ret i32 %x
}

; `initializes` only counts writes through the argument it's on. Another pointer to the same memory doesn't.
define internal noundef i32 @initialized_through_the_other(ptr initializes((0, 4)) %p, ptr %q) {
  store i32 42, ptr %q, align 4
  %v = load i32, ptr %p, align 4
  store i32 0, ptr %p, align 4
  ret i32 %v
}

define i32 @initializes_written_through_another_pointer(i32 %x) {
  %a = alloca i32, align 4
  %r = call i32 @initialized_through_the_other(ptr %a, ptr %a)
  ret i32 %r
}

; And at return, what wasn't written through it is `undef`, even if another pointer wrote it.
define internal void @only_the_other_writes(ptr initializes((0, 4)) %p, ptr %q) {
  store i32 42, ptr %q, align 4
  ret void
}

define i32 @initializes_other_pointer_then_read_after(i32 %x) {
  %a = alloca i32, align 4
  call void @only_the_other_writes(ptr %a, ptr %a)
  %v = load i32, ptr %a, align 4
  %c = icmp eq i32 %v, 0
  br i1 %c, label %yes, label %no
yes:
  ret i32 1
no:
  ret i32 %x
}

; LangRef: `noreturn` "produces undefined behavior at runtime if the function ever does dynamically return".
define i32 @noreturn_returns(i32 %x) noreturn {
  ret i32 %x
}
