; Promises the code keeps, and things they don't rule out, so the checks must leave these alone. These
; run against native code, failing if any input is skipped.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare ptr @malloc(i64)
declare void @free(ptr)

; `readonly` is about this pointer, not the memory: another pointer can write it.
define internal void @writes_through_the_other(ptr readonly %p, ptr %q, i32 %x) {
  store i32 %x, ptr %q, align 4
  ret void
}

define i32 @readonly_with_another_pointer(i32 %x) {
  %a = alloca i32, align 4
  call void @writes_through_the_other(ptr %a, ptr %a, i32 %x)
  %v = load i32, ptr %a, align 4
  ret i32 %v
}

; Once the call is over, so is the promise.
define internal ptr @returns_readonly(ptr readonly %p) {
  ret ptr %p
}

define i32 @readonly_over_after_the_call(i32 %x) {
  %a = alloca i32, align 4
  %q = call ptr @returns_readonly(ptr %a)
  store i32 %x, ptr %q, align 4
  %v = load i32, ptr %q, align 4
  ret i32 %v
}

; `readnone` only rules out dereferencing it: its address is still fine.
define internal i64 @address_of_readnone(ptr readnone %p) {
  %v = ptrtoint ptr %p to i64
  ret i64 %v
}

define i32 @readnone_address(i32 %x) {
  %a = alloca i32, align 4
  %v = call i64 @address_of_readnone(ptr %a)
  %c = icmp eq i64 %v, 0
  %r = select i1 %c, i32 0, i32 %x
  ret i32 %r
}

; `writeonly` allows reading what was written.
define internal i32 @writes_then_reads(ptr writeonly %p, i32 %x) {
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

define i32 @writeonly_read_after(i32 %x) {
  %a = alloca i32, align 4
  %r = call i32 @writes_then_reads(ptr %a, i32 %x)
  ret i32 %r
}

; `initializes` allows reading what it wrote, and leaves it behind.
define internal i32 @initializes_then_reads(ptr initializes((0, 4)) %p, i32 %x) {
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

define i32 @initializes_written(i32 %x) {
  %a = alloca i32, align 4
  %r = call i32 @initializes_then_reads(ptr %a, i32 %x)
  %v = load i32, ptr %a, align 4
  %s = add i32 %r, %v
  ret i32 %s
}

; Past its range, `initializes` says nothing.
define internal void @initializes_first_half(ptr initializes((0, 4)) %p) {
  store i32 1, ptr %p, align 4
  ret void
}

define i32 @initializes_leaves_the_rest(i32 %x) {
  %a = alloca [2 x i32], align 4
  %b = getelementptr i32, ptr %a, i64 1
  store i32 %x, ptr %b, align 4
  call void @initializes_first_half(ptr %a)
  %v = load i32, ptr %b, align 4
  ret i32 %v
}

; Storing an uncaptured pointer is fine if nothing uses it afterwards. So is using it during the call.
define internal i32 @stores_and_reads(ptr captures(none) %p, ptr %to) {
  store ptr %p, ptr %to, align 8
  %q = load ptr, ptr %to, align 8
  %v = load i32, ptr %q, align 4
  ret i32 %v
}

define i32 @captures_none_during_the_call(i32 %x) {
  %a = alloca i32, align 4
  %slot = alloca ptr, align 8
  store i32 %x, ptr %a, align 4
  %r = call i32 @stores_and_reads(ptr %a, ptr %slot)
  ret i32 %r
}

; After the call, the same memory is still reachable through the caller's own pointer.
define internal void @takes_uncaptured(ptr captures(none) %p, i32 %x) {
  store i32 %x, ptr %p, align 4
  ret void
}

define i32 @captures_none_with_the_original(i32 %x) {
  %a = alloca i32, align 4
  call void @takes_uncaptured(ptr %a, i32 %x)
  %v = load i32, ptr %a, align 4
  ret i32 %v
}

define internal ptr @returns_for_reading(ptr captures(address, read_provenance) %p) {
  ret ptr %p
}

define i32 @read_provenance_read_after(i32 %x) {
  %a = alloca i32, align 4
  store i32 %x, ptr %a, align 4
  %q = call ptr @returns_for_reading(ptr %a)
  %v = load i32, ptr %q, align 4
  ret i32 %v
}

; `memory(...)` always allows a function's own allocas and reading constants.
@constant = constant i32 5

define internal i32 @allocas_and_constants(i32 %x) memory(none) {
  %a = alloca i32, align 4
  store i32 %x, ptr %a, align 4
  %v = load i32, ptr %a, align 4
  %k = load i32, ptr @constant, align 4
  %s = add i32 %v, %k
  ret i32 %s
}

define i32 @memory_none_allocas_and_constants(i32 %x) {
  %r = call i32 @allocas_and_constants(i32 %x)
  ret i32 %r
}

; `memory(argmem: write)` allows reading back what it wrote.
define internal i32 @writes_argument(ptr %p, i32 %x) memory(argmem: write) {
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

define i32 @memory_write_read_after(i32 %x) {
  %a = alloca i32, align 4
  %r = call i32 @writes_argument(ptr %a, i32 %x)
  ret i32 %r
}

; A narrow `memory(...)` is over when the call is, so callers can do what they like.
define internal i32 @reads_argument(ptr %p) memory(argmem: read) {
  %v = load i32, ptr %p, align 4
  ret i32 %v
}

define i32 @memory_over_after_the_call(i32 %x) {
  %a = alloca i32, align 4
  store i32 0, ptr %a, align 4
  %r = call i32 @reads_argument(ptr %a)
  store i32 %x, ptr %a, align 4
  %v = load i32, ptr %a, align 4
  %s = add i32 %r, %v
  ret i32 %s
}

; `nofree` is about this pointer: another one can free the same memory.
define internal void @frees_the_other(ptr nofree %p, ptr %q) {
  call void @free(ptr %q)
  ret void
}

define i32 @nofree_with_another_pointer(i32 %x) {
  %p = call ptr @malloc(i64 4)
  call void @frees_the_other(ptr %p, ptr %p)
  ret i32 %x
}

; A `noalias` result that's new in the call.
define internal noalias ptr @makes_new() {
  %p = call noalias ptr @malloc(i64 4)
  ret ptr %p
}

define i32 @noalias_result_new(i32 %x) {
  %p = call ptr @makes_new()
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  call void @free(ptr %p)
  ret i32 %v
}

declare void @llvm.assume(i1)

define i32 @assume_nonnull_of_a_real_pointer(i32 %x) {
  %a = alloca i32, align 4
  call void @llvm.assume(i1 true) [ "nonnull"(ptr %a) ]
  ret i32 %x
}

; Every bundle the model has, kept: an alignment with and without an offset, one that isn't a power of two on null,
; `noundef` on an argument, and the two that promise nothing.
define i32 @assume_bundles_kept(i32 %x) {
  %a = alloca [4 x i32], align 16
  %p = getelementptr inbounds i8, ptr %a, i64 4
  call void @llvm.assume(i1 true) [ "align"(ptr %p, i64 4), "align"(ptr %p, i32 16, i64 4) ]
  call void @llvm.assume(i1 true) [ "align"(ptr null, i64 3), "align"(ptr null, i64 0) ]
  call void @llvm.assume(i1 true) [ "noundef"(i32 %x), "cold"(), "ignore"(ptr %a, i32 %x) ]
  ret i32 %x
}

; A pointer through an indirect call still finds its function, even with tags on it.
define internal i32 @target(i32 %x) {
  ret i32 %x
}

define internal i32 @calls_it(ptr readonly %f, i32 %x) {
  %r = call i32 %f(i32 %x)
  ret i32 %r
}

define i32 @tagged_function_pointer(i32 %x) {
  %r = call i32 @calls_it(ptr @target, i32 %x)
  ret i32 %r
}

define internal ptr @returns_it(ptr returned %p) {
  ret ptr %p
}

define i32 @returned_kept(i32 %x) {
  %a = alloca i32, align 4
  %q = call ptr @returns_it(ptr %a)
  store i32 %x, ptr %q, align 4
  %v = load i32, ptr %a, align 4
  ret i32 %v
}

; `initializes` says nothing about bytes outside its range, even through the same pointer.
define internal i32 @reads_past_initializes(ptr initializes((0, 4)) %p) {
  store i32 1, ptr %p, align 4
  %q = getelementptr i8, ptr %p, i64 4
  %v = load i32, ptr %q, align 4
  ret i32 %v
}

define i32 @initializes_read_outside_the_range(i32 %x) {
  %a = alloca [2 x i32], align 4
  %b = getelementptr i32, ptr %a, i64 1
  store i32 %x, ptr %b, align 4
  %r = call i32 @reads_past_initializes(ptr %a)
  ret i32 %r
}

; `memory(read, argmem: readwrite)` lets arguments be written and anything be read.
@global = global i32 3

define internal void @writes_argument_reads_global(ptr %p) memory(read, argmem: readwrite) {
  %v = load i32, ptr @global, align 4
  store i32 %v, ptr %p, align 4
  ret void
}

define i32 @memory_read_argmem_readwrite(i32 %x) {
  %a = alloca i32, align 4
  call void @writes_argument_reads_global(ptr %a)
  %v = load i32, ptr %a, align 4
  %s = add i32 %v, %x
  ret i32 %s
}

; `inaccessiblemem` is what `malloc` and `free` need.
define internal ptr @wraps_malloc() memory(inaccessiblemem: readwrite, errnomem: write) {
  %p = call ptr @malloc(i64 4)
  ret ptr %p
}

define internal void @wraps_free(ptr %p) memory(argmem: readwrite, inaccessiblemem: readwrite) {
  call void @free(ptr %p)
  ret void
}

define i32 @allocator_wrappers(i32 %x) {
  %p = call ptr @wraps_malloc()
  store i32 %x, ptr %p, align 4
  %v = load i32, ptr %p, align 4
  call void @wraps_free(ptr %p)
  ret i32 %v
}

define internal i1 @is_it_null(ptr captures(address_is_null) %p) {
  %c = icmp eq ptr %p, null
  ret i1 %c
}

define i32 @address_is_null_asks_that(i32 %x) {
  %a = alloca i32, align 4
  %c = call i1 @is_it_null(ptr %a)
  %r = select i1 %c, i32 0, i32 %x
  ret i32 %r
}

define internal i64 @its_address(ptr captures(address) %p) {
  %v = ptrtoint ptr %p to i64
  ret i64 %v
}

define i32 @captures_address_looks_at_it(i32 %x) {
  %a = alloca i32, align 4
  %v = call i64 @its_address(ptr %a)
  %c = icmp eq i64 %v, 0
  %r = select i1 %c, i32 0, i32 %x
  ret i32 %r
}

; The caller's own pointer was never restricted.
define internal void @takes_it(ptr captures(none) %p) {
  ret void
}

define i32 @own_pointer_after_captures_none(i32 %x) {
  %a = alloca i32, align 4
  call void @takes_it(ptr %a)
  %v = ptrtoint ptr %a to i64
  %c = icmp eq i64 %v, 0
  %r = select i1 %c, i32 0, i32 %x
  ret i32 %r
}
