cmake_minimum_required(VERSION 3.20)
project(ir-lean LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE RelWithDebInfo)
endif()

find_package(LLVM REQUIRED CONFIG)

add_executable(ir-lean src/main.cpp src/Emitter.cpp)
target_include_directories(ir-lean SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
# LLVM gives its definitions as one string.
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
target_compile_definitions(ir-lean PRIVATE ${LLVM_DEFINITIONS_LIST})
target_compile_options(ir-lean PRIVATE -Wall -Wextra -fno-rtti)
llvm_config(ir-lean USE_SHARED core irreader support)

# Tests need the Lean library: run `lake build` first.
enable_testing()
add_test(NAME opcheck COMMAND ${CMAKE_SOURCE_DIR}/tests/opcheck.py $<TARGET_FILE:ir-lean>)
add_test(NAME gepcheck COMMAND ${CMAKE_SOURCE_DIR}/tests/gepcheck.py $<TARGET_FILE:ir-lean>)
add_test(
    NAME differential
    COMMAND
        ${CMAKE_SOURCE_DIR}/tests/differential.py $<TARGET_FILE:ir-lean>
        ${CMAKE_SOURCE_DIR}/tests/real/bi_reverse.c ${CMAKE_SOURCE_DIR}/tests/real/calls.c
        ${CMAKE_SOURCE_DIR}/tests/real/memory.c --bound fib=20 --bound is_even=200 --bound is_odd=200
)
add_test(
    NAME vectors_pointers
    COMMAND
        ${CMAKE_SOURCE_DIR}/tests/differential.py $<TARGET_FILE:ir-lean>
        ${CMAKE_SOURCE_DIR}/tests/real/pointers.c ${CMAKE_SOURCE_DIR}/tests/real/vectors.ll
        ${CMAKE_SOURCE_DIR}/tests/real/heap.ll ${CMAKE_SOURCE_DIR}/tests/real/gep.ll
        ${CMAKE_SOURCE_DIR}/tests/real/promises.ll --strict
)
add_test(
    NAME undefined
    COMMAND
        ${CMAKE_SOURCE_DIR}/tests/differential.py $<TARGET_FILE:ir-lean> ${CMAKE_SOURCE_DIR}/tests/real/ub.ll
        --runs 3 --expect-ub
)
add_test(
    NAME model_stops
    COMMAND
        ${CMAKE_SOURCE_DIR}/tests/differential.py $<TARGET_FILE:ir-lean>
        ${CMAKE_SOURCE_DIR}/tests/real/stops.ll --runs 3 --expect-stop
)
# `--expect-ub` has to say these aren't undefined. Comparing the output keeps any other failure from passing.
add_test(
    NAME model_stops_are_not_undefined
    COMMAND
        ${CMAKE_SOURCE_DIR}/tests/differential.py $<TARGET_FILE:ir-lean>
        ${CMAKE_SOURCE_DIR}/tests/real/stops.ll --runs 3 --expect-ub
)
set_tests_properties(
    model_stops_are_not_undefined
    PROPERTIES PASS_REGULAR_EXPRESSION "not undefined: .*model stop: freezePoison"
)
# Each memory error has to stop for its own reason, not just any undefined behavior, so this checks them all.
add_test(
    NAME memory_errors
    COMMAND
        ${CMAKE_SOURCE_DIR}/tests/differential.py $<TARGET_FILE:ir-lean>
        ${CMAKE_SOURCE_DIR}/tests/real/memory_errors.ll --runs 3 --expect-ub
)
string(
    JOIN ", "
    memory_error_reasons
    "undefined: badAccess in @dangling_stack 3"
    "undefined: badAccess in @heap_past_end 3"
    "undefined: badAccess in @load_before_start 3"
    "undefined: badAccess in @load_null 3"
    "undefined: badAccess in @load_past_end 3"
    "undefined: badAccess in @store_past_end 3"
    "undefined: badAccess in @use_after_free 3"
    "undefined: badAccess in @wrong_provenance 3"
    "undefined: badFree in @double_free 3"
    "undefined: badFree in @free_interior 3"
    "undefined: badFree in @free_stack 3"
    "undefined: misaligned in @load_misaligned 3"
    "undefined: overlappingCopy in @memcpy_overlapping 3"
    "undefined: writeToConstant in @store_to_constant 3"
)
set_tests_properties(
    memory_errors
    PROPERTIES
        PASS_REGULAR_EXPRESSION
            "14 functions: 42 calls stopped, 0 returned a value\nbecause of: ${memory_error_reasons}\n"
        FAIL_REGULAR_EXPRESSION "not undefined|left out|nothing tested"
        TIMEOUT 1800
)
add_test(NAME emitter COMMAND ${CMAKE_SOURCE_DIR}/tests/emitter.sh $<TARGET_FILE:ir-lean>)
add_test(NAME fuzz COMMAND ${CMAKE_SOURCE_DIR}/tests/fuzz.py $<TARGET_FILE:ir-lean>)
add_test(NAME proofs COMMAND ${CMAKE_SOURCE_DIR}/tests/proofs.sh $<TARGET_FILE:ir-lean>)
add_test(NAME llvm COMMAND ${CMAKE_SOURCE_DIR}/tests/llvm.py $<TARGET_FILE:ir-lean>)
add_test(NAME superopt COMMAND ${CMAKE_SOURCE_DIR}/tests/superopt.py $<TARGET_FILE:ir-lean>)
add_test(NAME names COMMAND ${CMAKE_SOURCE_DIR}/tests/names.sh)
add_test(
    NAME zlib
    COMMAND
        ${CMAKE_SOURCE_DIR}/tests/zlib.sh $<TARGET_FILE:ir-lean> --only harness_ --runs 10 --slow
        harness_slow=0
)
# These run far enough for `deflate` to slide its window, which takes the longest. Skip with `ctest -LE slow`.
add_test(
    NAME zlib_slow
    COMMAND ${CMAKE_SOURCE_DIR}/tests/zlib.sh $<TARGET_FILE:ir-lean> --runs 1 --only harness_slow
)
set_tests_properties(zlib zlib_slow PROPERTIES TIMEOUT 5400)
# ctest has no limit of its own, and a Lean run that never ends would otherwise hang these.
set_tests_properties(
    differential
    vectors_pointers
    undefined
    fuzz
    llvm
    superopt
    PROPERTIES TIMEOUT 1800
)
set_tests_properties(zlib_slow PROPERTIES LABELS slow)
# These compile the same modules, and the second finds them in the cache.
set_tests_properties(zlib_slow PROPERTIES DEPENDS zlib)
# Formatters, linters and language servers. The lint test comes first, so the language servers can find the
# generated modules it writes.
add_test(NAME lint COMMAND ${CMAKE_SOURCE_DIR}/tests/lint.sh)
add_test(NAME lsp COMMAND ${CMAKE_SOURCE_DIR}/tests/lsp.py)
set_tests_properties(lint lsp PROPERTIES LABELS lint)
set_tests_properties(lsp PROPERTIES DEPENDS lint TIMEOUT 1800)
