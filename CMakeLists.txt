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
# The pinned LLVM's passes, and what's claimed and planned about them: the checks on claims and on
# docs/llvm-verification-tasks.md, in Python, and then the inventory derived again from LLVM's source, opt and
# llc, byte for byte. Neither runs Lean.
add_test(NAME llvm_scope COMMAND ${CMAKE_SOURCE_DIR}/tests/llvm_scope_test.py)
add_test(NAME llvm_scope_check COMMAND ${CMAKE_SOURCE_DIR}/tests/llvm_scope.py check)
set_tests_properties(llvm_scope llvm_scope_check PROPERTIES TIMEOUT 600)
add_test(NAME superopt COMMAND ${CMAKE_SOURCE_DIR}/tests/superopt.py $<TARGET_FILE:ir-lean>)
add_test(NAME names COMMAND ${CMAKE_SOURCE_DIR}/tests/names.sh)
# The experimental undef and freeze semantics against LangRef's examples and Alive2, compiled from copies in a
# temporary directory, one Lean or Alive2 process at a time, each Lean process capped at 2 GB and 300 s.
add_test(NAME undef_freeze COMMAND ${CMAKE_SOURCE_DIR}/tests/undef_freeze.sh)
set_tests_properties(undef_freeze PROPERTIES TIMEOUT 900)
add_test(NAME verify COMMAND ${CMAKE_SOURCE_DIR}/tests/verify.py $<TARGET_FILE:ir-lean>)
# What counts as a certificate: the gate on stored and broken results, in Python, and then a corpus of
# wrong and right rewrites through tools/verify.py, one Lean process at a time.
add_test(NAME verify_negative_static COMMAND ${CMAKE_SOURCE_DIR}/tests/verify_negative.py --tier static)
add_test(
    NAME verify_negative
    COMMAND
        ${CMAKE_SOURCE_DIR}/tests/verify_negative.py --tier live --tool $<TARGET_FILE:ir-lean>
        --min-available-mb 4000
)
# Alone, so its Lean process has the memory to itself, and longer than every case's limits together.
set_tests_properties(verify_negative PROPERTIES RUN_SERIAL TRUE TIMEOUT 900)
# Replay certificates challenged from outside: manifests and processes tools/binding.py has to refuse or
# call unknown, in Python; every rewrite those tests use against Alive2, one capped process at a time; and
# IRLean on poison and flag rewrites, with tools/binding.py on real opt runs, alone, as it runs Lean.
add_test(NAME replay_challenge_static COMMAND ${CMAKE_SOURCE_DIR}/tests/replay_challenge.py --tier static)
add_test(NAME replay_challenge_alive COMMAND ${CMAKE_SOURCE_DIR}/tests/replay_challenge.py --tier alive)
add_test(NAME replay_challenge COMMAND ${CMAKE_SOURCE_DIR}/tests/replay_challenge.py --tier live)
set_tests_properties(replay_challenge_static replay_challenge_alive PROPERTIES TIMEOUT 600)
set_tests_properties(replay_challenge PROPERTIES RUN_SERIAL TRUE TIMEOUT 1800)
# A certificate bound to its IR, the opt run and the toolchain, and refused when any of them doesn't
# match: one instcombine rewrite, and the cases of mismatched evidence, one capped Lean process at a time.
add_test(NAME binding COMMAND ${CMAKE_SOURCE_DIR}/tests/binding.py)
# Alone, since each of its Lean processes takes up to 3.5 GB. It hashes the Lean toolchain on every check,
# so it gets more time than it takes on a fast disk, about 5 minutes.
set_tests_properties(binding PROPERTIES RUN_SERIAL TRUE TIMEOUT 1800)
# The scorer, on two small tests rather than llvm-project: an instance counts only when tools/binding.py
# binds its bundle in the same run. The rules in Python first, then the scorer itself, alone, since it runs
# tools/binding.py, one capped Lean process at a time.
add_test(NAME passes_static COMMAND ${CMAKE_SOURCE_DIR}/tests/passes_test.py --tier static)
add_test(NAME passes COMMAND ${CMAKE_SOURCE_DIR}/tests/passes_test.py --tier live)
set_tests_properties(passes PROPERTIES RUN_SERIAL TRUE TIMEOUT 1800)
# The semantic contracts against the model, compiled from copies in a temporary directory, one Lean
# process at a time, each capped at 2 GB and 300 s by the script itself.
add_test(NAME contracts COMMAND ${CMAKE_SOURCE_DIR}/tests/contracts.sh)
set_tests_properties(contracts PROPERTIES TIMEOUT 900)
# The refinement contract against its cases, the same way: copies in a temporary directory, one Lean
# process at a time, each capped at 2 GB and 300 s by the script itself.
add_test(NAME refine COMMAND ${CMAKE_SOURCE_DIR}/tests/refine.sh)
set_tests_properties(refine PROPERTIES TIMEOUT 900)
# A model of LLVM's simplifyAddInst against the pinned C++ and opt, compiled in a temporary directory, one
# Lean process at a time, each capped at 2 GB and 300 s by the script itself.
add_test(NAME cpp_correspondence COMMAND ${CMAKE_SOURCE_DIR}/tests/cpp_correspondence.py)
set_tests_properties(cpp_correspondence PROPERTIES TIMEOUT 900)
# The rewrites proved for every width against the model, the same way: copies in a temporary directory,
# one Lean process at a time, each capped at 2 GB and 300 s by the script itself.
add_test(NAME generic_rewrites COMMAND ${CMAKE_SOURCE_DIR}/tests/generic_rewrites.sh)
set_tests_properties(generic_rewrites PROPERTIES TIMEOUT 900)
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
# llama.cpp's q4_K rewrite. x86's dot-product intrinsics against the processor, which needs AVX-512 VNNI, so
# it skips without it. Those and vector bitcasts against Alive2 and LLVM's constant folder, on any processor.
# And the rewrite's proofs, which need llama.cpp's source, so they're labeled `llama`, run in
# `nix develop .#llama`, and skip in any other shell.
add_test(
    NAME x86
    COMMAND
        sh -c "grep -q avx512_vnni /proc/cpuinfo || exit 77; exec \"$@\"" sh
        ${CMAKE_SOURCE_DIR}/tests/differential.py $<TARGET_FILE:ir-lean> ${CMAKE_SOURCE_DIR}/tests/real/x86.ll
        --strict --runs 400
)
add_test(NAME x86check COMMAND ${CMAKE_SOURCE_DIR}/tests/x86check.py $<TARGET_FILE:ir-lean>)
add_test(NAME llama COMMAND ${CMAKE_SOURCE_DIR}/tests/llama.py $<TARGET_FILE:ir-lean>)
set_tests_properties(x86 llama PROPERTIES SKIP_RETURN_CODE 77)
set_tests_properties(x86 x86check llama PROPERTIES TIMEOUT 1800)
set_tests_properties(llama PROPERTIES LABELS llama)
# ctest has no limit of its own, and a Lean run that never ends would otherwise hang these.
set_tests_properties(
    differential
    vectors_pointers
    undefined
    fuzz
    llvm
    superopt
    verify
    PROPERTIES TIMEOUT 1800
)
set_tests_properties(zlib_slow PROPERTIES LABELS slow)
# CI's test jobs: the longest tests apart, so they don't wait for each other. Each job is named after its
# label and runs the tests with it, and a test with none of these runs in the job for the rest. See
# docs/testing.md.
set_tests_properties(passes PROPERTIES LABELS passes)
set_tests_properties(binding PROPERTIES LABELS binding)
set_tests_properties(llvm PROPERTIES LABELS llvm)
set_tests_properties(
    verify_negative
    replay_challenge
    contracts
    refine
    undef_freeze
    generic_rewrites
    cpp_correspondence
    PROPERTIES LABELS semantics
)
# These compile the same modules, and the second finds them in the cache.
set_tests_properties(zlib_slow PROPERTIES DEPENDS zlib)
# Formatters, linters and language servers. The lint test comes first, so the language servers can find the
# generated modules it writes.
add_test(NAME lint COMMAND ${CMAKE_SOURCE_DIR}/tests/lint.sh)
add_test(NAME lsp COMMAND ${CMAKE_SOURCE_DIR}/tests/lsp.py)
set_tests_properties(lint lsp PROPERTIES LABELS lint)
set_tests_properties(lsp PROPERTIES DEPENDS lint TIMEOUT 1800)
