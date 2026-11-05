cmake_minimum_required(VERSION 3.20)
project(llvm-lean LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE RelWithDebInfo)
endif()

find_package(LLVM REQUIRED CONFIG)

add_executable(llvm-lean src/main.cpp src/Emitter.cpp)
target_include_directories(llvm-lean SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
target_compile_definitions(llvm-lean PRIVATE ${LLVM_DEFINITIONS})
target_compile_options(llvm-lean PRIVATE -Wall -Wextra -fno-rtti)
llvm_config(llvm-lean USE_SHARED core irreader support)

# Tests need the Lean library: run `lake build` first.
enable_testing()
add_test(NAME opcheck COMMAND ${CMAKE_SOURCE_DIR}/tests/opcheck.py $<TARGET_FILE:llvm-lean>)
add_test(NAME differential COMMAND ${CMAKE_SOURCE_DIR}/tests/differential.py $<TARGET_FILE:llvm-lean>
  ${CMAKE_SOURCE_DIR}/tests/real/bi_reverse.c ${CMAKE_SOURCE_DIR}/tests/real/calls.c
  ${CMAKE_SOURCE_DIR}/tests/real/memory.c
  --bound fib=20 --bound is_even=200 --bound is_odd=200)
add_test(NAME vectors_pointers COMMAND ${CMAKE_SOURCE_DIR}/tests/differential.py $<TARGET_FILE:llvm-lean>
  ${CMAKE_SOURCE_DIR}/tests/real/pointers.c ${CMAKE_SOURCE_DIR}/tests/real/vectors.ll
  ${CMAKE_SOURCE_DIR}/tests/real/heap.ll --strict)
add_test(NAME undefined COMMAND ${CMAKE_SOURCE_DIR}/tests/differential.py $<TARGET_FILE:llvm-lean>
  ${CMAKE_SOURCE_DIR}/tests/real/ub.ll --runs 3 --expect-ub)
add_test(NAME fuzz COMMAND ${CMAKE_SOURCE_DIR}/tests/fuzz.py $<TARGET_FILE:llvm-lean>)
add_test(NAME names COMMAND ${CMAKE_SOURCE_DIR}/tests/names.sh)
add_test(NAME zlib COMMAND ${CMAKE_SOURCE_DIR}/tests/zlib.sh $<TARGET_FILE:llvm-lean>
  --only harness_ --runs 10 --slow harness_slow=0)
# About 20 minutes: these run far enough for `deflate` to slide its window. Skip with `ctest -LE slow`.
add_test(NAME zlib_slow COMMAND ${CMAKE_SOURCE_DIR}/tests/zlib.sh $<TARGET_FILE:llvm-lean> --runs 1
  --only harness_slow)
set_tests_properties(zlib zlib_slow PROPERTIES TIMEOUT 3600)
set_tests_properties(zlib_slow PROPERTIES LABELS slow)
