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
