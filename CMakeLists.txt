cmake_minimum_required(VERSION 3.15)
project(LLVMSymbolicRanges)

find_package(LLVM REQUIRED CONFIG)

include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})
link_directories(${LLVM_LIBRARY_DIRS})

include(AddLLVM)

include_directories(include)

add_llvm_pass_plugin(SymbolicRanges
  lib/SymbolicRangeAnalysis.cpp
)
