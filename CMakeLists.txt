cmake_minimum_required(VERSION 3.15)
project(LLVMSymbolicRanges)

find_package(ZLIB)
find_package(LLVM REQUIRED CONFIG)

include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})
include(AddLLVM)
include_directories(include)

separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND "${LLVM_DEFINITIONS}")

add_llvm_pass_plugin(ESSAfier
  lib/ESSAfier.cpp
)
add_llvm_pass_plugin(SymbolicRanges
  lib/SymbolicRangeAnalysis.cpp
  lib/GiNaCGlue.cpp
)
add_executable(symboxes
  tests/testSymBoxes.cpp
  lib/GiNaCGlue.cpp
)

execute_process(
  COMMAND ${LLVM_TOOLS_BINARY_DIR}/llvm-config --libs core support
  OUTPUT_VARIABLE LLVM_LIBS
  OUTPUT_STRIP_TRAILING_WHITESPACE
)
execute_process(
  COMMAND ${LLVM_TOOLS_BINARY_DIR}/llvm-config --system-libs
  OUTPUT_VARIABLE LLVM_SYSTEM_LIBS
  OUTPUT_STRIP_TRAILING_WHITESPACE
)

target_compile_options(ESSAfier PRIVATE ${LLVM_DEFINITIONS_LIST})
target_compile_options(SymbolicRanges PRIVATE ${LLVM_DEFINITIONS_LIST} -frtti -fexceptions)

target_link_libraries(symboxes PRIVATE ${LLVM_LIBS} ${LLVM_SYSTEM_LIBS} ginac cln)
target_link_libraries(SymbolicRanges PRIVATE ginac cln)

target_compile_options(symboxes PRIVATE -frtti -fexceptions)
