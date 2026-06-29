#!/bin/bash
set -e

mkdir -p build
cd build
cmake -G Ninja .. \
  -DLLVM_DIR=${LLVM_DIR:-"$(llvm-config --prefix)/lib/cmake/llvm"}
ninja
