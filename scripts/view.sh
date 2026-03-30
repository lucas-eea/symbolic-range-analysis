#!/bin/bash
set -e
mkdir -p tests/cfgs
clang -O1 -Xclang -disable-llvm-passes -fno-discard-value-names -emit-llvm -S tests/test.c -o tests/input.ll
opt -passes=mem2reg -S tests/input.ll -o tests/beforeESSAfier.ll
opt -passes=dot-cfg -disable-output tests/beforeESSAfier.ll
dot  -Tpng .test.dot -o tests/cfgs/before.png
opt -load-pass-plugin=build/ESSAfier.so -passes="ESSAfier" -S tests/beforeESSAfier.ll -o tests/afterESSAfier.ll
opt -passes=dot-cfg -disable-output tests/afterESSAfier.ll
dot -Tpng .test.dot -o tests/cfgs/after.png
rm .test.dot
