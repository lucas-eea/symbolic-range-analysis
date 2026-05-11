opt -load-pass-plugin=./build/ESSAfier.so     -load-pass-plugin=./build/SymbolicRanges.so     -passes="function(ESSAfier),sra-annotator"     -disable-output tests/ll/branches.ll 2>&1 | FileCheck tests/ll/branches.ll

