#!/bin/bash

ESSAFIER=build/ESSAfier.so
SRA=build/SymbolicRanges.so

PASS=0
FAIL=0

compile_to_ll() {
  clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone -fno-discard-value-names "$1" -o - 2>/dev/null | \
    opt -passes=mem2reg -S 2>/dev/null
}

run() {
  local label=$1
  local check_file=$2
  local output=$3

  echo "--- $label ---"
  echo "$output"
  echo ""
  if echo "$output" | FileCheck "$check_file" 2>/dev/null; then
    echo "✅ Pass"
    ((PASS++))
  else
    echo "❌ Fail"
    ((FAIL++))
  fi
  echo ""
}

echo "=== ESSAfier ==="

output=$(compile_to_ll tests/c/branches.c | \
  opt -load-pass-plugin=$ESSAFIER -passes=ESSAfier -S 2>/dev/null)
run "branches" tests/ll/branches.ll "$output"

output=$(compile_to_ll tests/c/transitive_dependences_handling.c | \
  opt -load-pass-plugin=$ESSAFIER -passes=ESSAfier -S 2>/dev/null)
run "transitive_dependences_handling" tests/ll/transitive_dependences_handling.ll "$output"

echo "=== Symbolic Range Analysis (x=[0,15]) ==="

output=$(compile_to_ll tests/c/symbolic_range_analysis_fig7.c | \
  opt -load-pass-plugin=$ESSAFIER -passes=ESSAfier \
      -load-pass-plugin=$SRA -passes='sra-annotator<x=0:15>' \
      -S 2>/dev/null)
run "symbolic_range_analysis_fig7" tests/ll/symbolic_range_analysis_fig7.ll "$output"

echo "=== SymBoxes unit tests ==="

output=$(./build/symboxes 2>/dev/null)
run "symboxes" tests/ll/symboxes.txt "$output"

TOTAL=$((PASS + FAIL))
echo "=== Results: $PASS/$TOTAL passed ==="
