#!/bin/bash

# Runs the FileCheck tests. Usage: scripts/run_tests.sh (BUILD=<dir> to use
# another build directory).

BUILD=${BUILD:-build}
ESSAFIER=$BUILD/ESSAfier.so
SRA=$BUILD/SymbolicRanges.so
SRACVP=$BUILD/SRACVP.so

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
    echo "PASS"
    ((PASS++))
  else
    echo "FAIL"
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
  opt -load-pass-plugin=$ESSAFIER -load-pass-plugin=$SRA \
      -passes='function(ESSAfier),sra-annotator<x=0:15>' \
      -S 2>/dev/null)
run "symbolic_range_analysis_fig7" tests/ll/symbolic_range_analysis_fig7.ll "$output"

output=$(compile_to_ll tests/c/transitive_dependences_handling.c | \
  opt -load-pass-plugin=$ESSAFIER -load-pass-plugin=$SRA \
      -passes='function(ESSAfier),sra-annotator' \
      -S 2>/dev/null)
run "sra_min_arithmetic" tests/ll/sra_min_arithmetic.ll "$output"

for name in narrowing_loops casts_and_bits wraparound loops_and_widening guard_facts interprocedural loop_variant_symbols exact_values; do
  output=$(compile_to_ll tests/c/$name.c | \
    opt -load-pass-plugin=$ESSAFIER -load-pass-plugin=$SRA \
        -passes='function(ESSAfier),sra-annotator' \
        -S 2>/dev/null)
  run "$name" tests/ll/$name.ll "$output"
done

# Code whose && chains SimplifyCFG first turns into one branch.
for name in unsigned_window; do
  output=$(compile_to_ll tests/c/$name.c | \
    opt -load-pass-plugin=$ESSAFIER -load-pass-plugin=$SRA \
        -passes='function(simplifycfg),function(ESSAfier),sra-annotator' \
        -S 2>/dev/null)
  run "$name" tests/ll/$name.ll "$output"
done

echo "=== ESSAfier on IR regression tests (output must verify) ==="

# The CHECK lines exercise the multiple-predecessor logic, so critical-edge
# splitting is off there; with it on, the output must still verify.
for f in tests/ir/*.ll; do
  output=$(opt -load-pass-plugin=$ESSAFIER -essa-split-critical-edges=false \
      -passes='function(ESSAfier),verify' -S "$f" 2>&1)
  run "$(basename "$f" .ll)" "$f" "$output"
  if ! opt -load-pass-plugin=$ESSAFIER -passes='function(ESSAfier),verify' \
      -disable-output "$f" 2>/dev/null; then
    echo "FAIL: $(basename "$f" .ll) with critical-edge splitting"
    ((FAIL++))
  fi
done

echo "=== SRA on IR tests (e.g. optimized loop shapes C at -O0 cannot produce) ==="

for f in tests/sra-ir/*.ll; do
  output=$(opt -load-pass-plugin=$ESSAFIER -load-pass-plugin=$SRA \
      -passes='function(ESSAfier),sra-annotator,verify' -S "$f" 2>&1)
  run "$(basename "$f" .ll)" "$f" "$output"
done

echo "=== sra-cvp and simplifycfg: printf removal ==="

for name in test05 test08; do
  output=$(compile_to_ll tests/c/$name.c | \
    opt -load-pass-plugin=$SRACVP -sra-cvp-plugin-dir=$BUILD \
        -passes='sra-cvp,function(simplifycfg)' -S 2>/dev/null)
  run "$name" tests/ll/$name.ll "$output"
done

echo "=== SymBoxes unit tests ==="

output=$(./$BUILD/symboxes 2>/dev/null)
run "symboxes" tests/ll/symboxes.txt "$output"

TOTAL=$((PASS + FAIL))
echo "=== Results: $PASS/$TOTAL passed ==="
[ "$FAIL" -eq 0 ]
