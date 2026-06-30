//===- SymbolicRangeAnalysis.h - Symbolic range analysis pass ---*- C++ -*-===//
//
/// \file
/// Declares the SymbolicRangeAnalysis pass, which annotates every instruction
/// in a module with !srange metadata containing its symbolic integer range.
///
/// Concrete ranges for function arguments can be supplied at pipeline
/// construction time via the pass parameter syntax:
///   sra-annotator<argname=lo:hi,...>
/// For example: sra-annotator<x=0:15,n=1:100>
/// Arguments without an explicit range remain symbolic (treated as unknowns).
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SYMBOLIC_RANGE_ANALYSIS_H
#define LLVM_SYMBOLIC_RANGE_ANALYSIS_H

#include "llvm/IR/PassManager.h"
#include <cstdint>
#include <map>
#include <string>

namespace llvm {

/// Annotates each instruction with !srange metadata encoding its symbolic
/// integer range, computed by fixpoint iteration over a symbolic interval
/// domain.
struct SymbolicRangeAnalysis : public PassInfoMixin<SymbolicRangeAnalysis> {
  /// Maps argument names to concrete [lo, hi] bounds supplied by the user.
  using ArgRangeMap = std::map<std::string, std::pair<int64_t, int64_t>>;

  ArgRangeMap ArgRanges;

  SymbolicRangeAnalysis() = default;
  explicit SymbolicRangeAnalysis(ArgRangeMap Ranges)
      : ArgRanges(std::move(Ranges)) {}

  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);
};

} // namespace llvm

#endif // LLVM_SYMBOLIC_RANGE_ANALYSIS_H
