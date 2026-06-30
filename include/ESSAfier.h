//===- ESSAfier.h - Extended-SSA form pass ----------------------*- C++ -*-===//
//
/// \file
/// Declares the ESSAfier pass, which inserts sigma nodes at conditional
/// branch targets to convert a function into Extended SSA form.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_ESSAFIER_H
#define LLVM_ESSAFIER_H

#include "llvm/IR/PassManager.h"

namespace llvm {

/// Converts a function to Extended SSA (ESSA) form by inserting sigma nodes
/// at the targets of conditional branches.
///
/// For each conditional branch on an ICmp, sigma nodes (which are implemented
/// as phi nodes with a single incoming value) are inserted at the start of
/// the true and false successor blocks.
/// Sigma-nodes split the live range of the compared variables at the branch
/// point, so that range analysis can assign each branch its own
/// SSA name and exploit the predicate — e.g. the true-branch sigma of \c x
/// in \c x < N carries the constraint \c x < N, enabling more precise range
/// information.
struct ESSAfier : public PassInfoMixin<ESSAfier> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
};

} // namespace llvm

#endif // LLVM_ESSAFIER_H
