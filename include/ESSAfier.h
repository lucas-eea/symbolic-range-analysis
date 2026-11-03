//===- ESSAfier.h - Extended-SSA form pass ----------------------*- C++ -*-===//
//
/// \file
/// Declares the ESSAfier pass, which converts a function into Extended SSA
/// (e-SSA) form.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_ESSAFIER_H
#define LLVM_ESSAFIER_H

#include "llvm/IR/PassManager.h"

namespace llvm {

/// Converts a function to e-SSA form.
///
/// For each conditional branch on integer comparisons, the pass inserts a
/// sigma node for every compared value at the top of the true and the false
/// successor. A sigma node is a phi node with a single incoming value, tagged
/// with !sigma metadata (".t" or ".f"). Uses dominated by the successor are
/// renamed to the sigma node, so each side of the branch has its own name for
/// the value. In `if (x < N)`, for example, the true side's copy of `x` is
/// known to be less than `N`.
struct ESSAfier : public PassInfoMixin<ESSAfier> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
};

} // namespace llvm

#endif // LLVM_ESSAFIER_H
