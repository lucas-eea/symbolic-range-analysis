#ifndef LLVM_SYMBOLIC_RANGES_H
#define LLVM_SYMBOLIC_RANGES_H

#include "llvm/IR/PassManager.h"

namespace llvm {
class SymbolicRangeAnalysis : public PassInfoMixin<SymbolicRangeAnalysis> {
public:
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);
};
}

#endif
