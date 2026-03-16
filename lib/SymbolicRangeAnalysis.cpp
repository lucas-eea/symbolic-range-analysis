#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/ScalarEvolution.h"


using namespace llvm;

struct SymbolicRange {
    const SCEV *Lower;
    const SCEV *Upper;

    void print(raw_ostream &OS) const {
        OS << "[";
        Lower->print(OS);
        OS << ", ";
        Upper->print(OS);
        OS << "]";
    }
};

namespace {

struct SymbolicRangeAnalysisAnnotator : PassInfoMixin<SymbolicRangeAnalysisAnnotator> {
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM) {
    auto &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

    DenseMap<Value *, SymbolicRange> State;

    for (auto &F : M) {
        if (F.isDeclaration()) continue;

        ScalarEvolution &SE = FAM.getResult<ScalarEvolutionAnalysis>(F);

        for (BasicBlock &BB : F) {
            for (Instruction &I : BB) {
                const SCEV *Scev = SE.getSCEV(&I);
                SymbolicRange R = { Scev, Scev };
                State[&I] = R;
                errs() << "Value: " << I << " -> Range: ";
                R.print(errs());
                errs() << "\n";
            }
        }
    }
    return PreservedAnalyses::all();
}
};
} 
extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, "SymbolicRangeAnalysis", LLVM_VERSION_STRING,
        [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                    if (Name == "sra-annotator") {
                        MPM.addPass(SymbolicRangeAnalysisAnnotator());
                        return true;
                    }
                    return false;
                });
        }
    };
}
