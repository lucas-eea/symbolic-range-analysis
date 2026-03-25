#include "llvm/IR/PassManager.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

struct ESSAfier : public PassInfoMixin<ESSAfier> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM){
    for (BasicBlock &BB : F){
      auto *BI = dyn_cast<BranchInst>(BB.getTerminator());
      if (!BI || !BI->isConditional()) continue;

      Value *LHS, *RHS;
      if (auto *ICmp = dyn_cast<ICmpInst>(BI->getCondition())){
        LHS = ICmp->getOperand(0);
	RHS = ICmp->getOperand(1);
      } else if (auto *FCmp = dyn_cast<FCmpInst>(BI->getCondition())){
        LHS = FCmp->getOperand(0);
	RHS = FCmp->getOperand(1);
      } else continue;

      errs() << "LHS: " << *LHS << "\n";
      errs() << "RHS: " << *RHS << "\n";
    }
    return PreservedAnalyses::all();
  }
};

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, "ESSA", LLVM_VERSION_STRING,
        [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                    if (Name == "ESSAfier") {
                        FPM.addPass(ESSAfier());
                        return true;
                    }
                    return false;
                }
	    );
        }
    };
}


