#include "llvm/IR/PassManager.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

bool dominatesUse(Value *V, BasicBlock *Succ, DominatorTree *DT) {
  for (User *U : V->users()) {
    if (isa<PHINode>(U)) continue;
    auto *I = dyn_cast<Instruction>(U);
    if (!I) continue;
    if (DT->dominates(Succ, I->getParent())) return true;
  }
  return false;
}

void getDependences(Value* V, BasicBlock* BB,
                    SmallPtrSet<Instruction*, 16> &Dependences,
                    SmallPtrSet<Value*, 16> &Visited) {
  if (!Visited.insert(V).second) return;

  auto *I = dyn_cast<Instruction>(V);
  if (!I || I->getParent() != BB) return;

  for (Value *Op : I->operands()) {
    auto *OpI = dyn_cast<Instruction>(Op);
    if (!OpI) continue;
    Dependences.insert(OpI);
    getDependences(OpI, BB, Dependences, Visited);
  }
}

void insertTransitiveDependences(BasicBlock* BB, BasicBlock* Succ,
                                 SmallPtrSet<Instruction*, 16> &Dependences,
                                 DominatorTree &DT,
                                 StringRef Suffix,
                                 DenseMap<Value*, Value*> &VMap) {
  auto InsertPt = Succ->getFirstInsertionPt();
  for (Instruction &I : *BB) {
    if (Dependences.count(&I) && dominatesUse(&I, Succ, &DT)) {
      Instruction *Clone = I.clone();
      Clone->setName(I.getName() + Suffix);
      Clone->insertBefore(InsertPt);
      for (unsigned i = 0; i < Clone->getNumOperands(); i++) {
        Value *Op = Clone->getOperand(i);
        if (VMap.count(Op))
          Clone->setOperand(i, VMap[Op]);
      }
      VMap[&I] = Clone;
    }
  }
}

void σ(Value* LHS, Value* RHS, BasicBlock* Succ, BasicBlock* BB,
       DominatorTree &DT, bool isTrueBranch) {
  bool sameValue = (LHS == RHS);
  StringRef Suffix = isTrueBranch ? ".t" : ".f";

  PHINode *SigmaLHS = PHINode::Create(LHS->getType(), 1, LHS->getName() + Suffix, Succ->begin());
  SigmaLHS->addIncoming(LHS, BB);

  PHINode *SigmaRHS = nullptr;
  if (!sameValue) {
    SigmaRHS = PHINode::Create(RHS->getType(), 1, RHS->getName() + Suffix, Succ->begin());
    SigmaRHS->addIncoming(RHS, BB);
  }

  DenseMap<Value*, Value*> VMap;
  VMap[LHS] = SigmaLHS;
  if (!sameValue) VMap[RHS] = SigmaRHS;

  SmallPtrSet<Value*, 16> VisitedLHS;
  SmallPtrSet<Instruction*, 16> DependencesLHS;
  if (auto *I = dyn_cast<Instruction>(LHS))
    if (I->getParent() == BB)
      DependencesLHS.insert(I);
  getDependences(LHS, BB, DependencesLHS, VisitedLHS);
  insertTransitiveDependences(BB, Succ, DependencesLHS, DT, Suffix, VMap);

  SmallPtrSet<Value*, 16> VisitedRHS;
  SmallPtrSet<Instruction*, 16> DependencesRHS;
    if (auto *I = dyn_cast<Instruction>(RHS))
      if (I->getParent() == BB)
        DependencesRHS.insert(I);
  getDependences(RHS, BB, DependencesRHS, VisitedRHS);
  insertTransitiveDependences(BB, Succ, DependencesRHS, DT, Suffix, VMap);
}
  
struct ESSAfier : public PassInfoMixin<ESSAfier> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM){
    DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);
    DominanceFrontier &DF = FAM.getResult<DominanceFrontierAnalysis>(F);
    
    for (BasicBlock &BB : F){
      auto *BI = dyn_cast<BranchInst>(BB.getTerminator());
      if (!BI || !BI->isConditional()) continue;

      Value *LHS, *RHS;
      if (auto *ICmp = dyn_cast<ICmpInst>(BI->getCondition())){
        LHS = ICmp->getOperand(0);
	RHS = ICmp->getOperand(1);
      } else continue;
      
      BasicBlock *TrueBranch = BI->getSuccessor(0);
      BasicBlock *FalseBranch = BI->getSuccessor(1);
      
      if (TrueBranch->getSinglePredecessor()) σ(LHS, RHS, TrueBranch, &BB, DT, true);
      if (FalseBranch->getSinglePredecessor()) σ(LHS, RHS, FalseBranch, &BB, DT, false);      
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


