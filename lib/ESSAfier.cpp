#include "llvm/IR/PassManager.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include <map>

using namespace llvm;

void insertPHIs(Value* LHS, Value* RHS, BasicBlock* Branch,
		BasicBlock* BB, StringRef Suffix){


  if (!Branch->getSinglePredecessor()) return;
  
  PHINode *SigmaLHS = PHINode::Create(LHS->getType(),
					1,
					LHS->getName() + Suffix,
					Branch->begin());
  PHINode *SigmaRHS = PHINode::Create(RHS->getType(),
					1,
					RHS->getName() + Suffix,
					Branch->begin());
  SigmaLHS->addIncoming(LHS, BB);
  SigmaRHS->addIncoming(RHS, BB);

  LLVMContext &CtxLHS = SigmaLHS->getContext();
  LLVMContext &CtxRHS = SigmaRHS->getContext();
  Metadata *MDLHS[] = {MDString::get(CtxLHS, Suffix)};
  Metadata *MDRHS[] = {MDString::get(CtxRHS, Suffix)};
  SigmaLHS->setMetadata("sigma", MDNode::get(CtxLHS, {MDLHS}));
  SigmaRHS->setMetadata("sigma", MDNode::get(CtxRHS, {MDRHS}));
  
  
  for (Instruction &I : *Branch){
    if (isa<PHINode>(&I)) continue;
    for (Use &U : I.operands()){
      if (U.get() == LHS) U.set(SigmaLHS);
      if (U.get() == RHS) U.set(SigmaRHS);
    }
  }
}

void getDominatedDependences(std::map<Value*, Value*> Pred,
					       std::set<Instruction*> &Copies,
					       BasicBlock* Branch,
					       DominatorTree &DT){
  for (auto &[Key, P] : Pred){
    Instruction *I = dyn_cast<Instruction>(Key);
    if (!I) continue;
    if (any_of(I->users(), [&](User *U){
      Instruction *UI = dyn_cast<Instruction>(U);
      return UI && DT.dominates(Branch, UI->getParent());
    })) {
      Value *Cur = I;
      while (Cur){
	if (Instruction *I = dyn_cast<Instruction>(Cur))
	  Copies.insert(I);
	auto It = Pred.find(Cur);
	Cur = (It != Pred.end()) ? It->second : nullptr;
      }
    }
  }
}

void getDependences(Value *V, std::set<Instruction*> &Dependents,
		    std::map<Value*, Value*> &Pred, BasicBlock *BB){
  if (!V || isa<Constant>(V)) return;
  for (User *U : V->users()){
    Instruction *I = dyn_cast<Instruction>(U);
    if (!I || isa<PHINode>(I) || isa<ICmpInst>(I)) continue;
    if (I->getParent() != BB) continue;
    if (Dependents.count(I)) continue;
    Dependents.insert(I);
    Pred[I] = V;
    getDependences(I, Dependents, Pred, BB);
  }
}

std::map<Instruction*, Instruction*> copyAndInsert(
		                     std::set<Instruction*> ToBeCopied,
		                     BasicBlock* Branch,
		                     BasicBlock* BB,
		                     StringRef Suffix){
  std::map<Instruction*, Instruction*> copies;
  
  for (Instruction *I : ToBeCopied){
    Instruction *copy = I->clone();
    copy->setName(I->getName() + Suffix);
    copies[I] = copy;
  }

  BasicBlock::iterator insertPoint = Branch->getFirstNonPHIIt();    

  for (Instruction &I : *BB){
    if (!ToBeCopied.count(&I)) continue;

    Instruction *copy = copies[&I];

    for (Use &Op : copy->operands()){
      if (Instruction *OpI = dyn_cast<Instruction>(Op.get()))
	if (copies.count(OpI))
	  Op.set(copies[OpI]);
    }
    copy->insertBefore(*Branch, insertPoint);
  }

  for (auto it  = insertPoint; it != Branch->end(); ++it) {
    for (Use &Op : it->operands()){
      if (Instruction *OpI = dyn_cast<Instruction>(Op.get()))
	if (copies.count(OpI))
	  Op.set(copies[OpI]);
    }
  }

  return copies;
}

void σ(Value* LHS, Value* RHS,
       BasicBlock* TrueBranch,
       BasicBlock* FalseBranch,
       BasicBlock* BB,
       DominatorTree &DT) {

  std::set<Instruction*> DependentsOnLHS, DependentsOnRHS;
  std::map<Value*, Value*> Pred;
  std::set<Instruction*> toBeCopied;

  getDependences(LHS,DependentsOnLHS, Pred, BB);
  getDependences(RHS, DependentsOnRHS, Pred, BB);

  std::set<Instruction *> toBeCopiedTB, toBeCopiedFB;
  getDominatedDependences(Pred, toBeCopiedTB, TrueBranch, DT);
  getDominatedDependences(Pred, toBeCopiedFB, FalseBranch, DT);

  std::map<Instruction*, Instruction*> copiesTB, copiesFB, allCopies;  
  copiesTB = copyAndInsert(toBeCopiedTB, TrueBranch, BB, ".t");
  copiesFB = copyAndInsert(toBeCopiedFB, FalseBranch, BB, ".f");

  insertPHIs(LHS, RHS, TrueBranch, BB, ".t");
  insertPHIs(LHS, RHS, FalseBranch, BB, ".f");
  
  allCopies = copiesTB;
  allCopies.insert(copiesFB.begin(), copiesFB.end());

  SSAUpdater Updater;
  
  for (auto &[OG, Copy] : allCopies){
    bool inTB = copiesTB.count(OG);
    bool inFB = copiesTB.count(OG);
    Updater.Initialize(OG->getType(), OG->getName());
    if (inTB && inFB){
      Updater.AddAvailableValue(TrueBranch, copiesTB[OG]);
      Updater.AddAvailableValue(FalseBranch, copiesFB[OG]);
    } else if (inTB){
      Updater.AddAvailableValue(TrueBranch, copiesTB[OG]);
      Updater.AddAvailableValue(BB, OG);
    } else if (inFB){
      Updater.AddAvailableValue(FalseBranch, copiesFB[OG]);
      Updater.AddAvailableValue(BB, OG);
    } else continue;
    for (Use &U : OG->uses()) {
      auto *UserInst = cast<Instruction>(U.getUser());
      BasicBlock *UserBB = UserInst->getParent();

      if (UserBB == BB || UserBB == TrueBranch || UserBB == FalseBranch)
        continue;

      Updater.RewriteUse(U);
    }
  }
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
      
      σ(LHS, RHS, TrueBranch, FalseBranch, &BB, DT);
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


