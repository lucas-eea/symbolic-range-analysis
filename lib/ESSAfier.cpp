//===- ESSAfier.cpp - Extended-SSA form pass ------------------------------===//

#include "ESSAfier.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Plugins/PassPlugin.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include <map>
#include <set>

using namespace llvm;

/// Inserts the phi nodes that represent sigma nodes
/// with correct metadata.
static void insertPHIs(Value *LHS, Value *RHS, BasicBlock *Branch,
                       BasicBlock *BB, StringRef Suffix) {
  if (!Branch->getSinglePredecessor())
    return;

  PHINode *SigmaLHS = PHINode::Create(LHS->getType(), 1,
                                      LHS->getName() + Suffix,
                                      Branch->begin());
  PHINode *SigmaRHS = PHINode::Create(RHS->getType(), 1,
                                      RHS->getName() + Suffix,
                                      Branch->begin());
  SigmaLHS->addIncoming(LHS, BB);
  SigmaRHS->addIncoming(RHS, BB);

  LLVMContext &Ctx = SigmaLHS->getContext();
  Metadata *MDLHS[] = {MDString::get(Ctx, Suffix)};
  Metadata *MDRHS[] = {MDString::get(Ctx, Suffix)};
  SigmaLHS->setMetadata("sigma", MDNode::get(Ctx, MDLHS));
  SigmaRHS->setMetadata("sigma", MDNode::get(Ctx, MDRHS));

  for (Instruction &I : *Branch) {
    if (isa<PHINode>(I))
      continue;
    for (Use &U : I.operands()) {
      if (U.get() == LHS)
        U.set(SigmaLHS);
      if (U.get() == RHS)
        U.set(SigmaRHS);
    }
  }
}

/// Split the live range of a variable v along the
/// edge l' -> l, if:
/// 1) v depend transitively on a or b from cond(a,b)
/// 2) v is used in a label dominated by l
/// (we do this by inserting a copy of v).
static void getDominatedDependences(const std::map<Value *, Value *> &Pred,
                                    std::set<Instruction *> &Copies,
                                    BasicBlock *Branch, DominatorTree &DT) {
  for (const auto &Entry : Pred) {
    Instruction *I = dyn_cast<Instruction>(Entry.first);
    if (!I)
      continue;
    if (any_of(I->users(), [&](User *U) {
          Instruction *UI = dyn_cast<Instruction>(U);
          return UI && DT.dominates(Branch, UI->getParent());
        })) {
      Value *Cur = I;
      while (Cur) {
        if (Instruction *CurI = dyn_cast<Instruction>(Cur))
          Copies.insert(CurI);
        auto It = Pred.find(Cur);
        Cur = (It != Pred.end()) ? It->second : nullptr;
      }
    }
  }
}

/// Recursively collect instructions that depend transitively
/// on \p V. Results are added to \p Dependents; \p Pred maps
/// each dependent instruction to the value it was reached from.
static void getDependences(Value *V, std::set<Instruction *> &Dependents,
                           std::map<Value *, Value *> &Pred, BasicBlock *BB) {
  if (!V || isa<Constant>(V))
    return;
  for (User *U : V->users()) {
    Instruction *I = dyn_cast<Instruction>(U);
    if (!I || isa<PHINode>(I) || isa<ICmpInst>(I))
      continue;
    if (I->getParent() != BB)
      continue;
    if (Dependents.count(I))
      continue;
    Dependents.insert(I);
    Pred[I] = V;
    getDependences(I, Dependents, Pred, BB);
  }
}

/// Insert copies from \p ToBeCopied into \p Branch, inserting
/// them after the last phi node.
/// Operands of the clones are rewritten to refer to other clones
/// (e.g. x.t = b + y --> x.t = b.t + y)
/// Iteration follows the original order in \p BB to respect
/// def-use ordering.
static std::map<Instruction *, Instruction *>
copyAndInsert(const std::set<Instruction *> &ToBeCopied, BasicBlock *Branch,
              BasicBlock *BB, StringRef Suffix) {
  std::map<Instruction *, Instruction *> Copies;

  for (Instruction *I : ToBeCopied) {
    Instruction *Copy = I->clone();
    Copy->setName(I->getName() + Suffix);
    Copies[I] = Copy;
  }

  BasicBlock::iterator InsertPoint = Branch->getFirstNonPHIIt();

  for (Instruction &I : *BB) {
    if (!ToBeCopied.count(&I))
      continue;

    Instruction *Copy = Copies[&I];

    for (Use &Op : Copy->operands()) {
      if (Instruction *OpI = dyn_cast<Instruction>(Op.get()))
        if (Copies.count(OpI))
          Op.set(Copies[OpI]);
    }
    Copy->insertBefore(*Branch, InsertPoint);
  }

  for (auto It = InsertPoint; It != Branch->end(); ++It) {
    for (Use &Op : It->operands()) {
      if (Instruction *OpI = dyn_cast<Instruction>(Op.get()))
        if (Copies.count(OpI))
          Op.set(Copies[OpI]);
    }
  }

  return Copies;
}

/// Orchestrate E-SSA construction for a single conditional branch.
/// Insert sigma nodes for \p LHS and \p RHS at the top of each
/// true and false branch, with \p BB as the single incoming block.
/// Sigma nodes are represented with phi nodes tagged with a "sigma"
/// + \p Suffix metadata for downstream passes.
static void insertSigmaNodes(Value *LHS, Value *RHS, BasicBlock *TrueBranch,
                             BasicBlock *FalseBranch, BasicBlock *BB,
                             DominatorTree &DT) {
  std::set<Instruction *> DependentsOnLHS, DependentsOnRHS;
  std::map<Value *, Value *> Pred;

  getDependences(LHS, DependentsOnLHS, Pred, BB);
  getDependences(RHS, DependentsOnRHS, Pred, BB);

  std::set<Instruction *> ToBeCopiedTB, ToBeCopiedFB;
  getDominatedDependences(Pred, ToBeCopiedTB, TrueBranch, DT);
  getDominatedDependences(Pred, ToBeCopiedFB, FalseBranch, DT);

  std::map<Instruction *, Instruction *> CopiesTB =
      copyAndInsert(ToBeCopiedTB, TrueBranch, BB, ".t");
  std::map<Instruction *, Instruction *> CopiesFB =
      copyAndInsert(ToBeCopiedFB, FalseBranch, BB, ".f");

  insertPHIs(LHS, RHS, TrueBranch, BB, ".t");
  insertPHIs(LHS, RHS, FalseBranch, BB, ".f");

  std::map<Instruction *, Instruction *> AllCopies = CopiesTB;
  AllCopies.insert(CopiesFB.begin(), CopiesFB.end());

  SSAUpdater Updater;

  for (auto &[OG, Copy] : AllCopies) {
    bool InTB = CopiesTB.count(OG);
    bool InFB = CopiesFB.count(OG);
    Updater.Initialize(OG->getType(), OG->getName());
    if (InTB && InFB) {
      Updater.AddAvailableValue(TrueBranch, CopiesTB[OG]);
      Updater.AddAvailableValue(FalseBranch, CopiesFB[OG]);
    } else if (InTB) {
      Updater.AddAvailableValue(TrueBranch, CopiesTB[OG]);
      Updater.AddAvailableValue(BB, OG);
    } else if (InFB) {
      Updater.AddAvailableValue(FalseBranch, CopiesFB[OG]);
      Updater.AddAvailableValue(BB, OG);
    } else {
      continue;
    }
    for (Use &U : OG->uses()) {
      auto *UserInst = dyn_cast<Instruction>(U.getUser());
      if (!UserInst)
        continue;
      BasicBlock *UserBB = UserInst->getParent();
      if (UserBB == BB || UserBB == TrueBranch || UserBB == FalseBranch)
        continue;
      Updater.RewriteUse(U);
    }
  }
}

PreservedAnalyses ESSAfier::run(Function &F, FunctionAnalysisManager &FAM) {
  DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);

  for (BasicBlock &BB : F) {
    auto *BI = dyn_cast<BranchInst>(BB.getTerminator());
    if (!BI || !BI->isConditional())
      continue;

    Value *LHS, *RHS;
    if (auto *ICmp = dyn_cast<ICmpInst>(BI->getCondition())) {
      LHS = ICmp->getOperand(0);
      RHS = ICmp->getOperand(1);
    } else {
      continue;
    }

    BasicBlock *TrueBranch = BI->getSuccessor(0);
    BasicBlock *FalseBranch = BI->getSuccessor(1);

    insertSigmaNodes(LHS, RHS, TrueBranch, FalseBranch, &BB, DT);
  }
  return PreservedAnalyses::none();
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
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
            });
      }};
}
