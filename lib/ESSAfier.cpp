//===- ESSAfier.cpp - Extended-SSA form pass ------------------------------===//
//
/// \file
/// Implements the ESSAfier pass and registers it as `ESSAfier`.
//
//===----------------------------------------------------------------------===//

#include "ESSAfier.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Plugins/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include <map>
#include <set>

using namespace llvm;

static cl::opt<bool> SplitCriticalEdges(
    "essa-split-critical-edges", cl::init(true),
    cl::desc("Split critical edges out of conditional branches, so that every "
             "branch target can receive sigma nodes"));

/// Returns true if live ranges can be split along the edge \p BB -> \p
/// Target, that is, if that edge is the only way into \p Target.
static bool canSplitInto(BasicBlock *Target, BasicBlock *BB) {
  return Target != BB && Target->getSinglePredecessor() == BB;
}

/// Returns true if \p V may be renamed. Only integer values are renamed:
/// constants have the same value everywhere, and renaming pointers would
/// break intrinsics that need the original value, such as
/// llvm.lifetime.start.
static bool isRedefinable(Value *V) {
  return !isa<Constant>(V) && V->getType()->isIntegerTy();
}

/// Inserts a sigma node for each of \p Roots at the top of \p Branch, tagged
/// with !sigma \p Suffix, and renames every use of a root dominated by \p
/// Branch. A use in a phi node counts at the end of its incoming block.
static void insertPHIs(ArrayRef<Value *> Roots, BasicBlock *Branch,
                       BasicBlock *BB, StringRef Suffix, DominatorTree &DT) {
  LLVMContext &Ctx = Branch->getContext();
  MDNode *MD = MDNode::get(Ctx, {MDString::get(Ctx, Suffix)});
  for (Value *Root : Roots) {
    PHINode *Sigma = PHINode::Create(Root->getType(), 1,
                                     Root->getName() + Suffix, Branch->begin());
    Sigma->addIncoming(Root, BB);
    Sigma->setMetadata("sigma", MD);
    for (Use &U : make_early_inc_range(Root->uses())) {
      auto *UI = dyn_cast<Instruction>(U.getUser());
      if (!UI || UI == Sigma)
        continue;
      BasicBlock *UseBB = UI->getParent();
      if (auto *Phi = dyn_cast<PHINode>(UI)) {
        // Sigma nodes at the top of Branch keep the original value.
        if (UseBB == Branch)
          continue;
        UseBB = Phi->getIncomingBlock(U);
      }
      if (DT.dominates(Branch, UseBB))
        U.set(Sigma);
    }
  }
}

/// Collects into \p Copies the dependents in \p Pred that are used in blocks
/// dominated by \p Branch, together with the chain of instructions that
/// leads to them from one of \p Roots. These values get a copy in \p Branch.
static void getDominatedDependences(const std::map<Value *, Value *> &Pred,
                                    ArrayRef<Value *> Roots,
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
      // Walk back to the root, which gets a sigma node instead of a copy.
      Value *Cur = I;
      while (Cur && !is_contained(Roots, Cur)) {
        if (Instruction *CurI = dyn_cast<Instruction>(Cur))
          Copies.insert(CurI);
        auto It = Pred.find(Cur);
        Cur = (It != Pred.end()) ? It->second : nullptr;
      }
    }
  }
}

/// Returns true if \p I can be duplicated at a branch target, that is, if it
/// computes a value from its operands only.
static bool isCopyable(const Instruction *I) {
  return !isa<PHINode>(I) && !isa<ICmpInst>(I) && !I->isTerminator() &&
         !I->mayReadOrWriteMemory() && !I->mayHaveSideEffects() &&
         !I->getType()->isVoidTy();
}

/// Collects into \p Dependents the copyable instructions of \p BB that
/// depend transitively on \p V, without going through \p Roots. \p Pred maps
/// each dependent to the value it was reached from.
static void getDependences(Value *V, ArrayRef<Value *> Roots,
                           std::set<Instruction *> &Dependents,
                           std::map<Value *, Value *> &Pred, BasicBlock *BB) {
  if (!V || isa<Constant>(V))
    return;
  for (User *U : V->users()) {
    Instruction *I = dyn_cast<Instruction>(U);
    if (!I || !isCopyable(I) || is_contained(Roots, I))
      continue;
    if (I->getParent() != BB)
      continue;
    if (Dependents.count(I))
      continue;
    Dependents.insert(I);
    Pred[I] = V;
    getDependences(I, Roots, Dependents, Pred, BB);
  }
}

/// Inserts copies of \p ToBeCopied after the phi nodes of \p Branch, in
/// their order in \p BB. Operands of the copies, and of the instructions of
/// \p Branch, are rewritten to use the copies (x.t = b + y becomes
/// x.t = b.t + y). Returns the map from each original to its copy.
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

/// Inserts sigma nodes for \p Operands, and copies of the values computed
/// from them in \p BB, at the top of \p TrueBranch and \p FalseBranch, the
/// successors of the conditional branch that ends \p BB.
static void insertSigmaNodes(ArrayRef<Value *> Operands, BasicBlock *TrueBranch,
                             BasicBlock *FalseBranch, BasicBlock *BB,
                             DominatorTree &DT) {
  bool SplitTB = canSplitInto(TrueBranch, BB);
  bool SplitFB = canSplitInto(FalseBranch, BB);
  SmallVector<Value *, 4> Roots;
  for (Value *V : Operands)
    if (isRedefinable(V) && !is_contained(Roots, V))
      Roots.push_back(V);
  if (Roots.empty() || (!SplitTB && !SplitFB))
    return;

  std::set<Instruction *> Dependents;
  std::map<Value *, Value *> Pred;
  for (Value *Root : Roots)
    getDependences(Root, Roots, Dependents, Pred, BB);

  std::set<Instruction *> ToBeCopiedTB, ToBeCopiedFB;
  if (SplitTB)
    getDominatedDependences(Pred, Roots, ToBeCopiedTB, TrueBranch, DT);
  if (SplitFB)
    getDominatedDependences(Pred, Roots, ToBeCopiedFB, FalseBranch, DT);

  std::map<Instruction *, Instruction *> CopiesTB =
      copyAndInsert(ToBeCopiedTB, TrueBranch, BB, ".t");
  std::map<Instruction *, Instruction *> CopiesFB =
      copyAndInsert(ToBeCopiedFB, FalseBranch, BB, ".f");

  if (SplitTB)
    insertPHIs(Roots, TrueBranch, BB, ".t", DT);
  if (SplitFB)
    insertPHIs(Roots, FalseBranch, BB, ".f", DT);

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
    for (Use &U : make_early_inc_range(OG->uses())) {
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

/// Collects into \p Out the integer comparisons that make up the branch
/// condition \p Cond: the condition itself, or the leaves of logical and,
/// or and not (including their select forms), as in `i < n && i < 100`.
static void collectComparisons(Value *Cond, SmallVectorImpl<ICmpInst *> &Out,
                               unsigned Depth = 0) {
  using namespace PatternMatch;
  Value *A, *B;
  if (auto *Cmp = dyn_cast<ICmpInst>(Cond)) {
    if (Cmp->getOperand(0)->getType()->isIntegerTy())
      Out.push_back(Cmp);
  } else if (Depth < 4 && (match(Cond, m_LogicalAnd(m_Value(A), m_Value(B))) ||
                           match(Cond, m_LogicalOr(m_Value(A), m_Value(B))))) {
    collectComparisons(A, Out, Depth + 1);
    collectComparisons(B, Out, Depth + 1);
  } else if (Depth < 4 && match(Cond, m_Not(m_Value(A)))) {
    collectComparisons(A, Out, Depth + 1);
  }
}

PreservedAnalyses ESSAfier::run(Function &F, FunctionAnalysisManager &FAM) {
  DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);

  // A branch target with other predecessors cannot hold sigma nodes, since
  // they would be wrong on the other incoming paths. Splitting the edge gives
  // the target a block of its own.
  if (SplitCriticalEdges) {
    SmallVector<std::pair<Instruction *, unsigned>, 16> Edges;
    for (BasicBlock &BB : F)
      if (auto *BI = dyn_cast<BranchInst>(BB.getTerminator()))
        if (BI->isConditional()) {
          SmallVector<ICmpInst *, 4> Cmps;
          collectComparisons(BI->getCondition(), Cmps);
          if (Cmps.empty())
            continue;
          for (unsigned I = 0; I < 2; ++I)
            if (isCriticalEdge(BI, I))
              Edges.push_back({BI, I});
        }
    for (auto [TI, I] : Edges)
      SplitCriticalEdge(TI, I, CriticalEdgeSplittingOptions(&DT));
  }

  for (BasicBlock &BB : F) {
    auto *BI = dyn_cast<BranchInst>(BB.getTerminator());
    if (!BI || !BI->isConditional())
      continue;

    SmallVector<ICmpInst *, 4> Cmps;
    collectComparisons(BI->getCondition(), Cmps);
    if (Cmps.empty())
      continue;
    SmallVector<Value *, 8> Operands;
    for (ICmpInst *Cmp : Cmps)
      Operands.append({Cmp->getOperand(0), Cmp->getOperand(1)});

    BasicBlock *TrueBranch = BI->getSuccessor(0);
    BasicBlock *FalseBranch = BI->getSuccessor(1);

    insertSigmaNodes(Operands, TrueBranch, FalseBranch, &BB, DT);
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
