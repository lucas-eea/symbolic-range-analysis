#include "llvm/IR/PassManager.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallVector.h"

#include <queue>

using namespace llvm;

struct IntOverflowSanitizerPass
    : public PassInfoMixin<IntOverflowSanitizerPass> {

  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
};

static bool isOverflowOp(Instruction *I) {
  switch (I->getOpcode()) {
    case Instruction::Add:
    case Instruction::Sub:
    case Instruction::Mul:
    case Instruction::Shl:
      return true;
    default:
      return false;
  }
}

static bool isMemAllocCall(CallInst *CI) {
  if (!CI->getCalledFunction()) return false;
  StringRef N = CI->getCalledFunction()->getName();
  return N == "malloc" || N == "calloc" || N == "realloc" || N == "free";
}

static SetVector<Value*> computeTb(Function &F, AAResults &AA) {

  SetVector<Value*> Tb;
  std::queue<Value*> W;

  auto add = [&](Value *V) {
    if (V && Tb.insert(V))
      W.push(V);
  };

  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *CI = dyn_cast<CallInst>(&I)) {
        if (isMemAllocCall(CI)) {
          if (CI->getNumArgOperands() > 0)
            add(CI->getArgOperand(0));
        }
      }

      if (auto *SI = dyn_cast<StoreInst>(&I)) {
        add(SI->getPointerOperand());
        add(SI->getValueOperand());
      }

      if (auto *LI = dyn_cast<LoadInst>(&I)) {
        add(LI->getPointerOperand());
      }

      if (auto *GEP = dyn_cast<GetElementPtrInst>(&I)) {
        for (auto &Idx : GEP->indices())
          add(Idx.get());
        add(GEP);
      }
    }
  }

  while (!W.empty()) {
    Value *V = W.front();
    W.pop();

    if (auto *I = dyn_cast<Instruction>(V)) {

      for (Use &U : I->operands()) {
        Value *Op = U.get();
        if (!isa<Constant>(Op) && !isa<BasicBlock>(Op))
          add(Op);
      }
      
      BasicBlock *BB = I->getParent();
      for (auto *Pred : predecessors(BB)) {
        if (auto *Term = Pred->getTerminator()) {
          if (auto *Br = dyn_cast<BranchInst>(Term)) {
            if (Br->isConditional())
              add(Br->getCondition());
          }
        }
      }

      if (auto *LI = dyn_cast<LoadInst>(I)) {
        Value *Ptr = LI->getPointerOperand();

        for (auto &BB2 : F) {
          for (auto &I2 : BB2) {
            if (auto *SI = dyn_cast<StoreInst>(&I2)) {
              Value *SPtr = SI->getPointerOperand();

              if (AA.alias(Ptr, SPtr) != NoAlias)
                add(SPtr);
            }
          }
        }
      }

      if (auto *GEP = dyn_cast<GetElementPtrInst>(I)) {
        Value *Base = GEP->getPointerOperand();

        for (auto &BB2 : F) {
          for (auto &I2 : BB2) {
            if (auto *LI = dyn_cast<LoadInst>(&I2)) {
              if (AA.alias(Base, LI->getPointerOperand()) != NoAlias) {
                for (auto &Idx : GEP->indices())
                  add(Idx.get());
              }
            }
          }
        }
      }
    }
  }

  return Tb;
}

static Value *instrumentOverflow(Instruction *I, IRBuilder<> &IRB) {

  Intrinsic::ID ID;
  bool isSigned = false;

  switch (I->getOpcode()) {
    case Instruction::Add:
      ID = isSigned ? Intrinsic::sadd_with_overflow
                    : Intrinsic::uadd_with_overflow;
      break;
    case Instruction::Sub:
      ID = isSigned ? Intrinsic::ssub_with_overflow
                    : Intrinsic::usub_with_overflow;
      break;
    case Instruction::Mul:
      ID = isSigned ? Intrinsic::smul_with_overflow
                    : Intrinsic::umul_with_overflow;
      break;
    default:
      return nullptr;
  }

  Function *F = Intrinsic::getDeclaration(
      I->getModule(), ID, {I->getType()});

  return IRB.CreateCall(F, {I->getOperand(0), I->getOperand(1)});
}

PreservedAnalyses
IntOverflowSanitizerPass::run(Function &F,
                              FunctionAnalysisManager &FAM) {

  auto &AA = FAM.getResult<AAManager>(F);

  SetVector<Value*> Tb = computeTb(F, AA);

  SmallVector<Instruction*> ToInstrument;

  for (auto &BB : F) {
    for (auto &I : BB) {
      if (Tb.count(&I) && isOverflowOp(&I))
        ToInstrument.push_back(&I);
    }
  }

  if (ToInstrument.empty())
    return PreservedAnalyses::all();

  for (Instruction *I : ToInstrument) {

    IRBuilder<> IRB(I);

    Value *Res = instrumentOverflow(I, IRB);
    if (!Res) continue;

    Value *Result = IRB.CreateExtractValue(Res, 0);
    Value *Ovf    = IRB.CreateExtractValue(Res, 1);

    BasicBlock *OrigBB = I->getParent();

    SplitBlockAndInsertIfThen(
        Ovf, I,
        true);

    IRBuilder<> TrapBuilder(I->getNextNode());
    TrapBuilder.CreateIntrinsic(Intrinsic::trap, {}, {});

    I->replaceAllUsesWith(Result);
    I->eraseFromParent();
  }

  return PreservedAnalyses::none();
}
