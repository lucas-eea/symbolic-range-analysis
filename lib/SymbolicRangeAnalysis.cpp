#include "SymBoxes.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

static symboxes::SymRange getState(Value *V,
                                   DenseMap<Value *, symboxes::SymRange> &St) {
    if (auto *C = dyn_cast<ConstantInt>(V))
        return symboxes::SymRange::single(
            symboxes::SymExpr::num(C->getSExtValue()));

    auto It = St.find(V);
    if (It != St.end())
        return It->second;

    return symboxes::SymRange::bottom();
}

static symboxes::SymRange intervalBinOp(unsigned Opcode,
                                        const symboxes::SymRange &L,
                                        const symboxes::SymRange &R) {
    if (L.isBottom || R.isBottom)
        return symboxes::SymRange::bottom();

    using SE = symboxes::SymExpr;

    switch (Opcode) {
    case Instruction::Add:
        return symboxes::SymRange::of(SE::add(L.Lower, R.Lower),
                                      SE::add(L.Upper, R.Upper));

    case Instruction::Sub:
        return symboxes::SymRange::of(SE::sub(L.Lower, R.Upper),
                                      SE::sub(L.Upper, R.Lower));

    case Instruction::Mul: {
        auto ll = SE::mul(L.Lower, R.Lower);
        auto lu = SE::mul(L.Lower, R.Upper);
        auto ul = SE::mul(L.Upper, R.Lower);
        auto uu = SE::mul(L.Upper, R.Upper);
        auto lo = SE::mkMin(SE::mkMin(ll, lu), SE::mkMin(ul, uu));
        auto hi = SE::mkMax(SE::mkMax(ll, lu), SE::mkMax(ul, uu));
        return symboxes::SymRange::of(lo, hi);
    }

    default:
        return symboxes::SymRange::full();
    }
}

static symboxes::SymRange transfer(Instruction &I,
                                   DenseMap<Value *, symboxes::SymRange> &St) {
    if (auto *Phi = dyn_cast<PHINode>(&I)) {
        auto R = symboxes::SymRange::bottom();
        for (Value *Op : Phi->incoming_values())
            R = R.join(getState(Op, St));
        return R;
    }

    if (auto *Bin = dyn_cast<BinaryOperator>(&I)) {
        auto L = getState(Bin->getOperand(0), St);
        auto R = getState(Bin->getOperand(1), St);
        return intervalBinOp(Bin->getOpcode(), L, R);
    }

    if (auto *Cast = dyn_cast<CastInst>(&I))
        return getState(Cast->getOperand(0), St);

    if (auto *C = dyn_cast<ConstantInt>(&I))
        return symboxes::SymRange::single(
            symboxes::SymExpr::num(C->getSExtValue()));

    return symboxes::SymRange::full();
}

namespace {

struct SymbolicRangeAnalysisAnnotator
    : PassInfoMixin<SymbolicRangeAnalysisAnnotator> {

    static constexpr int WIDEN_THRESHOLD = 3;

    PreservedAnalyses run(Module &M, ModuleAnalysisManager &) {
        for (Function &F : M) {
            if (F.isDeclaration())
                continue;
            runOnFunction(F);
        }
        return PreservedAnalyses::all();
    }

private:
    void runOnFunction(Function &F) {
        errs() << "=== Symbolic Range Analysis: " << F.getName() << " ===\n";

        DenseMap<Value *, symboxes::SymRange> State;
        DenseMap<Value *, int>                IterCount;

        for (Argument &Arg : F.args())
            State[&Arg] =
                symboxes::SymRange::single(symboxes::SymExpr::sym(&Arg));

        ReversePostOrderTraversal<Function *> RPOT(&F);

        bool Changed = true;
        while (Changed) {
            Changed = false;

            for (BasicBlock *BB : RPOT) {
                for (Instruction &I : *BB) {

                    if (isa<AllocaInst>(&I))
                        continue;

                    symboxes::SymRange NewR = transfer(I, State);

                    if (isa<PHINode>(&I)) {
                        int &Cnt = IterCount[&I];
                        ++Cnt;
                        if (Cnt > WIDEN_THRESHOLD) {
                            auto &Old = State[&I];
                            if (!Old.isBottom)
                                NewR = Old.widen(NewR);
                        }
                    }

                    auto &Old = State[&I];
                    if (!(NewR == Old)) {
                        Old     = NewR;
                        Changed = true;
                    }
                }
            }
        }

        for (BasicBlock &BB : F) {
            errs() << BB.getName() << ":\n";
            for (Instruction &I : BB) {
                errs() << "  " << I << "\n    => ";
                if (State.count(&I))
                    State[&I].print(errs());
                else
                    errs() << "bot";
                errs() << "\n";
            }
        }
        errs() << "\n";
    }
};

}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, "symbolicRangeAnalysis", LLVM_VERSION_STRING,
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
        }};
}