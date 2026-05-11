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
                                   DenseMap<Value *, symboxes::SymRange> &St)
{
    if (auto *C = dyn_cast<ConstantInt>(V))
        return symboxes::SymRange::single(
            symboxes::SymExpr::num(C->getSExtValue()));

    auto It = St.find(V);
    if (It != St.end())
        return It->second;

    if (auto *Arg = dyn_cast<Argument>(V))
      return symboxes::SymRange::single(symboxes::SymExpr::sym(Arg));
    
    return symboxes::SymRange::bottom();
}

static symboxes::SymRange intervalBinOp(unsigned Opcode,
                                        const symboxes::SymRange &L,
                                        const symboxes::SymRange &R)
{
    if (L.isBottom || R.isBottom)
        return symboxes::SymRange::bottom();

    using SE = symboxes::SymExpr;

    switch (Opcode)
    {
        case Instruction::ICmp:
      return symboxes::SymRange::of(SE::num(0), SE::num(1));
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

symboxes::SymRange applyConstraint(symboxes::SymRange R,
                                   ICmpInst *Cmp,
                                   Value *SigmaVar,
                                   bool isTrueSide,
                                   DenseMap<Value *, symboxes::SymRange> &St) {
    using SE = symboxes::SymExpr;
    Value *A = Cmp->getOperand(0);
    Value *B = Cmp->getOperand(1);
    bool isA = (A == SigmaVar);

    auto Ra = getState(A, St);
    auto Rb = getState(B, St);
    
    switch (Cmp->getPredicate()) {
    case ICmpInst::ICMP_SGE:
      isTrueSide = !isTrueSide;
      [[fallthrough]];
    case ICmpInst::ICMP_SLT:
      if (isTrueSide)
	  return isA
	      ? symboxes::SymRange::of(Ra.Lower,
					 SE::mkMin(SE::sub(Rb.Upper, SE::num(1)), Ra.Upper))
	      : symboxes::SymRange::of(
					 SE::mkMax(SE::add(Ra.Lower, SE::num(1)), Rb.Lower),
                      Rb.Upper);
        else
	  return isA
	      ? symboxes::SymRange::of(SE::mkMax(Ra.Lower, Rb.Lower), Ra.Upper)
	      : symboxes::SymRange::of(Rb.Lower, SE::mkMin(Ra.Upper, Rb.Upper));
	
    case ICmpInst::ICMP_SLE:
      isTrueSide = !isTrueSide;
      [[fallthrough]];
    case ICmpInst::ICMP_SGT:
      if (isTrueSide)
	return isA
	  ? symboxes::SymRange::of(SE::mkMax(Ra.Lower, SE::add(Rb.Lower, SE::num(1))),
				 Ra.Upper)
      : symboxes::SymRange::of(Rb.Lower,
			         SE::mkMin(SE::sub(Ra.Upper, SE::num(1)), Rb.Upper));
      else
	return isA
	  ? symboxes::SymRange::of(Ra.Lower,
				   SE::mkMin(Ra.Upper, Rb.Upper))
      : symboxes::SymRange::of(SE::mkMax(Rb.Lower, Ra.Lower),Rb.Upper);
    default:
      return R;
    }
}

static symboxes::SymRange transfer(Instruction &I,
                                   DenseMap<Value *, symboxes::SymRange> &St)
{

    if (auto *Phi = dyn_cast<PHINode>(&I))
    {
        if (MDNode *MD = Phi->getMetadata("sigma"))
        {
            bool isTrueSide = cast<MDString>(MD->getOperand(0))->getString() == ".t";
            Value *Incoming = Phi->getIncomingValue(0);
            BasicBlock *PredBB = Phi->getIncomingBlock(0);
            auto R = getState(Incoming, St);

            if (auto *Br = dyn_cast<BranchInst>(PredBB->getTerminator()))
                if (Br->isConditional())
                    if (auto *Cmp = dyn_cast<ICmpInst>(Br->getCondition()))
                        R = applyConstraint(R, Cmp, Incoming, isTrueSide, St);
            return R;
        }
        auto R = symboxes::SymRange::bottom();
        for (Value *Op : Phi->incoming_values())
            R = R.join(getState(Op, St));
        return R;
    }

    if (auto *Bin = dyn_cast<BinaryOperator>(&I))
    {
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

namespace
{

    struct SymbolicRangeAnalysisAnnotator
        : PassInfoMixin<SymbolicRangeAnalysisAnnotator>
    {

        static constexpr int WIDEN_THRESHOLD = 3;

        PreservedAnalyses run(Module &M, ModuleAnalysisManager &)
        {
            for (Function &F : M)
            {
                if (F.isDeclaration())
                    continue;
                runOnFunction(F);
            }
            return PreservedAnalyses::all();
        }

    private:
        void runOnFunction(Function &F)
        {
            errs() << "=== Symbolic Range Analysis: " << F.getName() << " ===\n";

            DenseMap<Value *, symboxes::SymRange> State;
            DenseMap<Value *, int> IterCount;

            for (Argument &Arg : F.args())
                State[&Arg] =
                    symboxes::SymRange::single(symboxes::SymExpr::sym(&Arg));

            ReversePostOrderTraversal<Function *> RPOT(&F);

            bool Changed = true;
            while (Changed)
            {
                Changed = false;

                for (BasicBlock *BB : RPOT)
                {
                    for (Instruction &I : *BB)
                    {

                        if (isa<AllocaInst>(&I))
                            continue;

                        symboxes::SymRange NewR = transfer(I, State);

                        if (isa<PHINode>(&I))
                        {
                            int &Cnt = IterCount[&I];
                            ++Cnt;
                            if (Cnt > WIDEN_THRESHOLD)
                            {
                                auto &Old = State[&I];
                                if (!Old.isBottom)
                                    NewR = Old.widen(NewR);
                            }
                        }

                        auto &Old = State[&I];
                        if (!(NewR == Old))
                        {
                            Old = NewR;
                            Changed = true;
                        }
                    }
                }
            }

            for (BasicBlock &BB : F)
            {
                errs() << BB.getName() << ":\n";
                for (Instruction &I : BB)
                {
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
llvmGetPassPluginInfo()
{
    return {
        LLVM_PLUGIN_API_VERSION, "symbolicRangeAnalysis", LLVM_VERSION_STRING,
        [](PassBuilder &PB)
        {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement>)
                {
                    if (Name == "sra-annotator")
                    {
                        MPM.addPass(SymbolicRangeAnalysisAnnotator());
                        return true;
                    }
                    return false;
                });
        }};
}
