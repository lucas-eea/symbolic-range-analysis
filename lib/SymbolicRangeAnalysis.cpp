//===- SymbolicRangeAnalysis.cpp - Symbolic range analysis pass -----------===//

#include "SymbolicRangeAnalysis.h"
#include "SymBoxes.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Plugins/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

static constexpr int WidenThreshold = 3;

/// Returns the symbolic range for \p V, consulting \p St first.
/// Constants are folded to single intervals.
/// Arguments that are not into \p St yet return a symbolic singleton.
/// Unmapped values return bottom.
static symboxes::SymRange getState(Value *V,
                                   DenseMap<Value *, symboxes::SymRange> &St) {
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

/// Given a binary operation on \p L and \p R,
/// compute a symbolic range.
/// Operations whose result cannot be bounded
/// symbolically fall back to full()
static symboxes::SymRange intervalBinOp(unsigned Opcode,
                                        const symboxes::SymRange &L,
                                        const symboxes::SymRange &R) {
  if (L.isBottom || R.isBottom)
    return symboxes::SymRange::bottom();

  using SE = symboxes::SymExpr;

  switch (Opcode) {
  case Instruction::ICmp:
    return symboxes::SymRange::of(SE::num(0), SE::num(1));
  case Instruction::Add:
    return symboxes::SymRange::of(SE::add(L.Lower, R.Lower),
                                  SE::add(L.Upper, R.Upper));
  case Instruction::Sub:
    return symboxes::SymRange::of(SE::sub(L.Lower, R.Upper),
                                  SE::sub(L.Upper, R.Lower));
  case Instruction::Mul: {
    auto LL = SE::mul(L.Lower, R.Lower);
    auto LU = SE::mul(L.Lower, R.Upper);
    auto UL = SE::mul(L.Upper, R.Lower);
    auto UU = SE::mul(L.Upper, R.Upper);
    auto Lo = SE::mkMin(SE::mkMin(LL, LU), SE::mkMin(UL, UU));
    auto Hi = SE::mkMax(SE::mkMax(LL, LU), SE::mkMax(UL, UU));
    return symboxes::SymRange::of(Lo, Hi);
  }
  case Instruction::SDiv:
  case Instruction::UDiv: {
    bool RIsConst = !R.isBottom && R.Lower.P == SE::Const &&
                    R.Upper.P == SE::Const && R.Lower.C == R.Upper.C;
    if (RIsConst && R.Lower.C > 0)
      return symboxes::SymRange::of(SE::div(L.Lower, R.Lower),
                                    SE::div(L.Upper, R.Lower));
    return symboxes::SymRange::full();
  }

  case Instruction::SRem: {
    bool RIsConst = !R.isBottom && R.Lower.P == SE::Const &&
                    R.Upper.P == SE::Const && R.Lower.C == R.Upper.C;
    if (RIsConst && R.Lower.C > 0)
      return symboxes::SymRange::of(SE::num(-(R.Lower.C - 1)),
                                    SE::num(R.Lower.C - 1));
    return symboxes::SymRange::full();
  }

  case Instruction::URem: {
    bool RIsConst = !R.isBottom && R.Lower.P == SE::Const &&
                    R.Upper.P == SE::Const && R.Lower.C == R.Upper.C;
    if (RIsConst && R.Lower.C > 0)
      return symboxes::SymRange::of(SE::num(0), SE::num(R.Lower.C - 1));
    return symboxes::SymRange::full();
  }

  case Instruction::Shl: {
    bool RIsConst = !R.isBottom && R.Lower.P == SE::Const &&
                    R.Upper.P == SE::Const && R.Lower.C == R.Upper.C;
    if (RIsConst && R.Lower.C >= 0 && R.Lower.C < 63) {
      int64_t Scale = 1LL << R.Lower.C;
      return symboxes::SymRange::of(SE::mul(L.Lower, SE::num(Scale)),
                                    SE::mul(L.Upper, SE::num(Scale)));
    }
    return symboxes::SymRange::full();
  }

  case Instruction::LShr:
  case Instruction::AShr: {
    bool RIsConst = !R.isBottom && R.Lower.P == SE::Const &&
                    R.Upper.P == SE::Const && R.Lower.C == R.Upper.C;
    if (RIsConst && R.Lower.C >= 0 && R.Lower.C < 63) {
      int64_t Scale = 1LL << R.Lower.C;
      return symboxes::SymRange::of(SE::div(L.Lower, SE::num(Scale)),
                                    SE::div(L.Upper, SE::num(Scale)));
    }
    return symboxes::SymRange::full();
  }

  case Instruction::And: {
    bool LIsConst = !L.isBottom && L.Lower.P == SE::Const &&
                    L.Upper.P == SE::Const && L.Lower.C == L.Upper.C;
    bool RIsConst = !R.isBottom && R.Lower.P == SE::Const &&
                    R.Upper.P == SE::Const && R.Lower.C == R.Upper.C;
    if (LIsConst && RIsConst)
      return symboxes::SymRange::single(SE::num(L.Lower.C & R.Lower.C));
    if (RIsConst && R.Lower.C >= 0)
      return symboxes::SymRange::of(SE::num(0),
                                    SE::mkMin(L.Upper, SE::num(R.Lower.C)));
    if (LIsConst && L.Lower.C >= 0)
      return symboxes::SymRange::of(SE::num(0),
                                    SE::mkMin(R.Upper, SE::num(L.Lower.C)));
    return symboxes::SymRange::full();
  }

  case Instruction::Or:
  case Instruction::Xor: {
    bool LIsConst = !L.isBottom && L.Lower.P == SE::Const &&
                    L.Upper.P == SE::Const && L.Lower.C == L.Upper.C;
    bool RIsConst = !R.isBottom && R.Lower.P == SE::Const &&
                    R.Upper.P == SE::Const && R.Lower.C == R.Upper.C;
    if (LIsConst && RIsConst) {
      int64_t Result = (Opcode == Instruction::Or) ? (L.Lower.C | R.Lower.C)
                                                   : (L.Lower.C ^ R.Lower.C);
      return symboxes::SymRange::single(SE::num(Result));
    }
    return symboxes::SymRange::full();
  }

  default:
    return symboxes::SymRange::full();
  }
}

/// Constraints the range \p R of a sigma node's incoming value
/// using the branch predicate \p Cmp. \p SigmaVar identifies
/// which operand of \p Cmp the sigma node renames; \p IsTrueSide
/// selects the true or false branch.
static symboxes::SymRange
applyConstraint(symboxes::SymRange R, ICmpInst *Cmp, Value *SigmaVar,
                bool IsTrueSide,
                DenseMap<Value *, symboxes::SymRange> &St) {
  using SE = symboxes::SymExpr;
  Value *A = Cmp->getOperand(0);
  Value *B = Cmp->getOperand(1);
  bool IsA = (A == SigmaVar);

  auto Ra = getState(A, St);
  auto Rb = getState(B, St);

  switch (Cmp->getPredicate()) {
  case ICmpInst::ICMP_EQ:
    if (IsTrueSide)
      return symboxes::SymRange::of(SE::mkMax(Ra.Lower, Rb.Lower),
                                    SE::mkMin(Ra.Upper, Rb.Upper));
    return R;

  case ICmpInst::ICMP_NE:
    if (!IsTrueSide)
      return symboxes::SymRange::of(SE::mkMax(Ra.Lower, Rb.Lower),
                                    SE::mkMin(Ra.Upper, Rb.Upper));
    return R;

  case ICmpInst::ICMP_SGE:
    IsTrueSide = !IsTrueSide;
    [[fallthrough]];
  case ICmpInst::ICMP_SLT:
    if (IsTrueSide)
      return IsA ? symboxes::SymRange::of(
                       Ra.Lower,
                       SE::mkMin(SE::sub(Rb.Upper, SE::num(1)), Ra.Upper))
                 : symboxes::SymRange::of(
                       SE::mkMax(SE::add(Ra.Lower, SE::num(1)), Rb.Lower),
                       Rb.Upper);
    else
      return IsA
                 ? symboxes::SymRange::of(SE::mkMax(Ra.Lower, Rb.Lower),
                                          Ra.Upper)
                 : symboxes::SymRange::of(Rb.Lower,
                                          SE::mkMin(Ra.Upper, Rb.Upper));

  case ICmpInst::ICMP_SLE:
    IsTrueSide = !IsTrueSide;
    [[fallthrough]];
  case ICmpInst::ICMP_SGT:
    if (IsTrueSide)
      return IsA ? symboxes::SymRange::of(
                       SE::mkMax(Ra.Lower, SE::add(Rb.Lower, SE::num(1))),
                       Ra.Upper)
                 : symboxes::SymRange::of(
                       Rb.Lower,
                       SE::mkMin(SE::sub(Ra.Upper, SE::num(1)), Rb.Upper));
    else
      return IsA
                 ? symboxes::SymRange::of(Ra.Lower,
                                          SE::mkMin(Ra.Upper, Rb.Upper))
                 : symboxes::SymRange::of(SE::mkMax(Rb.Lower, Ra.Lower),
                                          Rb.Upper);
  default:
    return R;
  }
}

/// Computes the transfer functions for \p I over the
/// symbolic interval domain.
/// - sigma nodes
/// - phi nodes
/// - v = .
/// - casts
static symboxes::SymRange transfer(Instruction &I,
                                   DenseMap<Value *, symboxes::SymRange> &St) {
  if (isa<LoadInst>(I))
    return symboxes::SymRange::single(symboxes::SymExpr::sym(&I));

  if (auto *Call = dyn_cast<CallInst>(&I)) {
    Function *Callee = Call->getCalledFunction();
    if (!Callee || Callee->isDeclaration())
      return symboxes::SymRange::single(symboxes::SymExpr::sym(&I));
  }

  if (auto *Phi = dyn_cast<PHINode>(&I)) {
    if (MDNode *MD = Phi->getMetadata("sigma")) {
      bool IsTrueSide =
          cast<MDString>(MD->getOperand(0))->getString() == ".t";
      Value *Incoming = Phi->getIncomingValue(0);
      BasicBlock *PredBB = Phi->getIncomingBlock(0);
      auto R = getState(Incoming, St);

      if (auto *Br = dyn_cast<BranchInst>(PredBB->getTerminator()))
        if (Br->isConditional())
          if (auto *Cmp = dyn_cast<ICmpInst>(Br->getCondition()))
            R = applyConstraint(R, Cmp, Incoming, IsTrueSide, St);
      return R;
    }
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

/// Runs the symbolic range fixpoint on \p F and annotates
/// each instruction with !srange metadaa encoding its computed
/// range.
static void runOnFunction(Function &F,
                          const SymbolicRangeAnalysis::ArgRangeMap &ArgRanges) {
  DenseMap<Value *, symboxes::SymRange> State;
  DenseMap<Value *, int> IterCount;

  for (Argument &Arg : F.args()) {
    auto It = ArgRanges.find(Arg.getName().str());
    if (It != ArgRanges.end())
      State[&Arg] = symboxes::SymRange::of(
          symboxes::SymExpr::num(It->second.first),
          symboxes::SymExpr::num(It->second.second));
    else
      State[&Arg] = symboxes::SymRange::single(symboxes::SymExpr::sym(&Arg));
  }

  ReversePostOrderTraversal<Function *> RPOT(&F);

  // RPOT ensures each block is visited after its dominators where possible,
  // minimizing the number of iterations needed to reach a fixpoint.
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
          if (Cnt > WidenThreshold) {
            auto &Old = State[&I];
            if (!Old.isBottom)
              NewR = Old.widen(NewR);
          }
        }

        auto &Old = State[&I];
        if (!(NewR == Old)) {
          Old = NewR;
          Changed = true;
        }
      }
    }
  }

  LLVMContext &Ctx = F.getContext();
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      auto It = State.find(&I);
      if (It == State.end())
        continue;
      const symboxes::SymRange &R = It->second;
      if (R.isBottom)
        continue;
      if (R.Lower.P == symboxes::SymExpr::NegInf &&
          R.Upper.P == symboxes::SymExpr::PosInf)
        continue;

      std::string Lo, Hi;
      raw_string_ostream LOS(Lo), HIS(Hi);
      ginac_glue::print(R.Lower, LOS);
      ginac_glue::print(R.Upper, HIS);

      Metadata *Ops[] = {MDString::get(Ctx, LOS.str()),
                         MDString::get(Ctx, HIS.str())};
      I.setMetadata("srange", MDNode::get(Ctx, Ops));
    }
  }
}

PreservedAnalyses SymbolicRangeAnalysis::run(Module &M,
                                             ModuleAnalysisManager &) {
  for (Function &F : M) {
    if (F.isDeclaration())
      continue;
    runOnFunction(F, ArgRanges);
  }
  return PreservedAnalyses::all();
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return {
      LLVM_PLUGIN_API_VERSION, "symbolicRangeAnalysis", LLVM_VERSION_STRING,
      [](PassBuilder &PB) {
        PB.registerPipelineParsingCallback(
            [](StringRef Name, ModulePassManager &MPM,
               ArrayRef<PassBuilder::PipelineElement>) {
              if (!Name.consume_front("sra-annotator"))
                return false;

              SymbolicRangeAnalysis::ArgRangeMap Ranges;
              if (Name.consume_front("<") && Name.consume_back(">")) {
                SmallVector<StringRef> Parts;
                Name.split(Parts, ',');
                for (StringRef Part : Parts) {
                  Part = Part.trim();
                  auto [ArgName, Rest] = Part.split('=');
                  auto [LoStr, HiStr] = Rest.split(':');
                  int64_t Lo, Hi;
                  if (!LoStr.trim().getAsInteger(10, Lo) &&
                      !HiStr.trim().getAsInteger(10, Hi))
                    Ranges[ArgName.trim().str()] = {Lo, Hi};
                }
              }

              MPM.addPass(SymbolicRangeAnalysis(std::move(Ranges)));
              return true;
            });
      }};
}
