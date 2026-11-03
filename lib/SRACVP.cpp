//===- SRACVP.cpp - Correlated value propagation driven by SRA ------------===//
//
/// \file
/// Implements the module pass `sra-cvp`. It applies the rewrites of LLVM's
/// CorrelatedValuePropagation, taking its facts from symbolic range analysis
/// (SRA) instead of LazyValueInfo:
///
///   comparison decided by SRA         -> true or false
///   add/sub/mul that cannot wrap      -> nsw and nuw flags
///   -sra-cvp-signs                    -> sext to zext nneg, sdiv/srem to
///                                        udiv/urem, samesign comparisons,
///                                        trunc flags, 64-bit to 32-bit
///                                        division
///   -sra-cvp-more                     -> dead switch cases, ashr to lshr,
///                                        min/max/abs folds
///   -sra-cvp-overflow                 -> overflow bits of checked arithmetic
///   -sra-cvp-alias                    -> !alias.scope and !noalias
///   -sra-cvp-facts                    -> llvm.assume, range attributes or
///                                        run-time checks
///
/// SRA needs e-SSA form, which rewrites the IR. The pass therefore names
/// every value, clones the module, runs `function(ESSAfier),sra-annotator`
/// on the clone and copies the verdicts back by name. The module itself only
/// changes by the rewrites above.
///
/// With -sra-cvp-at the pass is also added to the default pipelines.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/ProfDataUtils.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LazyValueInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/KnownBits.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Plugins/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/GlobalDCE.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar/ADCE.h"
#include "llvm/Transforms/Scalar/CorrelatedValuePropagation.h"
#include "llvm/Transforms/Scalar/InstSimplifyPass.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/MemoryBuffer.h"
#include <chrono>
#include <optional>

using namespace llvm;

#ifndef SRA_BUILD_DIR
#define SRA_BUILD_DIR ""
#endif

static cl::opt<std::string>
    SRADir("sra-cvp-plugin-dir", cl::init(SRA_BUILD_DIR),
           cl::desc("Directory with ESSAfier.so and SymbolicRanges.so"));
static cl::opt<std::string> At(
    "sra-cvp-at", cl::init("none"),
    cl::desc("Insert sra-cvp into the default pipelines: early "
             "(PipelineEarlySimplificationEP), optimizer-early "
             "(OptimizerEarlyEP), both, last (OptimizerLastEP, then only "
             "deleting cleanups), or none"));
static cl::opt<bool> FoldCmps("sra-cvp-cmps", cl::init(true),
                              cl::desc("Fold comparisons SRA decides"));
static cl::opt<bool> AliasFacts(
    "sra-cvp-alias", cl::init(false),
    cl::desc("Turn SRA's disjoint memory accesses into scoped alias metadata"));
static cl::opt<bool> SignFacts(
    "sra-cvp-signs", cl::init(false),
    cl::desc("Apply SRA's sign and width facts (CVP's sext/div/icmp/trunc rewrites)"));
static cl::opt<bool> MoreFacts(
    "sra-cvp-more", cl::init(false),
    cl::desc("Apply the rest of CVP's rewrites with SRA's facts: dead switch "
             "cases and unreachable defaults, ashr -> lshr, abs/min/max folds"));
static cl::opt<bool> OverflowFacts(
    "sra-cvp-overflow", cl::init(false),
    cl::desc("Fold the overflow bit of s{add,sub,mul}.with.overflow that SRA "
             "proves cannot overflow (removes -fsanitize=signed-integer-overflow checks)"));
static cl::opt<std::string> FactsMode(
    "sra-cvp-facts", cl::init("none"),
    cl::desc("Hand SRA's numeric ranges and known bits to LLVM's analyses: "
             "none; assume (only facts LLVM's computeKnownBits, "
             "computeConstantRange, LVI and SCEV do not already give: "
             "constants replace the value, llvm.assume for new bounds and bits "
             "where poison would already be UB, range attributes on internal "
             "functions' arguments); check (every fact becomes a runtime test "
             "that traps if it is violated)"));
static cl::opt<std::string> DumpInput(
    "sra-cvp-dump-input", cl::init(""), cl::Hidden,
    cl::desc("Write the module as sra-cvp receives it to this file (debugging)"));
static cl::opt<bool> AddFlags("sra-cvp-flags", cl::init(true),
                              cl::desc("Add the nsw/nuw flags SRA proves"));

static cl::opt<std::string> OnlyFunctions(
    "sra-cvp-only", cl::init(""),
    cl::desc("File with one function name per line: apply SRA's rewrites and "
             "facts only in these functions (the analysis still sees the whole "
             "module)"));

/// Returns true if sra-cvp may rewrite \p F (see -sra-cvp-only).
static bool rewriteAllowed(const Function &F) {
  static std::optional<StringSet<>> Allowed = []() -> std::optional<StringSet<>> {
    if (OnlyFunctions.empty())
      return std::nullopt;
    auto Buf = MemoryBuffer::getFile(OnlyFunctions);
    if (!Buf)
      report_fatal_error(Twine("sra-cvp: cannot read ") + OnlyFunctions);
    StringSet<> S;
    SmallVector<StringRef> Lines;
    (*Buf)->getBuffer().split(Lines, '\n', -1, false);
    for (StringRef L : Lines)
      if (!L.trim().empty())
        S.insert(L.trim());
    return S;
  }();
  return !Allowed || Allowed->contains(F.getName());
}

static cl::list<std::string> SRAOpts(
    "sra-cvp-sra-opt", cl::CommaSeparated,
    cl::desc("Options for the SRA plugin it loads, as name or name=value "
             "(e.g. sra-exact=false)"));

/// Runs ESSAfier and sra-annotator on \p C, loading the SRA plugins from
/// -sra-cvp-plugin-dir.
static void runSRA(Module &C) {
  static std::vector<PassPlugin> Plugins = [] {
    std::vector<PassPlugin> Ps;
    for (const char *Name : {"ESSAfier.so", "SymbolicRanges.so"}) {
      std::string Path = SRADir + "/" + Name;
      auto P = PassPlugin::Load(Path);
      if (!P)
        report_fatal_error(Twine("sra-cvp: cannot load ") + Path + ": " +
                           toString(P.takeError()));
      Ps.push_back(*P);
    }
    return Ps;
  }();
  PassBuilder PB;
  for (PassPlugin &P : Plugins)
    P.registerPassBuilderCallbacks(PB);
  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
  if (AliasFacts)
    if (auto *O = cl::getRegisteredOptions().lookup("sra-alias"))
      O->addOccurrence(0, "sra-alias", "true");
  // "name" sets a boolean option, "name=value" any option.
  for (const std::string &Opt : SRAOpts) {
    auto [Name, Val] = StringRef(Opt).split('=');
    if (auto *O = cl::getRegisteredOptions().lookup(Name))
      O->addOccurrence(0, Name, Val.empty() ? "true" : Val);
  }
  if (getenv("SRA_STATS"))
    if (auto *O = cl::getRegisteredOptions().lookup("sra-stats"))
      O->addOccurrence(0, "sra-stats", "true");
  ModulePassManager MPM;
  if (auto Err = PB.parsePassPipeline(MPM, "function(ESSAfier),sra-annotator"))
    report_fatal_error(Twine("sra-cvp: ") + toString(std::move(Err)));
  MPM.run(C, MAM);
}

/// Names every unnamed argument and instruction of \p M, so that values can
/// be matched between \p M and its clone.
static void nameValuesForSRA(Module &M) {
  for (Function &F : M) {
    if (F.isDeclaration())
      continue;
    for (Argument &A : F.args())
      if (!A.hasName())
        A.setName("sra.a");
    for (Instruction &I : instructions(F))
      if (!I.hasName() && !I.getType()->isVoidTy())
        I.setName("sra.v");
  }
}

/// Tags loads and stores (for alias facts) and switches (for switch facts)
/// with !sra.id, since they have no names to be matched by. \p ById maps
/// each tag back to its instruction.
static void tagAccesses(Module &M, std::vector<Instruction *> &ById) {
  LLVMContext &Ctx = M.getContext();
  Type *I64 = Type::getInt64Ty(Ctx);
  for (Function &F : M)
    for (Instruction &I : instructions(F))
      if (((isa<LoadInst>(I) || isa<StoreInst>(I)) && AliasFacts) ||
          (isa<SwitchInst>(I) && MoreFacts)) {
        I.setMetadata("sra.id", MDNode::get(Ctx, ConstantAsMetadata::get(
                                                     ConstantInt::get(I64, ById.size()))));
        ById.push_back(&I);
      }
}

/// For every access A that SRA proves disjoint from accesses B1..Bk, adds a
/// new scope to A's !alias.scope and to each Bi's !noalias, declared at the
/// function's entry with llvm.experimental.noalias.scope.decl so that the
/// facts hold within one call. Returns the number of pairs.
static unsigned applyAliasFacts(Module &C, const std::vector<Instruction *> &ById) {
  unsigned Pairs = 0;
  MapVector<Function *, SmallVector<std::pair<Instruction *, SmallVector<Instruction *, 4>>, 8>> Facts;
  for (Function &CF : C)
    for (Instruction &CI : instructions(CF)) {
      MDNode *MD = CI.getMetadata("srange.noalias");
      MDNode *Id = CI.getMetadata("sra.id");
      if (!MD || !Id)
        continue;
      auto IdOf = [&](const MDOperand &Op) {
        return mdconst::extract<ConstantInt>(Op)->getZExtValue();
      };
      Instruction *A = ById[IdOf(Id->getOperand(0))];
      SmallVector<Instruction *, 4> Bs;
      for (const MDOperand &Op : MD->operands())
        Bs.push_back(ById[IdOf(Op)]);
      Pairs += Bs.size();
      Facts[A->getFunction()].push_back({A, std::move(Bs)});
    }
  for (auto &[F, List] : Facts) {
    LLVMContext &Ctx = F->getContext();
    MDBuilder MDB(Ctx);
    MDNode *Domain = MDB.createAnonymousAliasScopeDomain(F->getName());
    IRBuilder<> B(&*F->getEntryBlock().getFirstInsertionPt());
    for (auto &[A, Bs] : List) {
      MDNode *Scope = MDB.createAnonymousAliasScope(Domain);
      MDNode *One = MDNode::get(Ctx, Scope);
      A->setMetadata(LLVMContext::MD_alias_scope,
                     MDNode::concatenate(A->getMetadata(LLVMContext::MD_alias_scope), One));
      for (Instruction *X : Bs)
        X->setMetadata(LLVMContext::MD_noalias,
                       MDNode::concatenate(X->getMetadata(LLVMContext::MD_noalias), One));
      B.CreateIntrinsic(Intrinsic::experimental_noalias_scope_decl, {},
                        {MetadataAsValue::get(Ctx, One)});
    }
  }
  return Pairs;
}

namespace {

/// Counts of the facts handed to LLVM (-sra-cvp-facts).
struct FactStats {
  unsigned Consts = 0, Bounds = 0, Bits = 0, ArgAttrs = 0, Checks = 0,
           PoisonSkipped = 0, Known = 0;
};

/// Parses the decimal integer in the metadata string \p Op as a \p Width-bit
/// value.
APInt parseAPInt(const MDOperand &Op, unsigned Width, bool Signed) {
  APInt V(std::max(Width, 192u), cast<MDString>(Op)->getString(), 10);
  return Signed ? V.sextOrTrunc(Width) : V.zextOrTrunc(Width);
}

/// Returns SRA's numeric range and known bits of the clone's \p CI, if any:
/// !srange.cr and !srange.kb when present, otherwise the numeric hull of
/// !srange.
std::pair<std::optional<ConstantRange>, std::optional<KnownBits>>
sraFacts(Instruction &CI) {
  unsigned N = CI.getType()->getIntegerBitWidth();
  std::optional<ConstantRange> CR;
  std::optional<KnownBits> KB;
  if (MDNode *MD = CI.getMetadata("srange.cr")) {
    APInt Lo = parseAPInt(MD->getOperand(0), N, true);
    APInt Hi = parseAPInt(MD->getOperand(1), N, true);
    if (Lo.sle(Hi))
      CR = ConstantRange::getNonEmpty(Lo, Hi + 1);
  } else if (MDNode *MD = CI.getMetadata("srange");
             MD && MD->getNumOperands() == 4) {
    // !srange is {symbolic lo, symbolic hi, numeric lo, numeric hi}.
    APInt Lo = parseAPInt(MD->getOperand(2), N, true);
    APInt Hi = parseAPInt(MD->getOperand(3), N, true);
    if (Lo.sle(Hi) && !(Lo.isMinSignedValue() && Hi.isMaxSignedValue()))
      CR = ConstantRange::getNonEmpty(Lo, Hi + 1);
  }
  if (MDNode *MD = CI.getMetadata("srange.kb")) {
    KnownBits K(N);
    K.Zero = parseAPInt(MD->getOperand(0), N, false);
    K.One = parseAPInt(MD->getOperand(1), N, false);
    if (!K.hasConflict())
      KB = K;
  }
  return {CR, KB};
}

/// Inserts `assume(Cond)` (assume mode) or `if (!Cond) trap` (check mode)
/// right after the definition of \p I. \p MakeCond builds the condition on
/// the value; in check mode it gets a frozen copy, so that a poison value
/// cannot make the check itself undefined. \p Poison is the value's poison
/// shadow (check mode only).
void emitFact(Instruction *I, bool Check, FactStats &S,
              function_ref<Value *(IRBuilder<> &, Value *)> MakeCond,
              const Twine &What = "", Value *Poison = nullptr) {
  // The check reads the poison shadow, so it goes after whichever of the
  // value and its shadow comes last.
  Instruction *After = I;
  if (auto *PI = dyn_cast_or_null<Instruction>(Poison);
      PI && !isa<PHINode>(PI) && !isa<PHINode>(I) && PI->getParent() == I->getParent() &&
      I->comesBefore(PI))
    After = PI;
  auto Pos = After->getInsertionPointAfterDef();
  if (!Pos)
    return;
  IRBuilder<> B(After->getParent(), *Pos);
  if (!Check) {
    CallInst *A = B.CreateAssumption(MakeCond(B, I));
    // Tagged so that -sra-cvp-last-drop-assumes can remove it.
    A->setMetadata("sra.fact", MDNode::get(A->getContext(), {}));
    return;
  }
  Value *Frozen = B.CreateFreeze(I);
  Value *Cond = MakeCond(B, Frozen);
  // A fact only constrains values that are not poison.
  if (Poison)
    Cond = B.CreateOr(Cond, Poison);
  Instruction *Then = SplitBlockAndInsertIfThen(B.CreateNot(Cond), &*B.GetInsertPoint(),
                                                /*Unreachable=*/true);
  IRBuilder<> T(Then);
  // Report the failing fact with write(2, ...), which is unbuffered, then
  // trap.
  Module *M = I->getModule();
  FunctionCallee Write = M->getOrInsertFunction(
      "write", FunctionType::get(T.getInt64Ty(),
                                 {T.getInt32Ty(), T.getPtrTy(), T.getInt64Ty()}, false));
  std::string Name = I->hasName() ? I->getName().str() : "?";
  std::string Msg = ("SRA fact violated: @" + I->getFunction()->getName() + " %" + Name +
                     " " + What + "\n").str();
  T.CreateCall(Write, {T.getInt32(2), T.CreateGlobalString(Msg), T.getInt64(Msg.size())});
  T.CreateIntrinsic(Intrinsic::trap, {});
  ++S.Checks;
}

/// Builds, for every instruction of \p F, an i1 that is true at run time
/// when the instruction's value is poison. It combines the instruction's own
/// poison conditions (nsw/nuw overflow, nneg, exact, disjoint, samesign,
/// out-of-range shifts, trunc flags, !range and range attributes, abs, ctlz
/// and cttz flags) with its operands' shadows, computed on frozen values.
/// Where the condition is unknown the shadow is true, so a check is skipped
/// rather than wrongly failed.
DenseMap<Value *, Value *> buildPoisonShadows(Function &F) {
  DenseMap<Value *, Value *> Sh;
  LLVMContext &Ctx = F.getContext();
  Constant *False = ConstantInt::getFalse(Ctx), *True = ConstantInt::getTrue(Ctx);
  auto ShOf = [&](Value *V) -> Value * {
    if (auto It = Sh.find(V); It != Sh.end())
      return It->second;
    if (isa<PoisonValue>(V) || isa<UndefValue>(V))
      return True;
    if (auto *A = dyn_cast<Argument>(V))
      return A->hasAttribute(Attribute::NoUndef) || !A->use_empty() ? False : True;
    return False; // Constants and globals.
  };
  SmallVector<Instruction *, 64> Order;
  ReversePostOrderTraversal<Function *> RPOT(&F);
  for (BasicBlock *BB : RPOT)
    for (Instruction &I : *BB)
      if (!I.getType()->isVoidTy())
        Order.push_back(&I);
  // Phis first; their incoming shadows are filled in at the end.
  SmallVector<std::pair<PHINode *, PHINode *>, 32> Phis;
  for (Instruction *I : Order)
    if (auto *P = dyn_cast<PHINode>(I)) {
      auto *SP = PHINode::Create(Type::getInt1Ty(Ctx), P->getNumIncomingValues(), "",
                                 P->getParent()->getFirstNonPHIIt());
      Sh[P] = SP;
      Phis.push_back({P, SP});
    }
  for (Instruction *I : Order) {
    if (isa<PHINode>(I))
      continue;
    if (I->getType()->isVectorTy() || isa<FPToSIInst>(I) || isa<FPToUIInst>(I) ||
        isa<LandingPadInst>(I)) {
      Sh[I] = True;
      continue;
    }
    if (isa<FreezeInst>(I)) {
      Sh[I] = False;
      continue;
    }
    auto Pos = I->getInsertionPointAfterDef();
    if (!Pos) {
      Sh[I] = True;
      continue;
    }
    IRBuilder<> B(I->getParent(), *Pos);
    auto Fr = [&](Value *V) { return isa<Constant>(V) ? V : B.CreateFreeze(V); };
    Value *P = False;
    auto Or = [&](Value *X) { P = P == False ? X : B.CreateOr(P, X); };
    if (auto *Sel = dyn_cast<SelectInst>(I)) {
      Or(ShOf(Sel->getCondition()));
      Or(B.CreateSelect(Fr(Sel->getCondition()), ShOf(Sel->getTrueValue()),
                        ShOf(Sel->getFalseValue())));
      Sh[I] = P;
      continue;
    }
    for (Value *Op : I->operands())
      if (!isa<BasicBlock>(Op) && !isa<Function>(Op) && !isa<MetadataAsValue>(Op) &&
          !Op->getType()->isLabelTy())
        if (Value *X = ShOf(Op); X != False)
          Or(X);
    Type *Ty = I->getType();
    auto *IT = dyn_cast<IntegerType>(Ty);
    if (auto *BO = dyn_cast<BinaryOperator>(I); BO && IT) {
      Value *A = Fr(BO->getOperand(0)), *C = Fr(BO->getOperand(1));
      unsigned N = IT->getBitWidth();
      unsigned Opc = BO->getOpcode();
      auto Ovf = [&](Intrinsic::ID ID) {
        return B.CreateExtractValue(B.CreateBinaryIntrinsic(ID, A, C), 1);
      };
      if (auto *OBO = dyn_cast<OverflowingBinaryOperator>(BO)) {
        if (Opc == Instruction::Shl) {
          Value *Big = B.CreateICmpUGE(C, ConstantInt::get(IT, N));
          Or(Big);
          Value *Amt = B.CreateSelect(Big, ConstantInt::get(IT, 0), C);
          Value *Sh1 = B.CreateShl(A, Amt);
          if (OBO->hasNoUnsignedWrap())
            Or(B.CreateICmpNE(B.CreateLShr(Sh1, Amt), A));
          if (OBO->hasNoSignedWrap())
            Or(B.CreateICmpNE(B.CreateAShr(Sh1, Amt), A));
        } else {
          Intrinsic::ID S = Opc == Instruction::Add   ? Intrinsic::sadd_with_overflow
                            : Opc == Instruction::Sub ? Intrinsic::ssub_with_overflow
                                                      : Intrinsic::smul_with_overflow;
          Intrinsic::ID U = Opc == Instruction::Add   ? Intrinsic::uadd_with_overflow
                            : Opc == Instruction::Sub ? Intrinsic::usub_with_overflow
                                                      : Intrinsic::umul_with_overflow;
          if (OBO->hasNoSignedWrap())
            Or(Ovf(S));
          if (OBO->hasNoUnsignedWrap())
            Or(Ovf(U));
        }
      } else if (Opc == Instruction::LShr || Opc == Instruction::AShr) {
        Value *Big = B.CreateICmpUGE(C, ConstantInt::get(IT, N));
        Or(Big);
        if (BO->isExact()) {
          Value *Amt = B.CreateSelect(Big, ConstantInt::get(IT, 0), C);
          Value *R = Opc == Instruction::LShr ? B.CreateLShr(A, Amt) : B.CreateAShr(A, Amt);
          Or(B.CreateICmpNE(B.CreateShl(R, Amt), A));
        }
      } else if ((Opc == Instruction::UDiv || Opc == Instruction::SDiv) && BO->isExact()) {
        // Division by zero and INT_MIN / -1 are UB, not poison: avoid them.
        Value *Bad = B.CreateICmpEQ(C, ConstantInt::get(IT, 0));
        if (Opc == Instruction::SDiv)
          Bad = B.CreateOr(Bad, B.CreateAnd(
                                    B.CreateICmpEQ(A, ConstantInt::get(IT, APInt::getSignedMinValue(N))),
                                    B.CreateICmpEQ(C, ConstantInt::getAllOnesValue(IT))));
        Value *D = B.CreateSelect(Bad, ConstantInt::get(IT, 1), C);
        Value *Rem = Opc == Instruction::UDiv ? B.CreateURem(A, D) : B.CreateSRem(A, D);
        Or(B.CreateAnd(B.CreateNot(Bad), B.CreateICmpNE(Rem, ConstantInt::get(IT, 0))));
      } else if (Opc == Instruction::Or && cast<PossiblyDisjointInst>(BO)->isDisjoint()) {
        Or(B.CreateICmpNE(B.CreateAnd(A, C), ConstantInt::get(IT, 0)));
      }
    } else if (auto *Cmp = dyn_cast<ICmpInst>(I); Cmp && Cmp->hasSameSign() &&
                                                 Cmp->getOperand(0)->getType()->isIntegerTy()) {
      Or(B.CreateICmpSLT(B.CreateXor(Fr(Cmp->getOperand(0)), Fr(Cmp->getOperand(1))),
                         ConstantInt::get(Cmp->getOperand(0)->getType(), 0)));
    } else if (auto *Z = dyn_cast<ZExtInst>(I); Z && Z->hasNonNeg()) {
      Or(B.CreateICmpSLT(Fr(Z->getOperand(0)), ConstantInt::get(Z->getSrcTy(), 0)));
    } else if (auto *T = dyn_cast<TruncInst>(I)) {
      Value *X = Fr(T->getOperand(0));
      if (T->hasNoUnsignedWrap())
        Or(B.CreateICmpNE(B.CreateZExt(B.CreateTrunc(X, Ty), X->getType()), X));
      if (T->hasNoSignedWrap())
        Or(B.CreateICmpNE(B.CreateSExt(B.CreateTrunc(X, Ty), X->getType()), X));
    } else if (auto *II = dyn_cast<IntrinsicInst>(I); II && IT) {
      Intrinsic::ID ID = II->getIntrinsicID();
      if (ID == Intrinsic::abs && cast<ConstantInt>(II->getArgOperand(1))->isOne())
        Or(B.CreateICmpEQ(Fr(II->getArgOperand(0)),
                          ConstantInt::get(IT, APInt::getSignedMinValue(IT->getBitWidth()))));
      if ((ID == Intrinsic::ctlz || ID == Intrinsic::cttz) &&
          cast<ConstantInt>(II->getArgOperand(1))->isOne())
        Or(B.CreateICmpEQ(Fr(II->getArgOperand(0)), ConstantInt::get(IT, 0)));
    }
    // A value outside its !range metadata or range attribute is poison.
    std::optional<ConstantRange> R;
    if (auto *L = dyn_cast<LoadInst>(I); L && IT)
      if (MDNode *MD = L->getMetadata(LLVMContext::MD_range))
        R = getConstantRangeFromMetadata(*MD);
    if (auto *CB = dyn_cast<CallBase>(I); CB && IT)
      R = CB->getRange();
    if (R && !R->isFullSet()) {
      Value *X = B.CreateFreeze(I);
      Value *Off = B.CreateSub(X, ConstantInt::get(IT, R->getLower()));
      Or(B.CreateICmpUGE(Off, ConstantInt::get(IT, R->getUpper() - R->getLower())));
    }
    Sh[I] = P;
  }
  for (auto [P, SP] : Phis)
    for (unsigned K = 0; K < P->getNumIncomingValues(); ++K)
      SP->addIncoming(ShOf(P->getIncomingValue(K)), P->getIncomingBlock(K));
  return Sh;
}

/// Check mode: turns every fact SRA claims in \p F into a run-time test that
/// traps if the value is not poison and the fact does not hold. \p CF is the
/// clone of \p F and \p Pairs matches their instructions.
void applyChecks(Function &F, Function &CF,
                 ArrayRef<std::pair<Instruction *, Instruction *>> Pairs, FactStats &S) {
  DenseMap<Value *, Value *> Sh = buildPoisonShadows(F);
  for (auto [I, CI] : Pairs) {
    Value *Poison = Sh.lookup(I);
    if (Poison == ConstantInt::getTrue(F.getContext()))
      continue; // Unknown poison condition.
    Type *Ty = I->getType();
    if (auto *Cmp = dyn_cast<ICmpInst>(I)) {
      if (MDNode *MD = CI->getMetadata("srange.cmp");
          MD && Cmp->getPredicate() == cast<ICmpInst>(CI)->getPredicate()) {
        bool V = cast<MDString>(MD->getOperand(0))->getString() == "true";
        emitFact(I, true, S, [&](IRBuilder<> &B, Value *X) {
          return B.CreateICmpEQ(X, ConstantInt::getBool(X->getContext(), V));
        }, V ? "cmp true" : "cmp false", Poison);
      }
      continue;
    }
    auto *IT = dyn_cast<IntegerType>(Ty);
    if (!IT || IT->getBitWidth() < 2 || IT->getBitWidth() > 128)
      continue;
    auto [CR, KB] = sraFacts(*CI);
    if (CR && !CR->isFullSet()) {
      APInt Lo = CR->getSignedMin(), Hi = CR->getSignedMax();
      emitFact(I, true, S, [&](IRBuilder<> &B, Value *V) {
        return B.CreateAnd(B.CreateICmpSGE(V, ConstantInt::get(Ty, Lo)),
                           B.CreateICmpSLE(V, ConstantInt::get(Ty, Hi)));
      }, "range [" + toString(Lo, 10, true) + ", " + toString(Hi, 10, true) + "]", Poison);
    }
    if (KB) {
      APInt Mask = KB->Zero | KB->One;
      APInt One = KB->One;
      emitFact(I, true, S, [&](IRBuilder<> &B, Value *V) {
        return B.CreateICmpEQ(B.CreateAnd(V, ConstantInt::get(Ty, Mask)),
                              ConstantInt::get(Ty, One));
      }, "bits zero=" + toString(KB->Zero, 16, false) + " one=" + toString(KB->One, 16, false),
               Poison);
    }
  }
  // Arguments of internal functions, from the numeric hulls in !srange.args.
  if (MDNode *Args = CF.getMetadata("srange.args"); Args && F.hasLocalLinkage())
    for (Argument &A : F.args()) {
      auto *IT = dyn_cast<IntegerType>(A.getType());
      if (!IT || IT->getBitWidth() < 2 || IT->getBitWidth() > 128 ||
          A.getArgNo() >= Args->getNumOperands() || !A.hasAttribute(Attribute::NoUndef))
        continue;
      auto *Tup = dyn_cast<MDTuple>(Args->getOperand(A.getArgNo()));
      if (!Tup || Tup->getNumOperands() < 4)
        continue;
      unsigned N = IT->getBitWidth();
      APInt Lo = parseAPInt(Tup->getOperand(2), N, true);
      APInt Hi = parseAPInt(Tup->getOperand(3), N, true);
      if (Lo.sgt(Hi) || ConstantRange::getNonEmpty(Lo, Hi + 1).isFullSet())
        continue;
      IRBuilder<> B(&*F.getEntryBlock().getFirstInsertionPt());
      Value *V = B.CreateFreeze(&A);
      Value *Cond = B.CreateAnd(B.CreateICmpSGE(V, ConstantInt::get(IT, Lo)),
                                B.CreateICmpSLE(V, ConstantInt::get(IT, Hi)));
      Instruction *Then = SplitBlockAndInsertIfThen(B.CreateNot(Cond), &*B.GetInsertPoint(), true);
      IRBuilder<>(Then).CreateIntrinsic(Intrinsic::trap, {});
      ++S.Checks;
    }
}

/// Hands SRA's numeric facts about \p F to LLVM (-sra-cvp-facts). \p CF is
/// the clone of \p F and \p Pairs matches their instructions.
void applyFacts(Function &F, Function &CF,
                ArrayRef<std::pair<Instruction *, Instruction *>> Pairs,
                FunctionAnalysisManager &FAM, FactStats &S) {
  if (FactsMode == "check") {
    applyChecks(F, CF, Pairs, S);
    FAM.invalidate(F, PreservedAnalyses::none());
    return;
  }
  bool Check = false;
  const DataLayout &DL = F.getDataLayout();
  // This pass may have changed F already.
  FAM.invalidate(F, PreservedAnalyses::none());
  auto &AC = FAM.getResult<AssumptionAnalysis>(F);
  auto &DT = FAM.getResult<DominatorTreeAnalysis>(F);
  auto &LVI = FAM.getResult<LazyValueAnalysis>(F);
  auto &SE = FAM.getResult<ScalarEvolutionAnalysis>(F);

  struct Todo {
    Instruction *I;
    std::optional<ConstantRange> CR;
    std::optional<KnownBits> KB;
    ConstantRange LCR;
    KnownBits LKB;
    bool PoisonOk;
  };
  SmallVector<Todo, 64> Todos;
  // Query LLVM's analyses before changing F.
  for (auto [I, CI] : Pairs) {
    auto *IT = dyn_cast<IntegerType>(I->getType());
    if (!IT || IT->getBitWidth() < 2 || IT->getBitWidth() > 128)
      continue;
    auto [CR, KB] = sraFacts(*CI);
    if (!CR && !KB)
      continue;
    unsigned N = IT->getBitWidth();
    KnownBits LKB = computeKnownBits(I, DL, &AC, I, &DT);
    ConstantRange LCR = computeConstantRange(I, /*ForSigned=*/true, true, &AC, I, &DT);
    LCR = LCR.intersectWith(LVI.getConstantRange(I, I, /*UndefAllowed=*/false),
                            ConstantRange::Signed);
    if (SE.isSCEVable(I->getType())) {
      const SCEV *X = SE.getSCEV(I);
      LCR = LCR.intersectWith(SE.getSignedRange(X), ConstantRange::Signed)
                .intersectWith(SE.getUnsignedRange(X), ConstantRange::Signed);
    }
    if (!LKB.hasConflict() && !LKB.isUnknown())
      LCR = LCR.intersectWith(ConstantRange::fromKnownBits(LKB, true), ConstantRange::Signed);
    if (LCR.isEmptySet())
      LCR = ConstantRange::getFull(N);
    bool PoisonOk = programUndefinedIfPoison(I) || isGuaranteedNotToBePoison(I, &AC, I, &DT);
    Todos.push_back({I, CR, KB, LCR, LKB, PoisonOk});
  }

  for (Todo &T : Todos) {
    Instruction *I = T.I;
    unsigned N = I->getType()->getIntegerBitWidth();
    Type *Ty = I->getType();
    if (Check) {
      if (T.CR && !T.CR->isFullSet()) {
        APInt Lo = T.CR->getSignedMin(), Hi = T.CR->getSignedMax();
        emitFact(I, true, S, [&](IRBuilder<> &B, Value *V) {
          return B.CreateAnd(B.CreateICmpSGE(V, ConstantInt::get(Ty, Lo)),
                             B.CreateICmpSLE(V, ConstantInt::get(Ty, Hi)));
        }, "range [" + toString(Lo, 10, true) + ", " + toString(Hi, 10, true) + "]");
      }
      if (T.KB) {
        APInt Mask = T.KB->Zero | T.KB->One;
        emitFact(I, true, S, [&](IRBuilder<> &B, Value *V) {
          return B.CreateICmpEQ(B.CreateAnd(V, ConstantInt::get(Ty, Mask)),
                                ConstantInt::get(Ty, T.KB->One));
        }, "bits zero=" + toString(T.KB->Zero, 16, false) + " one=" + toString(T.KB->One, 16, false));
      }
      continue;
    }
    // Assume mode: only the facts LLVM does not already know.
    ConstantRange SCR = T.CR ? *T.CR : ConstantRange::getFull(N);
    if (T.KB)
      SCR = SCR.intersectWith(ConstantRange::fromKnownBits(*T.KB, true), ConstantRange::Signed);
    if (SCR.isEmptySet())
      continue;
    if (const APInt *C = SCR.getSingleElement()) {
      if (!(T.LCR.getSingleElement())) {
        I->replaceAllUsesWith(ConstantInt::get(Ty, *C));
        ++S.Consts;
      } else {
        ++S.Known;
      }
      continue;
    }
    bool NewLo = SCR.getSignedMin().sgt(T.LCR.getSignedMin());
    bool NewHi = SCR.getSignedMax().slt(T.LCR.getSignedMax());
    APInt NewBits(N, 0);
    if (T.KB)
      NewBits = (T.KB->Zero | T.KB->One) & ~(T.LKB.Zero | T.LKB.One);
    // Bits already implied by the new bounds need no mask of their own.
    KnownBits FromRange = SCR.toKnownBits();
    bool BitsBeyondRange = !(NewBits & ~(FromRange.Zero | FromRange.One)).isZero();
    if (!NewLo && !NewHi && !BitsBeyondRange) {
      ++S.Known;
      continue;
    }
    if (!T.PoisonOk) {
      ++S.PoisonSkipped;
      continue;
    }
    APInt Lo = SCR.getSignedMin(), Hi = SCR.getSignedMax();
    if (NewLo) {
      emitFact(I, false, S, [&](IRBuilder<> &B, Value *V) {
        return B.CreateICmpSGE(V, ConstantInt::get(Ty, Lo));
      });
      ++S.Bounds;
    }
    if (NewHi) {
      emitFact(I, false, S, [&](IRBuilder<> &B, Value *V) {
        return B.CreateICmpSLE(V, ConstantInt::get(Ty, Hi));
      });
      ++S.Bounds;
    }
    if (BitsBeyondRange) {
      APInt Mask = NewBits;
      APInt Val = T.KB->One & Mask;
      emitFact(I, false, S, [&](IRBuilder<> &B, Value *V) {
        return B.CreateICmpEQ(B.CreateAnd(V, ConstantInt::get(Ty, Mask)),
                              ConstantInt::get(Ty, Val));
      });
      ++S.Bits;
    }
  }

  // Arguments of internal functions, whose call sites are all known: range
  // attributes in assume mode (a violation makes the argument poison, not
  // UB), checks at the entry in check mode.
  if (MDNode *Args = CF.getMetadata("srange.args"); Args && F.hasLocalLinkage())
    for (Argument &A : F.args()) {
      auto *IT = dyn_cast<IntegerType>(A.getType());
      if (!IT || IT->getBitWidth() < 2 || IT->getBitWidth() > 128 ||
          A.getArgNo() >= Args->getNumOperands())
        continue;
      auto *Tup = dyn_cast<MDTuple>(Args->getOperand(A.getArgNo()));
      if (!Tup || Tup->getNumOperands() < 4)
        continue;
      unsigned N = IT->getBitWidth();
      APInt Lo = parseAPInt(Tup->getOperand(2), N, true);
      APInt Hi = parseAPInt(Tup->getOperand(3), N, true);
      if (Lo.sgt(Hi))
        continue;
      ConstantRange CR = ConstantRange::getNonEmpty(Lo, Hi + 1);
      if (CR.isFullSet())
        continue;
      if (Check) {
        IRBuilder<> B(&*F.getEntryBlock().getFirstInsertionPt());
        Value *V = B.CreateFreeze(&A);
        Value *Cond = B.CreateAnd(B.CreateICmpSGE(V, ConstantInt::get(IT, Lo)),
                                  B.CreateICmpSLE(V, ConstantInt::get(IT, Hi)));
        Instruction *Then = SplitBlockAndInsertIfThen(B.CreateNot(Cond), &*B.GetInsertPoint(), true);
        IRBuilder<>(Then).CreateIntrinsic(Intrinsic::trap, {});
        ++S.Checks;
        continue;
      }
      if (auto Old = A.getRange()) {
        ConstantRange M = Old->intersectWith(CR, ConstantRange::Signed);
        if (M == *Old || M.isEmptySet())
          continue;
        CR = M;
      }
      A.removeAttr(Attribute::Range);
      A.addAttr(Attribute::get(F.getContext(), Attribute::Range, CR));
      ++S.ArgAttrs;
    }
  FAM.invalidate(F, PreservedAnalyses::none());
}

/// The `sra-cvp` module pass.
struct SRACVPPass : PassInfoMixin<SRACVPPass> {
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM) {
    auto &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
    FactStats FS;
    if (!DumpInput.empty()) {
      std::error_code EC;
      raw_fd_ostream OS(DumpInput, EC);
      if (!EC)
        M.print(OS, nullptr);
    }
    auto Start = std::chrono::steady_clock::now();
    nameValuesForSRA(M);
    std::vector<Instruction *> ById;
    if (AliasFacts || MoreFacts)
      tagAccesses(M, ById);
    std::unique_ptr<Module> C = CloneModule(M);
    runSRA(*C);
    unsigned AliasPairs = AliasFacts ? applyAliasFacts(*C, ById) : 0;
    unsigned DeadCases = 0, NoDefault = 0, LShr = 0, Picks = 0;
    if (MoreFacts)
      for (Function &CF : *C)
        for (Instruction &CI : instructions(CF)) {
          MDNode *MD = CI.getMetadata("srange.switch");
          MDNode *Id = CI.getMetadata("sra.id");
          if (!MD || !Id)
            continue;
          auto *SI = cast<SwitchInst>(ById[mdconst::extract<ConstantInt>(
                                                Id->getOperand(0))->getZExtValue()]);
          if (!rewriteAllowed(*SI->getFunction()))
            continue;
          BasicBlock *BB = SI->getParent();
          // Each removed edge removes one phi entry, as in LLVM's CVP.
          SwitchInstProfUpdateWrapper W(*SI);
          for (const MDOperand &Op : MD->operands()) {
            if (isa<MDString>(Op)) { // The default destination.
              BasicBlock *Old = SI->getDefaultDest();
              BasicBlock *U = BasicBlock::Create(BB->getContext(), "default.unreachable",
                                                 BB->getParent(), Old);
              new UnreachableInst(BB->getContext(), U);
              Old->removePredecessor(BB);
              W->setDefaultDest(U);
              ++NoDefault;
              continue;
            }
            int64_t V = mdconst::extract<ConstantInt>(Op)->getSExtValue();
            auto *CV = ConstantInt::get(cast<IntegerType>(SI->getCondition()->getType()), V,
                                        /*IsSigned=*/true);
            auto Case = SI->findCaseValue(CV);
            if (Case == SI->case_default())
              continue;
            Case->getCaseSuccessor()->removePredecessor(BB);
            W.removeCase(Case);
            ++DeadCases;
          }
        }
    for (Instruction *I : ById)
      I->setMetadata("sra.id", nullptr);

    unsigned True = 0, False = 0, NSW = 0, NUW = 0, NoOverflow = 0;
    unsigned SameSign = 0, TruncFlags = 0, NNeg = 0, Unsigned = 0, DivNarrow = 0;
    for (Function &F : M) {
      Function *CF = C->getFunction(F.getName());
      if (F.isDeclaration() || !CF || CF->isDeclaration() || !rewriteAllowed(F))
        continue;
      StringMap<Instruction *> Names;
      for (Instruction &I : instructions(F))
        if (I.hasName())
          Names[I.getName()] = &I;
      SmallVector<std::pair<ICmpInst *, bool>, 16> Folds;
      SmallVector<std::pair<Instruction *, Instruction *>, 16> Signs, More, FactPairs;
      for (Instruction &CI : instructions(*CF)) {
        if (!CI.hasName())
          continue;
        Instruction *I = Names.lookup(CI.getName());
        // ESSAfier's sigma nodes have no counterpart in M.
        if (!I || I->getOpcode() != CI.getOpcode() || I->getType() != CI.getType())
          continue;
        if (SignFacts)
          Signs.push_back({I, &CI});
        if (FactsMode != "none" && I->getType()->isIntegerTy())
          FactPairs.push_back({I, &CI});
        if (OverflowFacts && CI.getMetadata("srange.nooverflow") && isa<IntrinsicInst>(I) &&
            cast<IntrinsicInst>(I)->getIntrinsicID() ==
                cast<IntrinsicInst>(CI).getIntrinsicID())
          for (User *U : make_early_inc_range(I->users()))
            if (auto *EV = dyn_cast<ExtractValueInst>(U))
              if (EV->getNumIndices() == 1 && EV->getIndices()[0] == 1) {
                EV->replaceAllUsesWith(ConstantInt::getFalse(EV->getContext()));
                EV->eraseFromParent();
                ++NoOverflow;
              }
        if (MoreFacts) {
          if (CI.getMetadata("srange.lshr") && I->getOpcode() == Instruction::AShr)
            More.push_back({I, &CI});
          else if (CI.getMetadata("srange.pick") && isa<IntrinsicInst>(I))
            More.push_back({I, &CI});
        }
        if (auto *Cmp = dyn_cast<ICmpInst>(I)) {
          MDNode *MD = CI.getMetadata("srange.cmp");
          if (FoldCmps && MD &&
              Cmp->getPredicate() == cast<ICmpInst>(CI).getPredicate()) {
            bool V = cast<MDString>(MD->getOperand(0))->getString() == "true";
            Folds.push_back({Cmp, V});
            if (getenv("SRA_PRINT_DECIDED")) {
              // One line per decided comparison, with the definitions of its
              // operands.
              std::string Line;
              raw_string_ostream OS(Line);
              OS << "sra-decided: @" << F.getName() << " | " << (V ? "true" : "false") << " |";
              Cmp->print(OS);
              for (Value *Op : Cmp->operands()) {
                OS << " |";
                if (auto *OI = dyn_cast<Instruction>(Op))
                  OI->print(OS);
                else
                  Op->printAsOperand(OS);
              }
              for (char &Ch : Line)
                if (Ch == '\n')
                  Ch = ' ';
              errs() << Line << "\n";
            }
          }
          continue;
        }
        if (!AddFlags || !isa<OverflowingBinaryOperator>(I))
          continue;
        auto *BO = cast<BinaryOperator>(I);
        if (CI.getMetadata("srange.nsw") && !BO->hasNoSignedWrap()) {
          BO->setHasNoSignedWrap(true);
          ++NSW;
        }
        if (CI.getMetadata("srange.nuw") && !BO->hasNoUnsignedWrap()) {
          BO->setHasNoUnsignedWrap(true);
          ++NUW;
        }
      }
      if (!FactPairs.empty() || (FactsMode != "none" && F.hasLocalLinkage()))
        applyFacts(F, *CF, FactPairs, FAM, FS);
      for (auto [I, CI] : More) {
        if (I->getOpcode() == Instruction::AShr) {
          auto *L = BinaryOperator::CreateLShr(I->getOperand(0), I->getOperand(1), "",
                                               I->getIterator());
          L->setIsExact(cast<BinaryOperator>(I)->isExact());
          L->takeName(I);
          I->replaceAllUsesWith(L);
          I->eraseFromParent();
          ++LShr;
          continue;
        }
        auto *II = cast<IntrinsicInst>(I);
        auto *CII = cast<IntrinsicInst>(CI);
        if (II->getIntrinsicID() != CII->getIntrinsicID())
          continue;
        unsigned K = mdconst::extract<ConstantInt>(
                         CI->getMetadata("srange.pick")->getOperand(0))->getZExtValue();
        II->replaceAllUsesWith(II->getArgOperand(K));
        II->eraseFromParent();
        ++Picks;
      }
      // Sign and width facts go before the folds, which erase comparisons.
      for (auto [I, CI] : Signs) {
        if (auto *Cmp = dyn_cast<ICmpInst>(I)) {
          if (CI->getMetadata("srange.samesign") && !Cmp->hasSameSign() &&
              Cmp->getPredicate() == cast<ICmpInst>(CI)->getPredicate()) {
            Cmp->setSameSign(true);
            ++SameSign;
          }
          continue;
        }
        if (auto *T = dyn_cast<TruncInst>(I)) {
          if (MDNode *MD = CI->getMetadata("srange.trunc")) {
            StringRef K = cast<MDString>(MD->getOperand(0))->getString();
            bool Changed = false;
            if (K != "nsw" && !T->hasNoUnsignedWrap())
              T->setHasNoUnsignedWrap(true), Changed = true;
            if (K != "nuw" && !T->hasNoSignedWrap())
              T->setHasNoSignedWrap(true), Changed = true;
            TruncFlags += Changed;
          }
          continue;
        }
        if (isa<SExtInst>(I) && CI->getMetadata("srange.nneg")) {
          auto *Z = CastInst::Create(Instruction::ZExt, I->getOperand(0), I->getType(),
                                     "", I->getIterator());
          cast<ZExtInst>(Z)->setNonNeg(true);
          Z->takeName(I);
          I->replaceAllUsesWith(Z);
          I->eraseFromParent();
          ++NNeg;
          continue;
        }
        unsigned Opc = I->getOpcode();
        if (Opc != Instruction::SDiv && Opc != Instruction::SRem &&
            Opc != Instruction::UDiv && Opc != Instruction::URem)
          continue;
        Instruction *Cur = I;
        if ((Opc == Instruction::SDiv || Opc == Instruction::SRem) &&
            CI->getMetadata("srange.unsigned")) {
          auto *U = BinaryOperator::Create(
              Opc == Instruction::SDiv ? Instruction::UDiv : Instruction::URem,
              I->getOperand(0), I->getOperand(1), "", I->getIterator());
          if (Opc == Instruction::SDiv)
            U->setIsExact(cast<BinaryOperator>(I)->isExact());
          U->takeName(I);
          I->replaceAllUsesWith(U);
          I->eraseFromParent();
          Cur = U;
          Opc = U->getOpcode();
          ++Unsigned;
        }
        MDNode *Bits = CI->getMetadata("srange.divbits");
        if (!Bits || (Opc != Instruction::UDiv && Opc != Instruction::URem))
          continue;
        unsigned Need = std::stoi(cast<MDString>(Bits->getOperand(0))->getString().str());
        unsigned W = Cur->getType()->getIntegerBitWidth();
        // Only narrowing 64-bit division to 32 bits is profitable on x86.
        if (W != 64 || Need > 32)
          continue;
        IRBuilder<> B(Cur);
        Type *I32 = B.getInt32Ty();
        Value *A = B.CreateTrunc(Cur->getOperand(0), I32, "", /*IsNUW=*/true);
        Value *D = B.CreateTrunc(Cur->getOperand(1), I32, "", /*IsNUW=*/true);
        Value *N = B.CreateBinOp(static_cast<Instruction::BinaryOps>(Opc), A, D);
        Value *Z = B.CreateZExt(N, Cur->getType(), "", /*IsNonNeg=*/true);
        Z->takeName(Cur);
        Cur->replaceAllUsesWith(Z);
        Cur->eraseFromParent();
        ++DivNarrow;
      }
      for (auto [Cmp, V] : Folds) {
        Cmp->replaceAllUsesWith(ConstantInt::getBool(Cmp->getType(), V));
        Cmp->eraseFromParent();
        ++(V ? True : False);
      }
    }
    double Secs = std::chrono::duration<double>(
                      std::chrono::steady_clock::now() - Start)
                      .count();
    errs() << "sra-cvp: {\"cmp_true\": " << True << ", \"cmp_false\": " << False
           << ", \"nsw\": " << NSW << ", \"nuw\": " << NUW
           << ", \"alias_pairs\": " << AliasPairs << ", \"samesign\": " << SameSign
           << ", \"trunc_flags\": " << TruncFlags << ", \"sext_nneg\": " << NNeg
           << ", \"to_unsigned\": " << Unsigned << ", \"div_narrowed\": " << DivNarrow
           << ", \"dead_cases\": " << DeadCases << ", \"no_default\": " << NoDefault
           << ", \"ashr_lshr\": " << LShr << ", \"minmax_abs\": " << Picks
           << ", \"no_overflow\": " << NoOverflow << ", \"fact_consts\": " << FS.Consts
           << ", \"fact_bounds\": " << FS.Bounds << ", \"fact_bits\": " << FS.Bits
           << ", \"fact_arg_attrs\": " << FS.ArgAttrs << ", \"fact_checks\": " << FS.Checks
           << ", \"fact_poison_skipped\": " << FS.PoisonSkipped
           << ", \"fact_already_known\": " << FS.Known
           << ", \"seconds\": " << format("%.3f", Secs) << "}\n";
    return True + False + NSW + NUW + AliasPairs + SameSign + TruncFlags + NNeg +
                   Unsigned + DivNarrow + DeadCases + NoDefault + LShr + Picks + NoOverflow +
                   FS.Consts + FS.Bounds + FS.Bits + FS.ArgAttrs + FS.Checks
               ? PreservedAnalyses::none()
                                    : PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
  static StringRef name() { return "sra-cvp"; }
};

} // namespace

static cl::opt<std::string> LastCleanup(
    "sra-cvp-last-cleanup", cl::init("basic"),
    cl::desc("Passes after SRA at -sra-cvp-at=last: basic (instsimplify, "
             "simplifycfg, adce: only delete code) or strong (instcombine, "
             "correlated-propagation, late simplifycfg with switch-to-lookup, "
             "instcombine, adce: use SRA's facts more, may grow code)"));

static cl::opt<bool> DropLastAssumes(
    "sra-cvp-last-drop-assumes", cl::init(false),
    cl::desc("With -sra-cvp-at=last, remove SRA's llvm.assume facts after the "
             "cleanups: no later pass uses them, but their extra uses of loop "
             "variables change the backend's loop strength reduction"));

namespace {

/// Removes the llvm.assume calls tagged !sra.fact and the conditions only
/// they use.
struct DropSRAAssumes : PassInfoMixin<DropSRAAssumes> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
    SmallVector<CallInst *> Dead;
    for (Instruction &I : instructions(F))
      if (auto *C = dyn_cast<CallInst>(&I); C && C->getMetadata("sra.fact"))
        Dead.push_back(C);
    for (CallInst *C : Dead) {
      auto *Cond = dyn_cast<Instruction>(C->getArgOperand(0));
      C->eraseFromParent();
      if (Cond && Cond->use_empty())
        Cond->eraseFromParent();
    }
    return Dead.empty() ? PreservedAnalyses::all() : PreservedAnalyses::none();
  }
};

/// Runs a function pipeline only in the functions sra-cvp may rewrite
/// (-sra-cvp-only).
struct OnlyAllowed : PassInfoMixin<OnlyAllowed> {
  explicit OnlyAllowed(FunctionPassManager FPM) : FPM(std::move(FPM)) {}
  FunctionPassManager FPM;
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
    return rewriteAllowed(F) ? FPM.run(F, FAM) : PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

} // namespace

/// Adds sra-cvp to the default pipelines as selected by -sra-cvp-at.
static void registerSRACVPExtensionPoints(PassBuilder &PB) {
  PB.registerPipelineEarlySimplificationEPCallback(
      [](ModulePassManager &MPM, OptimizationLevel L, ThinOrFullLTOPhase) {
        if ((At == "early" || At == "both") && L != OptimizationLevel::O0)
          MPM.addPass(SRACVPPass());
      });
  PB.registerOptimizerEarlyEPCallback(
      [](ModulePassManager &MPM, OptimizationLevel L, ThinOrFullLTOPhase) {
        if ((At == "optimizer-early" || At == "both") && L != OptimizationLevel::O0)
          MPM.addPass(SRACVPPass());
      });
  PB.registerOptimizerLastEPCallback(
      [](ModulePassManager &MPM, OptimizationLevel L, ThinOrFullLTOPhase) {
        if (At != "last" || L == OptimizationLevel::O0)
          return;
        MPM.addPass(SRACVPPass());
        FunctionPassManager FPM;
        if (LastCleanup == "strong") {
          FPM.addPass(InstCombinePass());
          FPM.addPass(CorrelatedValuePropagationPass());
          // The options of -O3's late simplifycfg.
          FPM.addPass(SimplifyCFGPass(SimplifyCFGOptions()
                                          .forwardSwitchCondToPhi(true)
                                          .convertSwitchRangeToICmp(true)
                                          .convertSwitchToLookupTable(true)
                                          .needCanonicalLoops(false)
                                          .hoistCommonInsts(true)
                                          .sinkCommonInsts(true)));
          FPM.addPass(InstCombinePass());
        } else {
          FPM.addPass(InstSimplifyPass());
          FPM.addPass(SimplifyCFGPass());
        }
        if (DropLastAssumes)
          FPM.addPass(DropSRAAssumes());
        FPM.addPass(ADCEPass());
        MPM.addPass(createModuleToFunctionPassAdaptor(OnlyAllowed(std::move(FPM))));
        MPM.addPass(GlobalDCEPass());
      });
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "SRACVP", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            registerSRACVPExtensionPoints(PB);
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name != "sra-cvp")
                    return false;
                  MPM.addPass(SRACVPPass());
                  return true;
                });
          }};
}
