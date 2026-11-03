//===- SymbolicRangeAnalysis.cpp - Symbolic range analysis pass -----------===//
//
/// \file
/// Implements symbolic range analysis (Nazaré et al., OOPSLA'14) on e-SSA form:
/// a fixpoint over symbolic intervals, with delayed widening at phi nodes and a
/// narrowing phase that recovers the precision lost to widening.
///
/// Values of an integer type iN are their signed interpretation. Symbols
/// (arguments, loads, calls and instructions the analysis does not model) are
/// bounded by their type and by LLVM's range attributes and !range metadata.
/// These bounds decide casts and bitwise operations, and give each result a
/// numeric range in addition to its symbolic one.
//
//===----------------------------------------------------------------------===//

#include <chrono>
#include "SymbolicRangeAnalysis.h"
#include "ExactValues.h"
#include "SymBoxes.h"
#include "GiNaCGlue.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Module.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Plugins/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

using namespace llvm;
using GiNaC::numeric;
using SE = symboxes::SymExpr;
using SR = symboxes::SymRange;

static cl::opt<bool> PrintStats(
    "sra-stats", cl::init(false), cl::Hidden,
    cl::desc("Print per-function solver statistics to stderr"));
static cl::opt<bool> UseExact(
    "sra-exact", cl::init(true),
    cl::desc("Decide comparisons that the ranges do not with exact values: "
             "linear equalities between variables (ExactValues)"));
static cl::opt<bool> ExactStats(
    "sra-exact-stats", cl::init(false), cl::Hidden,
    cl::desc("Print how many comparisons the exact values decided"));
/// The number of comparisons decided by ExactValues in the current module.
static unsigned ExactDecided = 0;
static cl::opt<bool> UseMemoOpt(
    "sra-memo", cl::init(true), cl::Hidden,
    cl::desc("Memoize symbolic sums and differences"),
    cl::cb<void, bool>([](bool B) { symboxes::UseMemo = B; }));
static cl::opt<bool> AliasFacts(
    "sra-alias", cl::init(false),
    cl::desc("Annotate pairs of memory accesses whose byte ranges are "
             "provably disjoint (!srange.noalias, by !sra.id)"));
static cl::opt<bool> InBoundsFacts(
    "sra-inbounds", cl::init(false),
    cl::desc("Annotate loads and stores whose bytes provably lie inside their "
             "object (alloca, global, allocation call): !srange.inbounds"));
static cl::opt<unsigned> AliasMaxGroup(
    "sra-alias-max-group", cl::init(256), cl::Hidden,
    cl::desc("Most accesses per base pointer considered for alias facts"));
static uint64_t StatAliasPairs = 0, StatAliasSymbolic = 0, StatAcc = 0, StatAccNoOff = 0, StatAccFull = 0, StatAccLoopBase = 0, StatCand = 0;

static cl::opt<bool> Incremental(
    "sra-incremental", cl::init(true), cl::Hidden,
    cl::desc("Reuse an instruction's last transfer result when none of the "
             "states it read has changed (same results, less work)"));
static uint64_t StatReused = 0;
static unsigned StatRounds = 0, StatNarrowRounds = 0;
static uint64_t StatTransfers = 0;

static cl::opt<unsigned> MaxExprArgs(
    "sra-max-expr-args", cl::init(8),
    cl::desc("min/max bounds with more arguments are widened to -inf/+inf"));
static cl::opt<unsigned> MaxExprNodes(
    "sra-max-expr-nodes", cl::init(64),
    cl::desc("Bounds with more nodes are widened to -inf/+inf"));
static cl::opt<unsigned> NarrowingRounds(
    "sra-narrowing-rounds", cl::init(8),
    cl::desc("Maximum number of narrowing rounds after the fixpoint (0 "
             "disables narrowing)"));
static cl::opt<bool> UseThresholds(
    "sra-widening-thresholds", cl::init(true),
    cl::desc("Widen loop phis to symbolic thresholds taken from the loop's "
             "comparisons before widening to -inf/+inf"));
static cl::opt<bool> UseGuardFacts(
    "sra-guard-facts", cl::init(true),
    cl::desc("Use the branch conditions on symbols (sigma nodes) that hold at "
             "an instruction to simplify its bounds"));
static cl::opt<bool> ResolveLoopVariant(
    "sra-resolve-loop-variant", cl::init(true),
    cl::desc("At loop headers, replace symbols defined inside the loop by "
             "their bounds (without this, ranges carried around a loop may "
             "refer to a load of an earlier iteration: unsound)"));
static cl::opt<bool> UseExactSymbols(
    "sra-exact-symbols", cl::init(true),
    cl::desc("In add/sub/mul, also read an operand that is a kernel value "
             "(through sigma nodes) as its own symbol, so that bounds cancel "
             "(j - i in [0, 9] from j in [i, i + 9])"));
static cl::opt<bool> UseInterprocedural(
    "sra-interprocedural", cl::init(true),
    cl::desc("Bound the parameters of functions whose every call site is "
             "known by the arguments of those calls (assumes the module is a "
             "whole program)"));
static cl::opt<bool> UseTypeBounds(
    "sra-type-bounds", cl::init(true),
    cl::desc("Bound symbols by their type and by LLVM's range facts"));

static constexpr int WidenThreshold = 3;
/// How deep onEdge refines the other operands of a branch's comparisons.
static constexpr unsigned EdgeDepth = 3;

/// Returns the signed range of an N-bit integer.
static std::pair<numeric, numeric> typeRange(unsigned N) {
  numeric Half = pow(numeric(2), numeric(N - 1));
  return {-Half, Half - 1};
}

static numeric pow2(unsigned K) { return pow(numeric(2), numeric(K)); }

/// Returns \p N as a constant bound, saturated to -inf or +inf if it does not
/// fit in SymExpr::Width bits.
static SE numE(const numeric &N) {
  if (auto A = ginac_glue::toAPInt(N, SE::Width))
    return SE::num(*A);
  return N.is_positive() ? SE::inf() : SE::negInf();
}

static std::string toString(const numeric &N) {
  std::ostringstream SS;
  SS << N;
  return SS.str();
}

/// Returns true if \p V has the same value on every iteration of \p L: it is
/// defined outside \p L, or is pure arithmetic or a cast of such values, such
/// as a bound `n + 8` that code at -O0 recomputes in the loop header.
static bool isLoopInvariantValue(Value *V, Loop *L, unsigned Depth = 0) {
  auto *I = dyn_cast<Instruction>(V);
  if (!I || !L->contains(I))
    return true;
  if (Depth > 4 || !(isa<BinaryOperator>(I) || isa<CastInst>(I)) ||
      I->mayReadOrWriteMemory())
    return false;
  return all_of(I->operands(), [&](Value *Op) {
    return isLoopInvariantValue(Op, L, Depth + 1);
  });
}

/// Follows sigma nodes back to the value they rename.
static Value *throughSigmas(Value *V) {
  while (auto *Phi = dyn_cast<PHINode>(V)) {
    if (!Phi->getMetadata("sigma"))
      break;
    V = Phi->getIncomingValue(0);
  }
  return V;
}

namespace {

/// Information from the call sites of a function about its integer parameters:
/// the numeric hull of each argument over all calls, and the pairs (i, j) such
/// that every call passes argument i below argument j (OOPSLA'14, Fig. 19).
struct CallSummary {
  unsigned Sites = 0;
  SmallVector<std::optional<std::pair<numeric, numeric>>, 4> Hull;
  SmallVector<SmallVector<bool, 4>, 4> Less;
};
using SummaryMap = DenseMap<Function *, CallSummary>;

class Solver {
public:
  Solver(Function &F, LoopInfo &LI, DominatorTree &DT,
         const SymbolicRangeAnalysis::ArgRangeMap &ArgRanges,
         const CallSummary *Summary);
  void run();
  void annotate();
  /// Adds what this function's calls to \p Eligible functions say about their
  /// parameters to \p Summaries.
  void summarizeCalls(SummaryMap &Summaries,
                      const DenseSet<Function *> &Eligible);

private:
  /// Computes one fixpoint: an ascending phase with widening, then a descending
  /// phase with narrowing.
  void solve();
  /// Returns the bounds of a loop header phi given by the loop's exit test: i =
  /// phi(init, i + 1) with exit test i < n lies in [init, max(init, n)].
  std::optional<SR> loopBound(PHINode *Phi);
  /// Returns the largest value the loop body sees for a loop counter Phi =
  /// phi(init, Phi + s) with s > 1, tested at the top of its loop with Phi < N
  /// or Phi <= N: init + s * ((N - 1 - init) / s). Only values init + k * s
  /// occur, so this is tighter than N - 1 (12 rather than 15 for i < 16
  /// stepping by 4).
  std::optional<SE> strideBodyMax(PHINode *Phi);
  /// Widens \p Phi from \p Old to \p New: an unstable bound moves to the
  /// tightest threshold (see thresholds()) that provably covers it, or to
  /// infinity if there is none.
  SR widenPhi(PHINode *Phi, const SR &Old, const SR &New);
  /// Returns \p R with the symbols that loop \p L redefines on each iteration,
  /// such as loads inside it, resolved to their numeric bounds. Every value
  /// that flows around the back edge of L goes through a phi of its header and
  /// must not keep such symbols, since they denote new values in the next
  /// iteration (for example highest <= p for a running maximum of loads p).
  SR resolveLoopVariant(const SR &R, Loop *L);
  /// Applies resolveLoopVariant() for the loop that \p Phi heads, if any.
  SR resolveAtHeader(PHINode *Phi, const SR &R);
  /// Returns the loop-invariant integers compared inside \p L, whose ranges are
  /// the symbolic widening thresholds.
  ArrayRef<Value *> thresholds(Loop *L);
  using Bounds = std::optional<std::pair<numeric, numeric>>;

  SR getState(Value *V);
  SR transfer(Instruction &I);
  SR binaryOp(BinaryOperator &I, const SR &L, const SR &R);
  SR binaryOp(unsigned Opc, Type *Ty, const SR &L, const SR &R);
  static std::optional<unsigned> overflowOpcode(Value *V);
  SR castOp(CastInst &I, const SR &R);
  SR intrinsicOp(IntrinsicInst &II);
  SR applyConstraint(SR R, ICmpInst *Cmp, Value *SigmaVar, bool IsTrueSide);
  /// Collects into \p Out the comparisons, each with the side on which it
  /// holds, implied by taking the \p Side edge of a branch on \p Cond: the
  /// condition itself, or the leaves of a logical and (true edge), or (false
  /// edge) or not.
  static void impliedComparisons(Value *Cond, bool Side,
                                 SmallVectorImpl<std::pair<ICmpInst *, bool>> &Out,
                                 unsigned Depth = 0);

  /// Returns the numeric bounds of the symbol \p V: its type range, narrowed by
  /// range facts and by the sigma nodes of V that dominate the current block.
  Bounds symbolBounds(Value *V);
  /// Returns the bounds of \p V from its type and LLVM's range facts only.
  Bounds baseBounds(Value *V);
  /// Makes \p BB the block whose facts apply, or no block if null.
  void setContext(BasicBlock *BB);
  /// Turns the less-than facts about parameters on or off.
  void enableParamFacts(bool On);
  /// Returns the numeric hull of \p R, clamped to the range of \p Ty.
  symboxes::NumInterval hull(const SR &R, Type *Ty);
  /// Returns true if \p R provably lies within the range of \p Ty.
  bool fitsType(const SR &R, Type *Ty);
  /// Returns \p R with its infinite bounds replaced by the limits of \p Ty. A
  /// value of type Ty never leaves them, and a cast to a wider type must keep
  /// that fact.
  SR clampToType(const SR &R, Type *Ty);
  bool nonNeg(const SR &R, Type *Ty);
  /// Returns the value \p Cmp always has where it is, if the ranges of its
  /// operands decide it, such as i < n inside a loop whose exit test is i < n -
  /// 1.
  std::optional<bool> decideCmp(ICmpInst &Cmp);
  /// Tags \p I with !srange.nsw and !srange.nuw if the ranges of its operands
  /// prove that it cannot wrap and it is not marked so already.
  void annotateNoWrap(Instruction &I);
  void annotateAlias();
  void annotateInBounds();
  std::optional<SE> objectSize(Value *Base);
  void annotateSigns(Instruction &I);
  void annotateCVP(Instruction &I);
  bool provablyNonNeg(Value *V);
  std::optional<SR> offsetRange(Value *Ptr, Value *&Base);
  bool negative(const SR &R, Type *Ty);
  /// Returns the value of a singleton constant range.
  std::optional<APInt> constOf(const SR &R);

  Function &F;
  LoopInfo &LI;
  DominatorTree &DT;
  /// Sigma nodes of each value, i.e. the places where a branch refines it.
  DenseMap<Value *, SmallVector<PHINode *, 2>> SigmasOf;
  BasicBlock *Ctx = nullptr;
  /// The block of the sigma node being computed. On its incoming edge, the
  /// operands of the branch's comparisons have the ranges of their sigma nodes.
  BasicBlock *SigmaBlock = nullptr;
  /// Returns the range of \p V on the edge into SigmaBlock, computed from the
  /// current states: the state of V intersected with the edge's comparisons on
  /// V, and V evaluated again from the ranges of its operands on the edge,
  /// refined the same way up to \p Depth levels deep. It never reads the stored
  /// states of the edge's sigma nodes, since two sigma nodes that refine each
  /// other would keep the small early values of the fixpoint iteration (n in
  /// [1, 1] from i + 1 == n).
  std::optional<SR> onEdge(Value *V, unsigned Depth);
  /// Returns the constraint of \p Cmp on \p SigmaVar, given the range \p Other
  /// of the other operand.
  SR constrain(SR R, ICmpInst *Cmp, Value *SigmaVar, bool IsTrueSide,
               const SR &Other);
  std::function<Bounds(Value *)> ContextFn;
  /// Call-site information about this function's parameters, if any.
  const CallSummary *Summary;
  /// Symbolic facts about parameters from the less-than relations.
  DenseMap<Value *, symboxes::SymFacts> ParamFacts;
  std::function<symboxes::SymFacts(Value *)> FactsFn;
  const SymbolicRangeAnalysis::ArgRangeMap &ArgRanges;
  /// Arithmetic without nsw whose range did not fit its type. It may wrap
  /// around, so its result is the full range.
  DenseSet<Instruction *> Wrapping;
  DenseMap<Value *, SR> State;
  DenseMap<Value *, int> IterCount;

  // Incremental evaluation: the version at which each state last changed, and
  // for each instruction its last transfer result and the states it read.
  struct Memo {
    SR Result;
    unsigned Version = 0;
    SmallVector<Value *, 4> Deps;
  };
  DenseMap<Value *, unsigned> ChangedAt;
  DenseMap<Instruction *, Memo> Memos;
  unsigned Version = 0;
  SmallVectorImpl<Value *> *Reads = nullptr;
  SR cachedTransfer(Instruction &I);
  void setState(Instruction &I, SR &Old, const SR &NewR) {
    Old = NewR;
    ChangedAt[&I] = ++Version;
  }
  DenseMap<Value *, Bounds> SymBounds;
  DenseMap<Loop *, SmallVector<Value *, 4>> Thresholds;
};

} // namespace

Solver::Solver(Function &F, LoopInfo &LI, DominatorTree &DT,
               const SymbolicRangeAnalysis::ArgRangeMap &ArgRanges,
               const CallSummary *Summary)
    : F(F), LI(LI), DT(DT), ArgRanges(ArgRanges), Summary(Summary) {
  ginac_glue::resetSymbols();
  if (Summary && Summary->Sites)
    for (unsigned I = 0; I < F.arg_size(); ++I)
      for (unsigned J = 0; J < F.arg_size(); ++J)
        if (I != J && Summary->Less[I][J]) {
          // Every call passes arg I below arg J: p_I <= p_J - 1.
          Value *PI = F.getArg(I), *PJ = F.getArg(J);
          auto &FI = ParamFacts[PI], &FJ = ParamFacts[PJ];
          SE Up = SE::sub(SE::sym(PJ), SE::num(1));
          FI.second = FI.second ? SE::mkMin(*FI.second, Up) : Up;
          SE Down = SE::add(SE::sym(PI), SE::num(1));
          FJ.first = FJ.first ? SE::mkMax(*FJ.first, Down) : Down;
        }
  FactsFn = [this](Value *V) -> symboxes::SymFacts {
    auto It = ParamFacts.find(V);
    return It == ParamFacts.end() ? symboxes::SymFacts() : It->second;
  };
  if (UseGuardFacts)
    for (Instruction &I : instructions(F))
      if (auto *Phi = dyn_cast<PHINode>(&I))
        if (Phi->getMetadata("sigma"))
          SigmasOf[throughSigmas(Phi)].push_back(Phi);
  ContextFn = [this](Value *V) { return symbolBounds(V); };
}

void Solver::setContext(BasicBlock *BB) {
  Ctx = BB;
  symboxes::setContextBounds(UseGuardFacts && BB ? &ContextFn : nullptr);
}

void Solver::enableParamFacts(bool On) {
  // Unlike guard facts, these come from call sites rather than from the states
  // being computed, so they hold everywhere in the function.
  symboxes::setSymbolicFacts(On && !ParamFacts.empty() ? &FactsFn : nullptr);
}

void Solver::summarizeCalls(SummaryMap &Summaries,
                            const DenseSet<Function *> &Eligible) {
  enableParamFacts(true);
  auto Off = make_scope_exit([this] { enableParamFacts(false); });
  for (Instruction &I : instructions(F)) {
    auto *CB = dyn_cast<CallBase>(&I);
    Function *G = CB ? CB->getCalledFunction() : nullptr;
    if (!G || !Eligible.count(G) || CB->arg_size() != G->arg_size())
      continue;
    setContext(CB->getParent());
    unsigned N = G->arg_size();
    SmallVector<SR, 4> Args;
    bool Reachable = true;
    for (unsigned K = 0; K < N; ++K) {
      Args.push_back(G->getArg(K)->getType()->isIntegerTy()
                         ? getState(CB->getArgOperand(K))
                         : SR::full());
      Reachable &= !Args.back().isBottom;
    }
    if (!Reachable) // a call in unreachable code says nothing
      continue;
    CallSummary &S = Summaries[G];
    bool First = S.Sites++ == 0;
    if (First) {
      S.Hull.assign(N, std::nullopt);
      S.Less.assign(N, SmallVector<bool, 4>(N, true));
    }
    for (unsigned K = 0; K < N; ++K) {
      Type *Ty = G->getArg(K)->getType();
      if (!Ty->isIntegerTy())
        continue;
      auto H = hull(Args[K], Ty);
      if (!H.Lo || !H.Hi)
        continue;
      auto &Acc = S.Hull[K];
      if (First)
        Acc = std::make_pair(*H.Lo, *H.Hi);
      else if (Acc)
        Acc = std::make_pair(std::min(Acc->first, *H.Lo),
                             std::max(Acc->second, *H.Hi));
    }
    for (unsigned A = 0; A < N; ++A)
      for (unsigned B = 0; B < N; ++B)
        if (A != B && S.Less[A][B])
          S.Less[A][B] =
              G->getArg(A)->getType() == G->getArg(B)->getType() &&
              G->getArg(A)->getType()->isIntegerTy() &&
              SE::provablyLE(SE::add(Args[A].Upper, SE::num(1)),
                             Args[B].Lower);
  }
  // A function without reachable calls keeps Sites at 0, meaning no
  // information.
  setContext(nullptr);
}

void Solver::solve() {
  State.clear();
  IterCount.clear();
  ChangedAt.clear();
  Memos.clear();
  Version = 0;
  enableParamFacts(true);
  auto Off = make_scope_exit([this] { enableParamFacts(false); });
  for (Argument &Arg : F.args()) {
    auto It = ArgRanges.find(Arg.getName().str());
    if (It != ArgRanges.end())
      State[&Arg] = SR::of(SE::num(It->second.first),
                           SE::num(It->second.second));
    else
      State[&Arg] = SR::single(SE::sym(&Arg));
  }

  ReversePostOrderTraversal<Function *> RPOT(&F);

  // Ascending phase. Reverse post-order keeps the number of rounds low. Phis
  // are widened after WidenThreshold evaluations, to the bounds of their loop's
  // exit test when there are some. Facts and thresholds make the transfer
  // functions non-monotone, so after MaxRounds the phis that still change go to
  // the full range, which guarantees termination.
  constexpr unsigned MaxRounds = 60;
  bool Changed = true;
  for (unsigned Round = 0; Changed; ++Round) {
    Changed = false;
    StatRounds = Round + 1;
    for (BasicBlock *BB : RPOT) {
      setContext(BB);
      for (Instruction &I : *BB) {
        ++StatTransfers;
        SR NewR = cachedTransfer(I);
        if (auto *Phi = dyn_cast<PHINode>(&I)) {
          int &Cnt = IterCount[&I];
          if (++Cnt > WidenThreshold) {
            auto It = State.find(&I);
            if (It != State.end() && !It->second.isBottom) {
              // Sigma nodes are not widened. They are not loop-carried, since
              // the loop phis they depend on are widened, and threshold
              // widening proves a candidate bound with the guard facts of the
              // current block, which come from the states of sibling sigma
              // nodes in earlier rounds: two sigma nodes widened to the same
              // threshold could justify each other.
              if (!Phi->getMetadata("sigma")) {
                NewR = widenPhi(Phi, It->second, NewR);
                if (auto LB = loopBound(Phi))
                  NewR = resolveAtHeader(Phi, NewR.narrow(*LB));
              }
              if (Round >= MaxRounds && !(NewR == It->second))
                NewR = SR::full();
            }
          }
        }
        auto &Old = State[&I];
        if (!(NewR == Old)) {
          setState(I, Old, NewR);
          Changed = true;
        }
      }
    }
  }

  // Descending phase: re-evaluate from the post-fixpoint and keep every bound
  // that gets provably tighter, in particular the infinite ones.
  for (unsigned Round = 0; Round < NarrowingRounds; ++Round) {
    StatNarrowRounds = Round + 1;
    Changed = false;
    for (BasicBlock *BB : RPOT) {
      setContext(BB);
      for (Instruction &I : *BB) {
        SR T = cachedTransfer(I);
        auto &Old = State[&I];
        SR NewR = Old.narrow(T);
        if (!(NewR == Old)) {
          setState(I, Old, NewR);
          Changed = true;
        }
      }
    }
    if (!Changed)
      break;
  }
  setContext(nullptr);
}

SR Solver::cachedTransfer(Instruction &I) {
  if (!Incremental)
    return transfer(I);
  auto [It, New] = Memos.try_emplace(&I);
  Memo &M = It->second;
  if (!New && all_of(M.Deps, [&](Value *D) {
        auto C = ChangedAt.find(D);
        return C == ChangedAt.end() || C->second <= M.Version;
      })) {
    ++StatReused;
    return M.Result;
  }
  SmallVector<Value *, 8> Rd;
  Reads = &Rd;
  SR R = transfer(I);
  Reads = nullptr;
  // Look the memo up again, in case transfer() grew Memos.
  Memo &M2 = Memos[&I];
  M2.Version = Version;
  M2.Deps.assign(Rd.begin(), Rd.end());
  llvm::sort(M2.Deps);
  M2.Deps.erase(std::unique(M2.Deps.begin(), M2.Deps.end()), M2.Deps.end());
  M2.Result = R;
  return R;
}

ArrayRef<Value *> Solver::thresholds(Loop *L) {
  auto [It, Inserted] = Thresholds.try_emplace(L);
  if (Inserted)
    for (BasicBlock *BB : L->blocks())
      for (Instruction &I : *BB)
        if (auto *Cmp = dyn_cast<ICmpInst>(&I))
          for (Value *Op : Cmp->operands()) {
            auto *OpI = dyn_cast<Instruction>(Op);
            if (Op->getType()->isIntegerTy() && !(OpI && L->contains(OpI)) &&
                !is_contained(It->second, Op))
              It->second.push_back(Op);
          }
  return It->second;
}

SR Solver::widenPhi(PHINode *Phi, const SR &Old, const SR &New) {
  SR W = Old.widen(New);
  if (!UseThresholds || W.isBottom ||
      (W.Lower.kind() != SE::NegInf && W.Upper.kind() != SE::PosInf))
    return W;
  Loop *L = LI.getLoopFor(Phi->getParent());
  if (!L)
    return W;

  // Candidates: t + d for every threshold t and d in -1..1, alone and combined
  // with the values entering the loop (such as max(init, n)), which makes a
  // symbolic candidate provable while the bound is still a number.
  SmallVector<SR, 4> Entries;
  for (unsigned K = 0; K < Phi->getNumIncomingValues(); ++K)
    if (!L->contains(Phi->getIncomingBlock(K))) {
      SR E = getState(Phi->getIncomingValue(K));
      if (!E.isBottom)
        Entries.push_back(E);
    }
  std::vector<SE> Up, Down;
  for (Value *T : thresholds(L)) {
    SR RT = getState(T);
    if (RT.isBottom)
      continue;
    for (int64_t D = -1; D <= 1; ++D) {
      SE U = SE::add(RT.Upper, SE::num(D)), Lo = SE::add(RT.Lower, SE::num(D));
      Up.push_back(U);
      Down.push_back(Lo);
      for (const SR &E : Entries) {
        Up.push_back(SE::mkMax(E.Upper, U));
        Down.push_back(SE::mkMin(E.Lower, Lo));
      }
    }
  }

  // The tightest candidates that cover both the old and the new bound. The min
  // (or max) of all valid candidates is valid too.
  SE Hi = W.Upper, Lo = W.Lower;
  if (Hi.kind() == SE::PosInf) {
    SE Best = SE::inf();
    for (const SE &T : Up)
      if (SE::provablyLE(New.Upper, T) && SE::provablyLE(Old.Upper, T))
        Best = SE::mkMin(Best, T);
    Hi = Best;
  }
  if (Lo.kind() == SE::NegInf) {
    SE Best = SE::negInf();
    for (const SE &T : Down)
      if (SE::provablyLE(T, New.Lower) && SE::provablyLE(T, Old.Lower))
        Best = SE::mkMax(Best, T);
    Lo = Best;
  }
  return SR::of(Lo, Hi);
}


SR Solver::resolveLoopVariant(const SR &R, Loop *L) {
  if (R.isBottom)
    return R;
  auto Drop = [L](Value *V) {
    auto *I = dyn_cast<Instruction>(V);
    return I && L->contains(I);
  };
  auto Num = [this](Value *V) { return baseBounds(V); };
  return SR::of(SE::resolve(R.Lower, /*Upper=*/false, Drop, Num),
                SE::resolve(R.Upper, /*Upper=*/true, Drop, Num));
}

SR Solver::resolveAtHeader(PHINode *Phi, const SR &R) {
  Loop *L = LI.getLoopFor(Phi->getParent());
  if (!ResolveLoopVariant || !L || L->getHeader() != Phi->getParent())
    return R;
  return resolveLoopVariant(R, L);
}

std::optional<SE> Solver::strideBodyMax(PHINode *Phi) {
  Loop *L = LI.getLoopFor(Phi->getParent());
  if (!L || L->getHeader() != Phi->getParent() ||
      Phi->getNumIncomingValues() != 2 || Phi->getMetadata("sigma"))
    return std::nullopt;
  unsigned Back = L->contains(Phi->getIncomingBlock(0)) ? 0 : 1;
  if (!L->contains(Phi->getIncomingBlock(Back)) ||
      L->contains(Phi->getIncomingBlock(1 - Back)))
    return std::nullopt;
  auto *Next =
      dyn_cast<BinaryOperator>(throughSigmas(Phi->getIncomingValue(Back)));
  if (!Next || Next->getOpcode() != Instruction::Add ||
      !Next->hasNoSignedWrap())
    return std::nullopt;
  auto *C = dyn_cast<ConstantInt>(Next->getOperand(1));
  if (!C || throughSigmas(Next->getOperand(0)) != Phi ||
      C->getBitWidth() > 64 || C->getSExtValue() <= 1)
    return std::nullopt;
  int64_t Step = C->getSExtValue();
  Value *Init = Phi->getIncomingValue(1 - Back);
  SR RI = getState(Init);
  if (RI.isBottom || RI.Upper.isInf())
    return std::nullopt;
  // With a start of one exact value, the values are init + k * s.
  bool ExactInit = RI.Lower == RI.Upper;
  // The test at the top of the loop, on the phi itself: the body only runs
  // for values that pass it.
  auto *Br = dyn_cast<BranchInst>(Phi->getParent()->getTerminator());
  if (!Br || !Br->isConditional())
    return std::nullopt;
  auto *Cmp = dyn_cast<ICmpInst>(Br->getCondition());
  if (!Cmp)
    return std::nullopt;
  bool InT = L->contains(Br->getSuccessor(0)),
       InF = L->contains(Br->getSuccessor(1));
  if (InT == InF)
    return std::nullopt;
  CmpInst::Predicate Pred = Cmp->getPredicate();
  Value *Tested = Cmp->getOperand(0), *Bound = Cmp->getOperand(1);
  if (throughSigmas(Bound) == Phi) {
    std::swap(Tested, Bound);
    Pred = CmpInst::getSwappedPredicate(Pred);
  }
  if (throughSigmas(Tested) != Phi)
    return std::nullopt;
  if (!InT)
    Pred = CmpInst::getInversePredicate(Pred);
  if (!isLoopInvariantValue(Bound, L))
    return std::nullopt;
  SR RN = getState(Bound);
  if (RN.isBottom || RN.Upper.isInf())
    return std::nullopt;
  // A bound init + C on the same start (for (x = b; x < b + 8; x += 4)):
  // the body sees at most init + s * ((C - 1) / s), whatever init is.
  std::optional<int64_t> Offset;
  {
    Value *B = Bound;
    while (auto *Cast = dyn_cast<SExtInst>(B))
      B = Cast->getOperand(0);
    if (auto *Add = dyn_cast<BinaryOperator>(B))
      if (Add->getOpcode() == Instruction::Add && Add->hasNoSignedWrap())
        if (auto *K = dyn_cast<ConstantInt>(Add->getOperand(1)))
          if (throughSigmas(Add->getOperand(0)) == throughSigmas(Init) &&
              K->getBitWidth() <= 64)
            Offset = K->getSExtValue();
  }
  if (!ExactInit && !Offset)
    return std::nullopt;
  if (ICmpInst::isUnsigned(Pred)) {
    Type *Ty = Phi->getType();
    if (!nonNeg(RI, Ty) || !nonNeg(RN, Ty))
      return std::nullopt;
    Pred = ICmpInst::getSignedPredicate(Pred);
  }
  SE Top; // the largest value that passes the test
  if (Pred == ICmpInst::ICMP_SLT)
    Top = SE::sub(RN.Upper, SE::num(1));
  else if (Pred == ICmpInst::ICMP_SLE)
    Top = RN.Upper;
  else
    return std::nullopt;
  SE S = SE::num(Step);
  std::optional<SE> M;
  if (Offset) {
    int64_t Span = Pred == ICmpInst::ICMP_SLT ? *Offset - 1 : *Offset;
    if (Span >= 0)
      M = SE::add(RI.Upper, SE::num(Step * (Span / Step)));
  }
  // The body runs only if init <= Top, so (Top - init) / s truncates as a
  // floor division would.
  if (ExactInit) {
    SE E = SE::add(RI.Lower, SE::mul(S, SE::div(SE::sub(Top, RI.Lower), S)));
    M = M ? SE::mkMin(*M, E) : E;
  }
  return M;
}

std::optional<SR> Solver::loopBound(PHINode *Phi) {
  Loop *L = LI.getLoopFor(Phi->getParent());
  if (!L || L->getHeader() != Phi->getParent() ||
      Phi->getNumIncomingValues() != 2 || Phi->getMetadata("sigma"))
    return std::nullopt;
  unsigned Back = L->contains(Phi->getIncomingBlock(0)) ? 0 : 1;
  if (!L->contains(Phi->getIncomingBlock(Back)) ||
      L->contains(Phi->getIncomingBlock(1 - Back)))
    return std::nullopt;
  Value *Init = Phi->getIncomingValue(1 - Back);

  // The value coming around (possibly renamed by sigma nodes on the back
  // edge) must be phi + c that cannot wrap: nsw, or nuw when the values stay
  // non-negative (checked below, once the bounds are known).
  auto *Next =
      dyn_cast<BinaryOperator>(throughSigmas(Phi->getIncomingValue(Back)));
  if (!Next || (Next->getOpcode() != Instruction::Add &&
                Next->getOpcode() != Instruction::Sub))
    return std::nullopt;
  bool NUWOnly = !Next->hasNoSignedWrap() && Next->hasNoUnsignedWrap();
  if (!Next->hasNoSignedWrap() && !NUWOnly)
    return std::nullopt;
  auto *C = dyn_cast<ConstantInt>(Next->getOperand(1));
  if (!C || throughSigmas(Next->getOperand(0)) != Phi ||
      C->getBitWidth() > 64)
    return std::nullopt;
  int64_t Step = C->getSExtValue();
  if (Next->getOpcode() == Instruction::Sub)
    Step = -Step;
  if (Step == 0)
    return std::nullopt;

  SR RI = getState(Init);
  if (RI.isBottom)
    return std::nullopt;

  // Every iteration passes a test before it can reach the back edge: in the
  // header (test at the top, on the phi) or in the latch (a rotated loop,
  // test at the bottom, usually on Next). The latch may sit behind the block
  // ESSAfier split off the back edge.
  BasicBlock *Latch = Phi->getIncomingBlock(Back);
  SmallVector<BasicBlock *, 3> Tests = {Phi->getParent(), Latch};
  if (BasicBlock *Pred = Latch->getSinglePredecessor())
    if (L->contains(Pred) && isa<BranchInst>(Latch->getTerminator()) &&
        !cast<BranchInst>(Latch->getTerminator())->isConditional())
      Tests.push_back(Pred);

  std::optional<SR> Result;
  for (BasicBlock *TestBB : Tests) {
    auto *Br = dyn_cast<BranchInst>(TestBB->getTerminator());
    if (!Br || !Br->isConditional())
      continue;
    auto *Cmp = dyn_cast<ICmpInst>(Br->getCondition());
    if (!Cmp)
      continue;
    bool InT = L->contains(Br->getSuccessor(0)),
         InF = L->contains(Br->getSuccessor(1));
    if (InT == InF)
      continue;
    CmpInst::Predicate Pred = Cmp->getPredicate();
    Value *Tested = Cmp->getOperand(0), *Bound = Cmp->getOperand(1);
    if (throughSigmas(Bound) == Phi || throughSigmas(Bound) == Next) {
      std::swap(Tested, Bound);
      Pred = CmpInst::getSwappedPredicate(Pred);
    }
    Value *T = throughSigmas(Tested);
    bool Post = T == Next; // the test sees the incremented value
    if (T != Phi && !Post)
      continue;
    if (!InT) // the loop continues while the test is false
      Pred = CmpInst::getInversePredicate(Pred);
    if (!isLoopInvariantValue(Bound, L))
      continue;
    SR RN = getState(Bound);
    if (RN.isBottom)
      continue;
    // With only nuw, the values cannot step past a non-negative bound from a
    // non-negative start without wrapping around 2^N, which nuw forbids.
    if (NUWOnly && !(nonNeg(RI, Phi->getType()) && nonNeg(RN, Phi->getType())))
      continue;
    if (ICmpInst::isUnsigned(Pred)) {
      Type *Ty = Phi->getType();
      if (!nonNeg(RI, Ty) || !nonNeg(RN, Ty))
        continue;
      Pred = ICmpInst::getSignedPredicate(Pred);
    }

    // Header values are Init, or Next = x + Step where the tested value
    // (x before the increment, Next after it) passed the test. With nsw
    // nothing wraps; a loop that steps over its bound under != would
    // overflow, which is undefined behavior.
    SE S = SE::num(Step);
    std::optional<SE> Last;
    if (Step > 0) {
      if (Pred == ICmpInst::ICMP_SLT)
        Last = SE::add(RN.Upper, SE::num(Post ? -1 : Step - 1));
      else if (Pred == ICmpInst::ICMP_SLE)
        Last = Post ? RN.Upper : SE::add(RN.Upper, S);
      else if (Pred == ICmpInst::ICMP_NE)
        Last = Post ? SE::sub(RN.Upper, S) : RN.Upper;
      // A stride: the last value is the largest passing one plus the step.
      if (Last && !Post && TestBB == Phi->getParent() &&
          (Pred == ICmpInst::ICMP_SLT || Pred == ICmpInst::ICMP_SLE))
        if (auto M = strideBodyMax(Phi))
          Last = SE::mkMin(*Last, SE::add(*M, S));
      if (!Last)
        continue;
      SR B = SR::of(RI.Lower, SE::mkMax(RI.Upper, *Last));
      Result = Result ? Result->narrow(B) : B;
    } else {
      if (Pred == ICmpInst::ICMP_SGT)
        Last = SE::add(RN.Lower, SE::num(Post ? 1 : Step + 1));
      else if (Pred == ICmpInst::ICMP_SGE)
        Last = Post ? RN.Lower : SE::add(RN.Lower, S);
      else if (Pred == ICmpInst::ICMP_NE)
        Last = Post ? SE::sub(RN.Lower, S) : RN.Lower;
      if (!Last)
        continue;
      SR B = SR::of(SE::mkMin(RI.Lower, *Last), RI.Upper);
      Result = Result ? Result->narrow(B) : B;
    }
  }
  return Result;
}

Solver::Bounds Solver::symbolBounds(Value *V) {
  Bounds B = baseBounds(V);
  if (!UseGuardFacts || !Ctx)
    return B;
  auto It = SigmasOf.find(V);
  if (It == SigmasOf.end())
    return B;
  // A sigma node of V whose block dominates the context holds V's value
  // there; its numeric hull (with base bounds only, to avoid recursion)
  // bounds V.
  if (!B)
    return B;
  auto Base = [this](Value *X) { return baseBounds(X); };
  Bounds Before = B;
  for (PHINode *S : It->second) {
    if (!DT.dominates(S->getParent(), Ctx))
      continue;
    if (Reads)
      Reads->push_back(S);
    auto St = State.find(S);
    if (St == State.end() || St->second.isBottom)
      continue;
    if (auto Lo = symboxes::evaluate(St->second.Lower, Base).Lo)
      B->first = std::max(B->first, *Lo);
    if (auto Hi = symboxes::evaluate(St->second.Upper, Base).Hi)
      B->second = std::min(B->second, *Hi);
  }
  // Contradictory facts, such as a parameter that every call passes as 0 inside
  // `if (p != 0)`, mean the block cannot run; use the bounds without facts
  // there.
  if (B->first > B->second)
    return Before;
  return B;
}

Solver::Bounds Solver::baseBounds(Value *V) {
  if (!UseTypeBounds)
    return std::nullopt;
  auto It = SymBounds.find(V);
  if (It != SymBounds.end())
    return It->second;
  Bounds B;
  if (auto *IT = dyn_cast<IntegerType>(V->getType())) {
    B = typeRange(IT->getBitWidth());
    std::optional<ConstantRange> CR;
    if (auto *A = dyn_cast<Argument>(V))
      CR = A->getRange();
    else if (auto *CB = dyn_cast<CallBase>(V))
      CR = CB->getRange();
    if (auto *I = dyn_cast<Instruction>(V))
      if (MDNode *MD = I->getMetadata(LLVMContext::MD_range)) {
        ConstantRange MR = getConstantRangeFromMetadata(*MD);
        CR = CR ? CR->intersectWith(MR) : MR;
      }
    if (CR && !CR->isFullSet() && !CR->isEmptySet()) {
      B->first = std::max(B->first, ginac_glue::toNumeric(CR->getSignedMin()));
      B->second =
          std::min(B->second, ginac_glue::toNumeric(CR->getSignedMax()));
    }
    // A parameter holds one of the values its known call sites pass.
    if (auto *A = dyn_cast<Argument>(V))
      if (Summary && Summary->Sites && A->getParent() == &F)
        if (auto &H = Summary->Hull[A->getArgNo()]) {
          B->first = std::max(B->first, H->first);
          B->second = std::min(B->second, H->second);
        }
  }
  SymBounds[V] = B;
  return B;
}

symboxes::NumInterval Solver::hull(const SR &R, Type *Ty) {
  if (R.isBottom)
    return {};
  auto Fn = [this](Value *V) { return symbolBounds(V); };
  symboxes::NumInterval H{symboxes::evaluate(R.Lower, Fn).Lo,
                          symboxes::evaluate(R.Upper, Fn).Hi};
  if (UseTypeBounds)
    if (auto *IT = dyn_cast<IntegerType>(Ty)) {
      auto [TLo, THi] = typeRange(IT->getBitWidth());
      H.Lo = H.Lo ? std::max(*H.Lo, TLo) : TLo;
      H.Hi = H.Hi ? std::min(*H.Hi, THi) : THi;
      // A range entirely outside the type can only describe a value that
      // overflowed (poison); say nothing numeric about it.
      if (*H.Lo > *H.Hi) {
        H.Lo = TLo;
        H.Hi = THi;
      }
    }
  return H;
}

SR Solver::clampToType(const SR &R, Type *Ty) {
  if (R.isBottom)
    return R;
  auto [TLo, THi] = typeRange(Ty->getIntegerBitWidth());
  return SR::of(R.Lower.kind() == SE::NegInf ? numE(TLo) : R.Lower,
                R.Upper.kind() == SE::PosInf ? numE(THi) : R.Upper);
}

bool Solver::fitsType(const SR &R, Type *Ty) {
  if (R.isBottom)
    return true;
  auto *IT = dyn_cast<IntegerType>(Ty);
  if (!IT)
    return false;
  auto Fn = [this](Value *V) { return symbolBounds(V); };
  auto Lo = symboxes::evaluate(R.Lower, Fn).Lo;
  auto Hi = symboxes::evaluate(R.Upper, Fn).Hi;
  auto [TLo, THi] = typeRange(IT->getBitWidth());
  return Lo && Hi && *Lo >= TLo && *Hi <= THi;
}

bool Solver::nonNeg(const SR &R, Type *Ty) {
  auto H = hull(R, Ty);
  return H.Lo && !H.Lo->is_negative();
}

bool Solver::negative(const SR &R, Type *Ty) {
  auto H = hull(R, Ty);
  return H.Hi && H.Hi->is_negative();
}

std::optional<APInt> Solver::constOf(const SR &R) {
  if (R.isBottom || !R.Lower.isConst() || R.Lower != R.Upper)
    return std::nullopt;
  return R.Lower.constVal();
}

/// Returns the symbolic range of \p V. Constants fold to singletons;
/// arguments are symbols; instructions not visited yet are bottom.
SR Solver::getState(Value *V) {
  if (auto *C = dyn_cast<ConstantInt>(V)) {
    if (C->getBitWidth() > SE::Width)
      return SR::full();
    return SR::single(SE::num(C->getValue()));
  }
  if (Reads && isa<Instruction>(V))
    Reads->push_back(V);
  auto It = State.find(V);
  if (It != State.end())
    return It->second;
  if (isa<Argument>(V))
    return SR::single(SE::sym(V));
  if (isa<UndefValue>(V))
    return SR::full();
  if (isa<Constant>(V))
    return V->getType()->isIntegerTy() ? SR::single(SE::sym(V)) : SR::full();
  return SR::bottom();
}

SR Solver::binaryOp(BinaryOperator &I, const SR &L, const SR &R) {
  return binaryOp(I.getOpcode(), I.getType(), L, R);
}

SR Solver::binaryOp(unsigned Opc, Type *Ty, const SR &L, const SR &R) {
  if (L.isBottom || R.isBottom)
    return SR::bottom();
  unsigned N = Ty->getIntegerBitWidth();
  std::optional<APInt> RC = constOf(R);
  std::optional<APInt> LC = constOf(L);
  SE Zero = SE::num(0);

  switch (Opc) {
  case Instruction::Add:
    return SR::of(SE::add(L.Lower, R.Lower), SE::add(L.Upper, R.Upper));
  case Instruction::Sub:
    return SR::of(SE::sub(L.Lower, R.Upper), SE::sub(L.Upper, R.Lower));
  case Instruction::Mul: {
    // Multiplying by a constant is monotone: scale both bounds.
    if (RC || LC) {
      const SR &X = RC ? L : R;
      const APInt &C = RC ? *RC : *LC;
      SE K = SE::num(C);
      if (C.isNonNegative())
        return SR::of(SE::mul(X.Lower, K), SE::mul(X.Upper, K));
      return SR::of(SE::mul(X.Upper, K), SE::mul(X.Lower, K));
    }
    SE LL = SE::mul(L.Lower, R.Lower), LU = SE::mul(L.Lower, R.Upper),
       UL = SE::mul(L.Upper, R.Lower), UU = SE::mul(L.Upper, R.Upper);
    return SR::of(SE::mkMin(SE::mkMin(LL, LU), SE::mkMin(UL, UU)),
                  SE::mkMax(SE::mkMax(LL, LU), SE::mkMax(UL, UU)));
  }

  case Instruction::SDiv: {
    if (RC && !RC->isZero()) {
      SE C = SE::num(*RC);
      if (RC->isStrictlyPositive())
        return SR::of(SE::div(L.Lower, C), SE::div(L.Upper, C));
      return SR::of(SE::div(L.Upper, C), SE::div(L.Lower, C));
    }
    // |a / b| <= |a| for any non-zero b.
    auto H = hull(L, Ty);
    if (H.Lo && H.Hi) {
      numeric M = std::max(abs(*H.Lo), abs(*H.Hi));
      return SR::of(numE(-M), numE(M));
    }
    return SR::full();
  }
  case Instruction::UDiv: {
    if (RC && RC->isOne())
      return L;
    if (RC && RC->isNegative()) // unsigned divisor >= 2^(N-1): quotient 0/1
      return SR::of(Zero, SE::num(1));
    if (RC && RC->sgt(1)) {
      SE C = SE::num(*RC);
      if (nonNeg(L, Ty))
        return SR::of(SE::div(L.Lower, C), SE::div(L.Upper, C));
      return SR::of(Zero, numE(iquo(pow2(N) - 1, ginac_glue::toNumeric(*RC))));
    }
    if (nonNeg(L, Ty) && nonNeg(R, Ty))
      return SR::of(Zero, L.Upper);
    return SR::full();
  }

  case Instruction::SRem: {
    if (RC && !RC->isZero()) {
      SE M = SE::num(RC->abs() - 1);
      if (nonNeg(L, Ty))
        return SR::of(Zero, SE::mkMin(L.Upper, M));
      return SR::of(SE::neg(M), M);
    }
    if (nonNeg(L, Ty))
      return SR::of(Zero, L.Upper);
    return SR::full();
  }
  case Instruction::URem: {
    if (RC && RC->isStrictlyPositive()) {
      SE M = SE::num(*RC - 1);
      if (nonNeg(L, Ty))
        return SR::of(Zero, SE::mkMin(L.Upper, M));
      return SR::of(Zero, M);
    }
    if (nonNeg(L, Ty) && nonNeg(R, Ty))
      return SR::of(Zero, SE::mkMin(L.Upper, SE::sub(R.Upper, SE::num(1))));
    return SR::full();
  }

  case Instruction::Shl: {
    if (RC && RC->isNonNegative() && RC->ult(N)) {
      SE Scale = numE(pow2(RC->getZExtValue()));
      return SR::of(SE::mul(L.Lower, Scale), SE::mul(L.Upper, Scale));
    }
    return SR::full();
  }
  case Instruction::LShr: {
    if (RC && RC->isNonNegative() && RC->ult(N)) {
      unsigned C = RC->getZExtValue();
      if (C == 0)
        return L;
      SE Scale = numE(pow2(C));
      if (nonNeg(L, Ty))
        return SR::of(SE::div(L.Lower, Scale), SE::div(L.Upper, Scale));
      return SR::of(Zero, numE(pow2(N - C) - 1));
    }
    if (nonNeg(L, Ty))
      return SR::of(Zero, L.Upper);
    return SR::full();
  }
  case Instruction::AShr: {
    if (RC && RC->isNonNegative() && RC->ult(N)) {
      SE Scale = numE(pow2(RC->getZExtValue()));
      if (nonNeg(L, Ty))
        return SR::of(SE::div(L.Lower, Scale), SE::div(L.Upper, Scale));
      // ashr is floor division; truncation rounds negative values up by at
      // most one.
      return SR::of(SE::sub(SE::div(L.Lower, Scale), SE::num(1)),
                    SE::div(L.Upper, Scale));
    }
    // Shifting right moves a value toward 0 (or -1 if negative).
    return SR::of(SE::mkMin(L.Lower, Zero), SE::mkMax(L.Upper, Zero));
  }

  case Instruction::And: {
    if (LC && RC)
      return SR::single(SE::num(*LC & *RC));
    bool LN = nonNeg(L, Ty), RN = nonNeg(R, Ty);
    if (LN && RN)
      return SR::of(Zero, SE::mkMin(L.Upper, R.Upper));
    if (LN)
      return SR::of(Zero, L.Upper);
    if (RN)
      return SR::of(Zero, R.Upper);
    if (negative(L, Ty) && negative(R, Ty))
      return SR::of(SE::negInf(), SE::mkMin(L.Upper, R.Upper));
    return SR::full();
  }
  case Instruction::Or:
  case Instruction::Xor: {
    bool IsOr = Opc == Instruction::Or;
    if (LC && RC)
      return SR::single(SE::num(IsOr ? (*LC | *RC) : (*LC ^ *RC)));
    if (nonNeg(L, Ty) && nonNeg(R, Ty)) {
      // Both fit in b bits, where b covers the larger upper bound.
      auto HL = hull(L, Ty), HR = hull(R, Ty);
      if (HL.Hi && HR.Hi) {
        numeric Max = std::max(*HL.Hi, *HR.Hi);
        unsigned B = 0;
        while (pow2(B) <= Max)
          ++B;
        SE Ones = numE(pow2(B) - 1);
        // x | y >= max(x, y) for non-negative x and y.
        return IsOr ? SR::of(SE::mkMax(L.Lower, R.Lower), Ones)
                    : SR::of(Zero, Ones);
      }
    }
    if (IsOr) {
      // Or-ing a negative value keeps it negative and does not decrease it.
      bool LNeg = negative(L, Ty), RNeg = negative(R, Ty);
      if (LNeg && RNeg)
        return SR::of(SE::mkMax(L.Lower, R.Lower), SE::num(-1));
      if (LNeg)
        return SR::of(L.Lower, SE::num(-1));
      if (RNeg)
        return SR::of(R.Lower, SE::num(-1));
    }
    return SR::full();
  }

  default:
    return SR::full();
  }
}

SR Solver::castOp(CastInst &I, const SR &R) {
  Type *SrcTy = I.getSrcTy();
  if (!SrcTy->isIntegerTy())
    return SR::single(SE::sym(&I)); // ptrtoint, fptosi, ...: a new symbol
  if (R.isBottom)
    return SR::bottom();
  unsigned NS = SrcTy->getIntegerBitWidth();
  unsigned ND = I.getDestTy()->getIntegerBitWidth();

  switch (I.getOpcode()) {
  case Instruction::SExt:
    return clampToType(R, SrcTy);
  case Instruction::ZExt: {
    if (nonNeg(R, SrcTy))
      return clampToType(R, SrcTy);
    if (I.hasNonNeg()) // the operand is non-negative, or the result poison
      return clampToType(SR::of(SE::mkMax(R.Lower, SE::num(0)), R.Upper),
                         SrcTy);
    SE Wrap = numE(pow2(NS));
    if (negative(R, SrcTy))
      return SR::of(SE::add(R.Lower, Wrap), SE::add(R.Upper, Wrap));
    return SR::of(SE::num(0), numE(pow2(NS) - 1));
  }
  case Instruction::Trunc: {
    auto H = hull(R, SrcTy);
    auto [TLo, THi] = typeRange(ND);
    if (H.Lo && H.Hi && *H.Lo >= TLo && *H.Hi <= THi)
      return R;
    return SR::full();
  }
  default:
    return NS == ND ? R : SR::full();
  }
}

SR Solver::intrinsicOp(IntrinsicInst &II) {
  unsigned N = II.getType()->getIntegerBitWidth();
  auto Arg = [&](unsigned K) { return getState(II.getArgOperand(K)); };
  switch (II.getIntrinsicID()) {
  case Intrinsic::smin:
  case Intrinsic::smax:
  case Intrinsic::umin:
  case Intrinsic::umax: {
    SR A = Arg(0), B = Arg(1);
    if (A.isBottom || B.isBottom)
      return SR::bottom();
    Intrinsic::ID ID = II.getIntrinsicID();
    bool Unsigned = ID == Intrinsic::umin || ID == Intrinsic::umax;
    if (Unsigned && !(nonNeg(A, II.getType()) && nonNeg(B, II.getType())))
      return SR::single(SE::sym(&II));
    if (ID == Intrinsic::smin || ID == Intrinsic::umin)
      return SR::of(SE::mkMin(A.Lower, B.Lower), SE::mkMin(A.Upper, B.Upper));
    return SR::of(SE::mkMax(A.Lower, B.Lower), SE::mkMax(A.Upper, B.Upper));
  }
  case Intrinsic::abs: {
    SR A = Arg(0);
    if (A.isBottom)
      return SR::bottom();
    if (nonNeg(A, II.getType()))
      return A;
    auto H = hull(A, II.getType());
    if (H.Hi && !H.Hi->is_positive())
      return SR::of(SE::neg(A.Upper), SE::neg(A.Lower));
    return SR::of(SE::num(0), SE::mkMax(SE::neg(A.Lower), A.Upper));
  }
  case Intrinsic::ctpop:
  case Intrinsic::ctlz:
  case Intrinsic::cttz:
    return SR::of(SE::num(0), SE::num(N));
  default:
    return SR::single(SE::sym(&II));
  }
}

std::optional<SR> Solver::onEdge(Value *V, unsigned Depth) {
  if (!SigmaBlock)
    return std::nullopt;
  BasicBlock *Pred = SigmaBlock->getSinglePredecessor();
  auto *Br = Pred ? dyn_cast<BranchInst>(Pred->getTerminator()) : nullptr;
  if (!Br || !Br->isConditional())
    return std::nullopt;
  SR R = getState(V);
  if (R.isBottom)
    return std::nullopt;
  bool Touched = false;
  SmallVector<std::pair<ICmpInst *, bool>, 4> Cmps;
  impliedComparisons(Br->getCondition(), Br->getSuccessor(0) == SigmaBlock,
                     Cmps);
  SR Base = R;
  for (auto [Cmp, Side] : Cmps) {
    Value *Other = Cmp->getOperand(0) == V   ? Cmp->getOperand(1)
                   : Cmp->getOperand(1) == V ? Cmp->getOperand(0)
                                             : nullptr;
    if (!Other)
      continue;
    SR OtherR = Depth ? onEdge(Other, Depth - 1).value_or(getState(Other))
                      : getState(Other);
    SR C = constrain(Base, Cmp, V, Side, OtherR);
    if (!C.isBottom) {
      R = SR::of(SE::mkMax(R.Lower, C.Lower), SE::mkMin(R.Upper, C.Upper));
      Touched = true;
    }
  }
  // A compared value computed from operands the branch also tests.
  if (Depth)
    if (auto *Bin = dyn_cast<BinaryOperator>(V)) {
      std::optional<SR> SA = onEdge(Bin->getOperand(0), Depth - 1),
                        SB = onEdge(Bin->getOperand(1), Depth - 1);
      if (SA || SB) {
        SR C = binaryOp(*Bin, SA ? *SA : getState(Bin->getOperand(0)),
                        SB ? *SB : getState(Bin->getOperand(1)));
        if (!C.isBottom &&
            (Bin->hasNoSignedWrap() || fitsType(C, Bin->getType()))) {
          R = SR::of(SE::mkMax(R.Lower, C.Lower), SE::mkMin(R.Upper, C.Upper));
          Touched = true;
        }
      }
    }
  if (!Touched)
    return std::nullopt;
  return R;
}

SR Solver::applyConstraint(SR R, ICmpInst *Cmp, Value *SigmaVar,
                           bool IsTrueSide) {
  // The other operand, as refined on this edge by the tests of the branch
  // (j < i + 10 && i < 1000000: i + 10 does not wrap there).
  Value *Other = Cmp->getOperand(0) == SigmaVar ? Cmp->getOperand(1)
                                                : Cmp->getOperand(0);
  return constrain(R, Cmp, SigmaVar, IsTrueSide,
                   onEdge(Other, EdgeDepth).value_or(getState(Other)));
}

SR Solver::constrain(SR R, ICmpInst *Cmp, Value *SigmaVar, bool IsTrueSide,
                     const SR &OtherR) {
  Value *A = Cmp->getOperand(0);
  Value *B = Cmp->getOperand(1);
  bool IsA = (A == SigmaVar);
  SR Ra = IsA ? getState(A) : OtherR;
  SR Rb = !IsA ? getState(B) : OtherR;
  if (Ra.isBottom || Rb.isBottom)
    return R;

  CmpInst::Predicate Pred = Cmp->getPredicate();
  if (ICmpInst::isUnsigned(Pred)) {
    Type *Ty = A->getType();
    if (!Ty->isIntegerTy())
      return R;
    bool NA = nonNeg(Ra, Ty), NB = nonNeg(Rb, Ty);
    if (!(NA && NB)) {
      // On this edge X <u Y (or X <=u Y). If Y is non-negative, X's unsigned
      // value is below the signed maximum, so X is a non-negative signed
      // value below Y: X in [0, Y - 1], whatever X's sign was (e.g. an
      // unsigned i < 1000000 gives i in [0, 999999]).
      CmpInst::Predicate P =
          IsTrueSide ? Pred : CmpInst::getInversePredicate(Pred);
      Value *X = A;
      SR RY = Rb;
      bool YNonNeg = NB;
      if (P == ICmpInst::ICMP_UGT || P == ICmpInst::ICMP_UGE) {
        X = B;
        RY = Ra;
        YNonNeg = NA;
        P = CmpInst::getSwappedPredicate(P);
      }
      if ((P == ICmpInst::ICMP_ULT || P == ICmpInst::ICMP_ULE) &&
          SigmaVar == X && YNonNeg && A != B) {
        SE Hi = P == ICmpInst::ICMP_ULT ? SE::sub(RY.Upper, SE::num(1))
                                        : RY.Upper;
        return SR::of(SE::mkMax(R.Lower, SE::num(0)), SE::mkMin(R.Upper, Hi));
      }
      return R;
    }
    // An unsigned comparison of non-negative values is a signed one.
    Pred = ICmpInst::getSignedPredicate(Pred);
  }

  switch (Pred) {
  case ICmpInst::ICMP_EQ:
    if (IsTrueSide)
      return SR::of(SE::mkMax(Ra.Lower, Rb.Lower),
                    SE::mkMin(Ra.Upper, Rb.Upper));
    return R;

  case ICmpInst::ICMP_NE:
    if (!IsTrueSide)
      return SR::of(SE::mkMax(Ra.Lower, Rb.Lower),
                    SE::mkMin(Ra.Upper, Rb.Upper));
    return R;

  case ICmpInst::ICMP_SGE:
    IsTrueSide = !IsTrueSide;
    [[fallthrough]];
  case ICmpInst::ICMP_SLT:
    if (IsTrueSide)
      return IsA ? SR::of(Ra.Lower,
                          SE::mkMin(SE::sub(Rb.Upper, SE::num(1)), Ra.Upper))
                 : SR::of(SE::mkMax(SE::add(Ra.Lower, SE::num(1)), Rb.Lower),
                          Rb.Upper);
    return IsA ? SR::of(SE::mkMax(Ra.Lower, Rb.Lower), Ra.Upper)
               : SR::of(Rb.Lower, SE::mkMin(Ra.Upper, Rb.Upper));

  case ICmpInst::ICMP_SLE:
    IsTrueSide = !IsTrueSide;
    [[fallthrough]];
  case ICmpInst::ICMP_SGT:
    if (IsTrueSide)
      return IsA ? SR::of(SE::mkMax(Ra.Lower, SE::add(Rb.Lower, SE::num(1))),
                          Ra.Upper)
                 : SR::of(Rb.Lower,
                          SE::mkMin(SE::sub(Ra.Upper, SE::num(1)), Rb.Upper));
    return IsA ? SR::of(Ra.Lower, SE::mkMin(Ra.Upper, Rb.Upper))
               : SR::of(SE::mkMax(Rb.Lower, Ra.Lower), Rb.Upper);
  default:
    return R;
  }
}

void Solver::impliedComparisons(
    Value *Cond, bool Side, SmallVectorImpl<std::pair<ICmpInst *, bool>> &Out,
    unsigned Depth) {
  using namespace PatternMatch;
  Value *A, *B;
  if (auto *Cmp = dyn_cast<ICmpInst>(Cond)) {
    Out.push_back({Cmp, Side});
  } else if (Depth >= 4) {
    return;
  } else if (match(Cond, m_LogicalAnd(m_Value(A), m_Value(B)))) {
    if (Side) {
      impliedComparisons(A, true, Out, Depth + 1);
      impliedComparisons(B, true, Out, Depth + 1);
    }
  } else if (match(Cond, m_LogicalOr(m_Value(A), m_Value(B)))) {
    if (!Side) {
      impliedComparisons(A, false, Out, Depth + 1);
      impliedComparisons(B, false, Out, Depth + 1);
    }
  } else if (match(Cond, m_Not(m_Value(A)))) {
    impliedComparisons(A, !Side, Out, Depth + 1);
  }
}

/// Returns the arithmetic opcode of llvm.s{add,sub,mul}.with.overflow, which
/// -fsanitize=signed-integer-overflow emits for +, - and *.
std::optional<unsigned> Solver::overflowOpcode(Value *V) {
  auto *II = dyn_cast<IntrinsicInst>(V);
  if (!II)
    return std::nullopt;
  switch (II->getIntrinsicID()) {
  case Intrinsic::sadd_with_overflow:
    return Instruction::Add;
  case Intrinsic::ssub_with_overflow:
    return Instruction::Sub;
  case Intrinsic::smul_with_overflow:
    return Instruction::Mul;
  default:
    return std::nullopt;
  }
}

/// Computes the transfer function of \p I over the symbolic interval domain.
SR Solver::transfer(Instruction &I) {
  if (!I.getType()->isIntegerTy())
    return SR::full();

  // The result of a checked operation: where it is used, the check passed
  // (the overflow path traps), so it is the mathematical result, as for an
  // operation with nsw.
  if (auto *EV = dyn_cast<ExtractValueInst>(&I))
    if (EV->getNumIndices() == 1 && EV->getIndices()[0] == 0)
      if (auto Opc = overflowOpcode(EV->getAggregateOperand())) {
        auto *II = cast<IntrinsicInst>(EV->getAggregateOperand());
        return binaryOp(*Opc, I.getType(), getState(II->getArgOperand(0)),
                        getState(II->getArgOperand(1)));
      }

  if (auto *Phi = dyn_cast<PHINode>(&I)) {
    if (MDNode *MD = Phi->getMetadata("sigma")) {
      // Sigma nodes are where facts come from: they are computed without
      // facts, so that simplifying with a fact cannot erase the fact itself.
      BasicBlock *Saved = Ctx;
      setContext(nullptr);
      auto Restore = make_scope_exit([&] { setContext(Saved); });
      bool IsTrueSide = cast<MDString>(MD->getOperand(0))->getString() == ".t";
      Value *Incoming = Phi->getIncomingValue(0);
      BasicBlock *PredBB = Phi->getIncomingBlock(0);
      SR R = getState(Incoming);
      SigmaBlock = Phi->getParent();
      auto ResetSigma = make_scope_exit([&] { SigmaBlock = nullptr; });
      // A value computed from operands that the branch also tests is evaluated
      // again from their ranges on this edge (the splitting of dependences of
      // OOPSLA'14, Section 4.1). An operation without nsw counts only if it
      // cannot wrap on the edge.
      if (auto *Bin = dyn_cast<BinaryOperator>(Incoming)) {
        std::optional<SR> SA = onEdge(Bin->getOperand(0), EdgeDepth),
                          SB = onEdge(Bin->getOperand(1), EdgeDepth);
        if (SA || SB) {
          SR C = binaryOp(*Bin, SA ? *SA : getState(Bin->getOperand(0)),
                          SB ? *SB : getState(Bin->getOperand(1)));
          if (!C.isBottom && !R.isBottom &&
              (Bin->hasNoSignedWrap() || fitsType(C, Bin->getType())))
            R = SR::of(SE::mkMax(R.Lower, C.Lower), SE::mkMin(R.Upper, C.Upper));
        }
      }
      auto *Br = dyn_cast<BranchInst>(PredBB->getTerminator());
      if (!Br || !Br->isConditional() || R.isBottom)
        return R;
      SmallVector<std::pair<ICmpInst *, bool>, 4> Cmps;
      impliedComparisons(Br->getCondition(), IsTrueSide, Cmps);
      // Each test gives a sound range for the value on this edge; with
      // several (`i < n && i < 100`) the value lies in all of them.
      SR Result = R;
      bool First = true;
      for (auto [Cmp, Side] : Cmps) {
        if (Cmp->getOperand(0) != Incoming && Cmp->getOperand(1) != Incoming)
          continue;
        SR C = applyConstraint(R, Cmp, Incoming, Side);
        if (First) {
          Result = C;
          First = false;
        } else if (!C.isBottom && !Result.isBottom) {
          Result = SR::of(SE::mkMax(Result.Lower, C.Lower),
                          SE::mkMin(Result.Upper, C.Upper));
        }
      }
      // Inside the body of a loop whose counter steps by s > 1, the counter is
      // at most its largest value that passes the loop test.
      if (auto *Root = dyn_cast<PHINode>(throughSigmas(Incoming)))
        if (Loop *RL = LI.getLoopFor(Root->getParent());
            RL && RL->getHeader() == Root->getParent() &&
            Phi->getParent() != Root->getParent() &&
            RL->contains(Phi->getParent()) && !Result.isBottom)
          if (auto M = strideBodyMax(Root))
            Result = SR::of(Result.Lower, SE::mkMin(Result.Upper, *M));
      return Result;
    }
    SR R = SR::bottom();
    for (Value *Op : Phi->incoming_values())
      R = R.join(getState(Op));
    return resolveAtHeader(Phi, R);
  }

  if (isa<LoadInst>(I))
    return SR::single(SE::sym(&I));
  if (auto *II = dyn_cast<IntrinsicInst>(&I))
    return intrinsicOp(*II);
  if (isa<CallBase>(I))
    return SR::single(SE::sym(&I));
  if (isa<CmpInst>(I)) // i1: true is -1 in the signed interpretation
    return SR::of(SE::num(-1), SE::num(0));
  if (auto *Sel = dyn_cast<SelectInst>(&I))
    return getState(Sel->getTrueValue()).join(getState(Sel->getFalseValue()));
  if (auto *Bin = dyn_cast<BinaryOperator>(&I)) {
    SR A = getState(Bin->getOperand(0)), B = getState(Bin->getOperand(1));
    SR R = binaryOp(*Bin, A, B);
    // A sigma node of a kernel value (parameter, load, call) is that value:
    // read it also as its own symbol. Each reading gives a sound range, so
    // their intersection is one too, and bounds can cancel: with j in
    // [i, i + 9], j - i is [i - i, i + 9 - i] = [0, 9], which the range of
    // the sigma of i ([i, j]) alone cannot give.
    unsigned Opc = Bin->getOpcode();
    if (UseExactSymbols && !R.isBottom &&
        (Opc == Instruction::Add || Opc == Instruction::Sub ||
         Opc == Instruction::Mul)) {
      auto Exact = [](Value *V) -> std::optional<SR> {
        Value *Root = throughSigmas(V);
        if (Root == V && !isa<PHINode>(V))
          return std::nullopt; // no sigma: its range is already [v, v]
        if ((isa<Argument>(Root) || isa<LoadInst>(Root) ||
             (isa<CallBase>(Root) && !isa<IntrinsicInst>(Root))) &&
            Root->getType() == V->getType())
          return SR::single(SE::sym(Root));
        return std::nullopt;
      };
      std::optional<SR> XA = Exact(Bin->getOperand(0)),
                        XB = Exact(Bin->getOperand(1));
      auto Meet = [&](const SR &C) {
        if (!C.isBottom)
          R = SR::of(SE::mkMax(R.Lower, C.Lower), SE::mkMin(R.Upper, C.Upper));
      };
      if (XA)
        Meet(binaryOp(*Bin, *XA, B));
      if (XB)
        Meet(binaryOp(*Bin, A, *XB));
      if (XA && XB)
        Meet(binaryOp(*Bin, *XA, *XB));
    }
    // As in OOPSLA'14, the analysis computes over mathematical integers. This
    // is sound when signed overflow is poison (nsw); operations that may wrap
    // are found after each solve (see run()).
    if (Wrapping.count(Bin))
      return SR::full();
    return R;
  }
  if (auto *Cast = dyn_cast<CastInst>(&I))
    return castOp(*Cast, getState(Cast->getOperand(0)));
  if (isa<FreezeInst>(I))
    return getState(I.getOperand(0));
  // Anything else is a new symbol of the kernel.
  return SR::single(SE::sym(&I));
}

void Solver::run() {
  // Solve assuming no arithmetic wraps; then any operation without nsw whose
  // range does not fit its type may wrap: give it the full range and solve
  // again. Operations are only ever added, so this terminates; after a few
  // rounds every remaining candidate is given up at once.
  for (unsigned Attempt = 0;; ++Attempt) {
    solve();
    SmallVector<Instruction *, 8> New;
    for (Instruction &I : instructions(F))
      if (auto *Bin = dyn_cast<OverflowingBinaryOperator>(&I))
        if (!Bin->hasNoSignedWrap() && !Wrapping.count(&I)) {
          auto It = State.find(&I);
          if (It != State.end() && !fitsType(It->second, I.getType()))
            New.push_back(&I);
        }
    if (New.empty())
      return;
    if (Attempt >= 3) {
      for (Instruction &I : instructions(F))
        if (auto *Bin = dyn_cast<OverflowingBinaryOperator>(&I))
          if (!Bin->hasNoSignedWrap())
            Wrapping.insert(&I);
    } else {
      Wrapping.insert(New.begin(), New.end());
    }
  }
}

std::optional<bool> Solver::decideCmp(ICmpInst &Cmp) {
  Type *Ty = Cmp.getOperand(0)->getType();
  if (!Ty->isIntegerTy() || Ty->getIntegerBitWidth() < 2)
    return std::nullopt;
  SR A = getState(Cmp.getOperand(0)), B = getState(Cmp.getOperand(1));
  if (A.isBottom || B.isBottom)
    return std::nullopt;
  CmpInst::Predicate Pred = Cmp.getPredicate();
  // Ranges are signed: an unsigned comparison of non-negative values is the
  // signed one.
  if (ICmpInst::isUnsigned(Pred)) {
    if (!nonNeg(A, Ty) || !nonNeg(B, Ty))
      return std::nullopt;
    Pred = ICmpInst::getSignedPredicate(Pred);
  }
  // A value of the symbolic kernel (seen through sigma nodes) is also
  // exactly its own symbol: with is in [0, Ns - 1], is < Ns holds although
  // the range of Ns has a numeric lower bound.
  auto Exact = [](Value *V) -> std::optional<SE> {
    V = throughSigmas(V);
    if (isa<Argument>(V) || isa<LoadInst>(V) || isa<CallBase>(V))
      return SE::sym(V);
    return std::nullopt;
  };
  SmallVector<SE, 2> AUp = {A.Upper}, ALo = {A.Lower}, BUp = {B.Upper},
                     BLo = {B.Lower};
  if (auto X = Exact(Cmp.getOperand(0))) {
    AUp.push_back(*X);
    ALo.push_back(*X);
  }
  if (auto X = Exact(Cmp.getOperand(1))) {
    BUp.push_back(*X);
    BLo.push_back(*X);
  }
  auto Below = [](ArrayRef<SE> XUp, ArrayRef<SE> YLo, int64_t D) {
    for (const SE &U : XUp)
      for (const SE &L : YLo)
        if (SE::provablyLE(SE::add(U, SE::num(D)), L))
          return true;
    return false;
  };
  auto Lt = [&](bool AB) {
    return AB ? Below(AUp, BLo, 1) : Below(BUp, ALo, 1);
  };
  auto Le = [&](bool AB) {
    return AB ? Below(AUp, BLo, 0) : Below(BUp, ALo, 0);
  };
  auto Decide = [](bool T, bool F) -> std::optional<bool> {
    if (T)
      return true;
    if (F)
      return false;
    return std::nullopt;
  };
  switch (Pred) {
  case ICmpInst::ICMP_SLT:
    return Decide(Lt(true), Le(false));
  case ICmpInst::ICMP_SLE:
    return Decide(Le(true), Lt(false));
  case ICmpInst::ICMP_SGT:
    return Decide(Lt(false), Le(true));
  case ICmpInst::ICMP_SGE:
    return Decide(Le(false), Lt(true));
  case ICmpInst::ICMP_EQ:
  case ICmpInst::ICMP_NE: {
    bool Disjoint = Lt(true) || Lt(false);
    bool Same = A.Lower == A.Upper && B.Lower == B.Upper && A.Lower == B.Lower &&
                !A.Lower.isInf();
    bool IsEq = Pred == ICmpInst::ICMP_EQ;
    return Decide(IsEq ? Same : Disjoint, IsEq ? Disjoint : Same);
  }
  default:
    return std::nullopt;
  }
}

void Solver::annotateNoWrap(Instruction &I) {
  auto *Op = dyn_cast<OverflowingBinaryOperator>(&I);
  if (!Op || !I.getType()->isIntegerTy() || Wrapping.count(&I))
    return;
  unsigned Opc = I.getOpcode();
  if (Opc != Instruction::Add && Opc != Instruction::Sub &&
      Opc != Instruction::Mul)
    return;
  auto It = State.find(&I);
  if (It == State.end() || It->second.isBottom)
    return;
  Type *Ty = I.getType();
  // The range is that of the mathematical result: if it fits the type, the
  // operation does not wrap (signed).
  bool NSW = Op->hasNoSignedWrap() || fitsType(It->second, Ty);
  if (!NSW)
    return;
  SR A = getState(I.getOperand(0)), B = getState(I.getOperand(1));
  // Non-negative operands and no signed wrap: add and mul do not wrap
  // unsigned either; sub neither if the result is non-negative.
  bool NUW = !Op->hasNoUnsignedWrap() && nonNeg(A, Ty) && nonNeg(B, Ty) &&
             (Opc != Instruction::Sub || nonNeg(It->second, Ty));
  LLVMContext &Ctx = I.getContext();
  if (!Op->hasNoSignedWrap())
    I.setMetadata("srange.nsw", MDNode::get(Ctx, {}));
  if (NUW)
    I.setMetadata("srange.nuw", MDNode::get(Ctx, {}));
}

/// Returns the range of byte offsets of \p Ptr from its base pointer, stored in
/// \p Base, through inbounds GEPs. Symbols that may differ between iterations
/// of a loop are replaced by their numeric bounds, so the range holds for every
/// execution within one call of the function.
std::optional<SR> Solver::offsetRange(Value *Ptr, Value *&Base) {
  const DataLayout &DL = F.getDataLayout();
  SE Lo = SE::num(0), Hi = SE::num(0);
  while (auto *GEP = dyn_cast<GEPOperator>(Ptr)) {
    if (!GEP->isInBounds())
      return std::nullopt;
    for (auto GTI = gep_type_begin(GEP), E = gep_type_end(GEP); GTI != E;
         ++GTI) {
      Value *Idx = GTI.getOperand();
      if (StructType *ST = GTI.getStructTypeOrNull()) {
        auto Off = SE::num(static_cast<int64_t>(
            DL.getStructLayout(ST)->getElementOffset(
                cast<ConstantInt>(Idx)->getZExtValue())));
        Lo = SE::add(Lo, Off);
        Hi = SE::add(Hi, Off);
        continue;
      }
      TypeSize Stride = GTI.getSequentialElementStride(DL);
      if (Stride.isScalable() || !Idx->getType()->isIntegerTy() ||
          Idx->getType()->getIntegerBitWidth() > 64)
        return std::nullopt;
      SR R = getState(Idx);
      if (R.isBottom)
        return std::nullopt;
      SE Sc = SE::num(static_cast<int64_t>(Stride.getFixedValue()));
      Lo = SE::add(Lo, SE::mul(R.Lower, Sc));
      Hi = SE::add(Hi, SE::mul(R.Upper, Sc));
    }
    Ptr = GEP->getPointerOperand();
  }
  Base = Ptr;
  auto InLoop = [this](Value *V) {
    auto *I = dyn_cast<Instruction>(V);
    return I && LI.getLoopFor(I->getParent());
  };
  if (InLoop(Base))
    return std::nullopt;
  auto Num = [this](Value *V) { return baseBounds(V); };
  return SR::of(SE::resolve(Lo, /*Upper=*/false, InLoop, Num),
                SE::resolve(Hi, /*Upper=*/true, InLoop, Num));
}

/// Returns a lower bound of the size in bytes of the object \p Base points to,
/// valid within one call, or std::nullopt if unknown.
std::optional<SE> Solver::objectSize(Value *Base) {
  const DataLayout &DL = F.getDataLayout();
  // A lower bound of a size operand. It may be negative as a signed value
  // (a huge unsigned size): a proof offset + size <= bound then needs
  // bound > 0, where signed and unsigned agree. Products need both factors
  // non-negative (NonNeg).
  auto LowerOf = [this](Value *V, bool NonNeg = false) -> std::optional<SE> {
    if (auto *C = dyn_cast<ConstantInt>(V))
      return C->getBitWidth() <= 64 ? std::optional<SE>(SE::num(C->getValue()))
                                    : std::nullopt;
    SR R = getState(V);
    if (R.isBottom || (NonNeg && !SE::provablyLE(SE::num(0), R.Lower)))
      return std::nullopt;
    return R.Lower;
  };
  std::optional<SE> Size;
  if (auto *AI = dyn_cast<AllocaInst>(Base)) {
    auto ES = DL.getTypeAllocSize(AI->getAllocatedType());
    if (ES.isScalable())
      return std::nullopt;
    auto N = LowerOf(AI->getArraySize(), /*NonNeg=*/true);
    if (!N)
      return std::nullopt;
    Size = SE::mul(*N, SE::num(static_cast<int64_t>(ES.getFixedValue())));
  } else if (auto *GV = dyn_cast<GlobalVariable>(Base)) {
    if (GV->isDeclaration() || GV->isInterposable())
      return std::nullopt;
    auto ES = DL.getTypeAllocSize(GV->getValueType());
    if (ES.isScalable())
      return std::nullopt;
    Size = SE::num(static_cast<int64_t>(ES.getFixedValue()));
  } else if (auto *CB = dyn_cast<CallBase>(Base)) {
    Attribute A = CB->getFnAttr(Attribute::AllocSize);
    if (!A.isValid())
      return std::nullopt;
    auto [ElemArg, NumArg] = A.getAllocSizeArgs();
    auto E = LowerOf(CB->getArgOperand(ElemArg), /*NonNeg=*/NumArg.has_value());
    if (!E)
      return std::nullopt;
    Size = *E;
    if (NumArg) {
      auto N = LowerOf(CB->getArgOperand(*NumArg), /*NonNeg=*/true);
      if (!N)
        return std::nullopt;
      Size = SE::mul(*Size, *N);
    }
  } else {
    return std::nullopt;
  }
  auto InLoop = [this](Value *V) {
    auto *I = dyn_cast<Instruction>(V);
    return I && LI.getLoopFor(I->getParent());
  };
  auto Num = [this](Value *V) { return baseBounds(V); };
  return SE::resolve(*Size, /*Upper=*/false, InLoop, Num);
}

void Solver::annotateInBounds() {
  const DataLayout &DL = F.getDataLayout();
  LLVMContext &Ctx = F.getContext();
  for (Instruction &I : instructions(F)) {
    Value *Ptr;
    Type *Ty;
    if (auto *L = dyn_cast<LoadInst>(&I)) {
      Ptr = L->getPointerOperand();
      Ty = L->getType();
    } else if (auto *St = dyn_cast<StoreInst>(&I)) {
      Ptr = St->getPointerOperand();
      Ty = St->getValueOperand()->getType();
    } else {
      continue;
    }
    if (!I.getMetadata("sra.id"))
      continue;
    TypeSize TS = DL.getTypeStoreSize(Ty);
    if (TS.isScalable())
      continue;
    Value *Base = nullptr;
    auto Off = offsetRange(Ptr, Base);
    if (!Off || Off->isBottom)
      continue;
    auto Size = objectSize(Base);
    if (!Size)
      continue;
    SE End = SE::add(Off->Upper, SE::num(static_cast<int64_t>(TS.getFixedValue())));
    if (SE::provablyLE(SE::num(0), Off->Lower) && SE::provablyLE(End, *Size))
      I.setMetadata("srange.inbounds", MDNode::get(Ctx, {}));
  }
}

void Solver::annotateAlias() {
  struct Access {
    Instruction *I;
    uint64_t Id;
    SR Off;
    SE Size;
    bool Store;
  };
  const DataLayout &DL = F.getDataLayout();
  MapVector<Value *, SmallVector<Access, 8>> Groups;
  for (Instruction &I : instructions(F)) {
    Value *Ptr;
    Type *Ty;
    bool Store = false;
    if (auto *L = dyn_cast<LoadInst>(&I)) {
      if (!L->isSimple())
        continue;
      Ptr = L->getPointerOperand();
      Ty = L->getType();
    } else if (auto *St = dyn_cast<StoreInst>(&I)) {
      if (!St->isSimple())
        continue;
      Ptr = St->getPointerOperand();
      Ty = St->getValueOperand()->getType();
      Store = true;
    } else {
      continue;
    }
    auto *IdMD = I.getMetadata("sra.id");
    TypeSize TS = DL.getTypeStoreSize(Ty);
    if (!IdMD || TS.isScalable())
      continue;
    uint64_t Id =
        mdconst::extract<ConstantInt>(IdMD->getOperand(0))->getZExtValue();
    Value *Base = nullptr;
    ++StatAcc;
    auto Off = offsetRange(Ptr, Base);
    if (!Off) {
      ++(Base ? StatAccLoopBase : StatAccNoOff);
      continue;
    }
    if (Off->isFull()) {
      ++StatAccFull;
      continue;
    }
    auto &G = Groups[Base];
    if (G.size() < AliasMaxGroup)
      G.push_back({&I, Id, *Off,
                   SE::num(static_cast<int64_t>(TS.getFixedValue())), Store});
  }
  LLVMContext &Ctx = F.getContext();
  Type *I64 = Type::getInt64Ty(Ctx);
  DenseMap<Instruction *, SmallVector<Metadata *, 4>> Out;
  for (auto &[Base, G] : Groups)
    for (unsigned A = 0; A < G.size(); ++A)
      for (unsigned B = A + 1; B < G.size(); ++B) {
        Access &X = G[A], &Y = G[B];
        if (!X.Store && !Y.Store)
          continue;
        // Both offsets constant: BasicAA already decides these.
        if (X.Off.Lower.isConst() && X.Off.Upper.isConst() &&
            Y.Off.Lower.isConst() && Y.Off.Upper.isConst())
          continue;
        ++StatCand;
        bool Disjoint =
            SE::provablyLE(SE::add(X.Off.Upper, X.Size), Y.Off.Lower) ||
            SE::provablyLE(SE::add(Y.Off.Upper, Y.Size), X.Off.Lower);
        if (!Disjoint)
          continue;
        ++StatAliasPairs;
        if (!(X.Off.Lower.isConst() && X.Off.Upper.isConst() &&
              Y.Off.Lower.isConst() && Y.Off.Upper.isConst()))
          ++StatAliasSymbolic;
        Out[X.I].push_back(ConstantAsMetadata::get(ConstantInt::get(I64, Y.Id)));
      }
  for (auto &[I, Ids] : Out)
    I->setMetadata("srange.noalias", MDTuple::get(Ctx, Ids));
}

bool Solver::provablyNonNeg(Value *V) {
  SR R = getState(V);
  if (R.isBottom)
    return false;
  return SE::provablyLE(SE::num(0), R.Lower) || nonNeg(R, V->getType());
}

/// Tags \p I with the sign and width facts used by CVP-style rewrites: a sext
/// of a non-negative value (!srange.nneg), signed division and remainder of
/// non-negative operands (!srange.unsigned), signed comparisons of non-negative
/// operands (!srange.samesign), truncations that lose no bits (!srange.trunc =
/// "nuw", "nsw" or "both"), and the unsigned bits a division's operands need
/// (!srange.divbits).
void Solver::annotateSigns(Instruction &I) {
  LLVMContext &Ctx = I.getContext();
  auto Mark = [&](StringRef Kind, std::optional<StringRef> Arg = std::nullopt) {
    I.setMetadata(Kind, Arg ? MDNode::get(Ctx, MDString::get(Ctx, *Arg))
                            : MDNode::get(Ctx, {}));
  };
  if (isa<SExtInst>(I) && provablyNonNeg(I.getOperand(0)))
    Mark("srange.nneg");
  unsigned Opc = I.getOpcode();
  bool Div = Opc == Instruction::SDiv || Opc == Instruction::SRem ||
             Opc == Instruction::UDiv || Opc == Instruction::URem;
  bool BothNonNeg = false;
  if (Div || isa<ICmpInst>(I))
    BothNonNeg = I.getOperand(0)->getType()->isIntegerTy() &&
                 provablyNonNeg(I.getOperand(0)) && provablyNonNeg(I.getOperand(1));
  if ((Opc == Instruction::SDiv || Opc == Instruction::SRem) && BothNonNeg)
    Mark("srange.unsigned");
  if (auto *Cmp = dyn_cast<ICmpInst>(&I))
    if (Cmp->isSigned() && BothNonNeg)
      Mark("srange.samesign");
  if (Div && BothNonNeg) {
    unsigned Bits = 0;
    for (Value *Op : I.operands()) {
      auto H = hull(getState(Op), Op->getType());
      auto Hi = H.Hi ? ginac_glue::toAPInt(*H.Hi, 128) : std::nullopt;
      if (!Hi) {
        Bits = 0;
        break;
      }
      Bits = std::max<unsigned>(Bits, Hi->getActiveBits());
    }
    if (Bits && Bits < I.getType()->getIntegerBitWidth())
      Mark("srange.divbits", std::to_string(Bits));
  }
  if (auto *T = dyn_cast<TruncInst>(&I)) {
    SR R = getState(T->getOperand(0));
    if (!R.isBottom) {
      bool NSW = fitsType(R, T->getType());
      auto H = hull(R, T->getOperand(0)->getType());
      unsigned DW = T->getType()->getIntegerBitWidth();
      auto Hi = H.Hi ? ginac_glue::toAPInt(*H.Hi, 128) : std::nullopt;
      bool NUW = H.Lo && Hi && !H.Lo->is_negative() && Hi->getActiveBits() <= DW;
      if (NSW || NUW)
        Mark("srange.trunc", NSW && NUW ? "both" : NSW ? "nsw" : "nuw");
    }
  }
}

/// Tags \p I with the remaining CVP-style facts: switch cases outside the
/// condition's range (!srange.switch, with the dead case values and "default"
/// if the cases cover the whole range), ashr of a non-negative value
/// (!srange.lshr), and abs/min/max whose result is one of the operands
/// (!srange.pick).
void Solver::annotateCVP(Instruction &I) {
  LLVMContext &Ctx = I.getContext();
  // A checked operation that cannot overflow: !srange.nooverflow (the
  // client folds the overflow bit to false, removing the check).
  if (auto Opc = overflowOpcode(&I)) {
    auto *II = cast<IntrinsicInst>(&I);
    Type *Ty = II->getArgOperand(0)->getType();
    SR A = getState(II->getArgOperand(0)), B = getState(II->getArgOperand(1));
    if (!A.isBottom && !B.isBottom && Ty->getIntegerBitWidth() <= 64) {
      SR R = binaryOp(*Opc, Ty, A, B);
      if (!R.isBottom && fitsType(R, Ty))
        I.setMetadata("srange.nooverflow", MDNode::get(Ctx, {}));
    }
    return;
  }
  if (auto *SI = dyn_cast<SwitchInst>(&I)) {
    Value *C = SI->getCondition();
    SR R = getState(C);
    if (R.isBottom || C->getType()->getIntegerBitWidth() > 64)
      return;
    SmallVector<Metadata *, 8> Ops;
    Type *I64 = Type::getInt64Ty(Ctx);
    unsigned Live = 0;
    for (auto Case : SI->cases()) {
      SE V = SE::num(Case.getCaseValue()->getValue());
      // Outside [lower, upper]: V < lower or V > upper.
      if (SE::provablyLE(SE::add(V, SE::num(1)), R.Lower) ||
          SE::provablyLE(SE::add(R.Upper, SE::num(1)), V))
        Ops.push_back(ConstantAsMetadata::get(
            ConstantInt::get(I64, Case.getCaseValue()->getSExtValue())));
      else
        ++Live;
    }
    // Default unreachable: the live cases are every value of the hull.
    auto H = hull(R, C->getType());
    bool NoDefault = false;
    if (H.Lo && H.Hi && Live) {
      GiNaC::numeric Width = *H.Hi - *H.Lo + 1;
      if (Width.is_integer() && Width <= GiNaC::numeric(static_cast<long>(Live))) {
        // Every value in [Lo, Hi] must be a case.
        NoDefault = true;
        auto Lo = ginac_glue::toAPInt(*H.Lo, 128), Hi = ginac_glue::toAPInt(*H.Hi, 128);
        if (!Lo || !Hi)
          NoDefault = false;
        else
          for (APInt X = *Lo; NoDefault && X.sle(*Hi); ++X)
            NoDefault = SI->findCaseValue(ConstantInt::get(
                            Ctx, X.trunc(C->getType()->getIntegerBitWidth()))) !=
                        SI->case_default();
      }
    }
    if (NoDefault && !SI->defaultDestUnreachable())
      Ops.push_back(MDString::get(Ctx, "default"));
    if (!Ops.empty())
      I.setMetadata("srange.switch", MDTuple::get(Ctx, Ops));
    return;
  }
  if (I.getOpcode() == Instruction::AShr && provablyNonNeg(I.getOperand(0))) {
    I.setMetadata("srange.lshr", MDNode::get(Ctx, {}));
    return;
  }
  auto *II = dyn_cast<IntrinsicInst>(&I);
  if (!II || !II->getType()->isIntegerTy())
    return;
  std::optional<unsigned> Pick;
  Intrinsic::ID ID = II->getIntrinsicID();
  if (ID == Intrinsic::abs) {
    if (provablyNonNeg(II->getArgOperand(0)))
      Pick = 0;
  } else if (ID == Intrinsic::smin || ID == Intrinsic::smax ||
             ID == Intrinsic::umin || ID == Intrinsic::umax) {
    Value *A = II->getArgOperand(0), *B = II->getArgOperand(1);
    bool Unsigned = ID == Intrinsic::umin || ID == Intrinsic::umax;
    if (!Unsigned || (provablyNonNeg(A) && provablyNonNeg(B))) {
      SR RA = getState(A), RB = getState(B);
      if (!RA.isBottom && !RB.isBottom) {
        bool Min = ID == Intrinsic::smin || ID == Intrinsic::umin;
        if (SE::provablyLE(RA.Upper, RB.Lower))
          Pick = Min ? 0 : 1; // A <= B
        else if (SE::provablyLE(RB.Upper, RA.Lower))
          Pick = Min ? 1 : 0; // B <= A
      }
    }
  }
  if (Pick)
    I.setMetadata("srange.pick",
                  MDNode::get(Ctx, ConstantAsMetadata::get(ConstantInt::get(
                                       Type::getInt32Ty(Ctx), *Pick))));
}

/// Decides the comparisons of the function (!srange.cmp) and tags each
/// integer instruction with !srange = !{lower, upper, numeric lower, numeric
/// upper}: the symbolic bounds, then a numeric hull with symbols bounded by
/// their types and range facts, clamped to the instruction's type.
void Solver::annotate() {
  LLVMContext &Ctx = F.getContext();
  enableParamFacts(true);
  // Exact values (linear equalities between variables), for the comparisons
  // that the ranges do not decide; built on first use.
  std::unique_ptr<exactvalues::ExactValues> Exact;
  for (BasicBlock &BB : F) {
    setContext(&BB);
    for (Instruction &I : BB) {
      if (auto *Cmp = dyn_cast<ICmpInst>(&I)) {
        std::optional<bool> D = decideCmp(*Cmp);
        if (!D && UseExact) {
          if (!Exact)
            Exact = std::make_unique<exactvalues::ExactValues>(
                F, LI, DT, [this](Value *V) { return provablyNonNeg(V); });
          if ((D = Exact->decide(*Cmp)))
            ++ExactDecided;
        }
        if (D)
          I.setMetadata("srange.cmp",
                        MDNode::get(Ctx, {MDString::get(Ctx, *D ? "true"
                                                                 : "false")}));
      }
      annotateNoWrap(I);
      annotateSigns(I);
      annotateCVP(I);
      if (!I.getType()->isIntegerTy())
        continue;
      auto It = State.find(&I);
      if (It == State.end())
        continue;
      const SR &R = It->second;
      if (R.isBottom || R.isFull())
        continue;

      std::string Lo, Hi;
      raw_string_ostream LOS(Lo), HIS(Hi);
      R.Lower.print(LOS);
      R.Upper.print(HIS);
      SmallVector<Metadata *, 4> Ops = {MDString::get(Ctx, LOS.str()),
                                        MDString::get(Ctx, HIS.str())};
      auto H = hull(R, I.getType());
      if (H.Lo && H.Hi) {
        Ops.push_back(MDString::get(Ctx, toString(*H.Lo)));
        Ops.push_back(MDString::get(Ctx, toString(*H.Hi)));
      }
      I.setMetadata("srange", MDNode::get(Ctx, Ops));
    }
  }
  // Parameters: !srange.args has one tuple per argument (empty if none).
  setContext(&F.getEntryBlock());
  enableParamFacts(true);
  SmallVector<Metadata *, 4> ArgOps;
  for (Argument &A : F.args()) {
    auto It = State.find(&A);
    if (!A.getType()->isIntegerTy() || It == State.end() ||
        It->second.isBottom) {
      ArgOps.push_back(MDTuple::get(Ctx, {}));
      continue;
    }
    std::string Lo, Hi;
    raw_string_ostream LOS(Lo), HIS(Hi);
    It->second.Lower.print(LOS);
    It->second.Upper.print(HIS);
    SmallVector<Metadata *, 4> Ops = {MDString::get(Ctx, LOS.str()),
                                      MDString::get(Ctx, HIS.str())};
    auto H = hull(It->second, A.getType());
    if (H.Lo && H.Hi) {
      Ops.push_back(MDString::get(Ctx, toString(*H.Lo)));
      Ops.push_back(MDString::get(Ctx, toString(*H.Hi)));
    }
    ArgOps.push_back(MDTuple::get(Ctx, Ops));
  }
  F.setMetadata("srange.args", MDTuple::get(Ctx, ArgOps));
  setContext(nullptr);
  if (InBoundsFacts)
    annotateInBounds();
  if (AliasFacts) {
    annotateAlias();
    if (PrintStats)
      errs() << "sra-alias-stats acc=" << StatAcc << " nooff=" << StatAccNoOff
             << " loopbase=" << StatAccLoopBase << " full=" << StatAccFull
             << " cand=" << StatCand << " pairs=" << StatAliasPairs << "\n";
  }
  enableParamFacts(false);
}

PreservedAnalyses SymbolicRangeAnalysis::run(Module &M,
                                             ModuleAnalysisManager &MAM) {
  SE::MaxArgs = MaxExprArgs;
  SE::MaxNodes = MaxExprNodes;
  auto &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

  // Callers before callees, so that call sites are summarized before the
  // callee is analyzed: the call graph's SCCs come callees first.
  SmallVector<Function *, 64> Order;
  DenseSet<Function *> Recursive;
  CallGraph CG(M);
  for (auto I = scc_begin(&CG); !I.isAtEnd(); ++I)
    for (CallGraphNode *N : *I)
      if (Function *Fn = N->getFunction(); Fn && !Fn->isDeclaration()) {
        Order.push_back(Fn);
        if (I.hasCycle())
          Recursive.insert(Fn);
      }
  std::reverse(Order.begin(), Order.end());
  // The traversal only reaches functions reachable from the root of the call
  // graph. Analyze every other defined function first, since nothing is known
  // about their callers.
  {
    DenseSet<Function *> Seen(Order.begin(), Order.end());
    SmallVector<Function *, 8> Missing;
    for (Function &Fn : M)
      if (!Fn.isDeclaration() && !Seen.count(&Fn))
        Missing.push_back(&Fn);
    Order.insert(Order.begin(), Missing.begin(), Missing.end());
  }
  DenseMap<Function *, unsigned> Position;
  for (unsigned I = 0; I < Order.size(); ++I)
    Position[Order[I]] = I;

  // Functions whose every use is a direct call from a function analyzed
  // before them: only then are all their call sites summarized in time.
  DenseSet<Function *> Eligible;
  if (UseInterprocedural)
    for (Function *Fn : Order) {
      // Only a function no other module can call has all its call sites
      // here (after LTO's internalization, every function but main).
      if (Fn->getName() == "main" || !Fn->hasLocalLinkage() || Fn->isVarArg() ||
          Recursive.count(Fn) || Fn->hasAddressTaken())
        continue;
      bool AllKnown = all_of(Fn->users(), [&](User *U) {
        auto *CB = dyn_cast<CallBase>(U);
        if (!CB || CB->getCalledFunction() != Fn)
          return false;
        auto It = Position.find(CB->getFunction());
        return It != Position.end() && It->second < Position[Fn];
      });
      if (AllKnown)
        Eligible.insert(Fn);
    }

  SummaryMap Summaries;
  for (Function *Fn : Order) {
    // A copy: summarizing this function's calls adds entries to the map.
    std::optional<CallSummary> Summary;
    auto It = Summaries.find(Fn);
    if (Eligible.count(Fn) && It != Summaries.end())
      Summary = It->second;
    Solver S(*Fn, FAM.getResult<LoopAnalysis>(*Fn),
             FAM.getResult<DominatorTreeAnalysis>(*Fn), ArgRanges,
             Summary ? &*Summary : nullptr);
    StatRounds = StatNarrowRounds = 0;
    StatTransfers = StatReused = 0;
    auto T0 = std::chrono::steady_clock::now();
    S.run();
    if (PrintStats)
      errs() << "sra-stats " << Fn->getName() << " insts=" << Fn->getInstructionCount()
             << " rounds=" << StatRounds << " narrow=" << StatNarrowRounds
             << " transfers=" << StatTransfers << " reused=" << StatReused
             << " alias_pairs=" << StatAliasPairs << " ms="
             << std::chrono::duration<double, std::milli>(
                    std::chrono::steady_clock::now() - T0).count()
             << "\n";
    if (UseInterprocedural)
      S.summarizeCalls(Summaries, Eligible);
    S.annotate();
  }
  if (ExactStats)
    errs() << "sra-exact: decided " << ExactDecided << "\n";
  ExactDecided = 0;
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
