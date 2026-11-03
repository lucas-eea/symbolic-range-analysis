//===- ExactValues.cpp - Exact symbolic values of SSA integers ------------===//
//
/// \file
/// Implements the ExactValues analysis declared in ExactValues.h.
//
//===----------------------------------------------------------------------===//

#include "ExactValues.h"
#include "GiNaCGlue.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

using namespace llvm;
using namespace GiNaC;

static cl::opt<bool> Debug("sra-exact-debug", cl::init(false), cl::Hidden,
                           cl::desc("Print the exact values' loop facts and the "
                                    "difference of each comparison"));

namespace exactvalues {

/// Returns the text of \p E, for debug output.
static std::string str(const GiNaC::ex &E) {
  std::ostringstream OS;
  OS << E;
  return OS.str();
}

/// smax(a, b) and smin(a, b): the signed maximum and minimum, used for loop
/// exit values. They evaluate when the difference of their arguments is a
/// number and otherwise stay opaque; decide() splits on which argument is
/// larger.
DECLARE_FUNCTION_2P(smax)
DECLARE_FUNCTION_2P(smin)

static ex smax_eval(const ex &A, const ex &B) {
  ex D = (A - B).expand();
  if (is_a<numeric>(D))
    return ex_to<numeric>(D).is_negative() ? B : A;
  return smax(A, B).hold();
}
static ex smin_eval(const ex &A, const ex &B) {
  ex D = (A - B).expand();
  if (is_a<numeric>(D))
    return ex_to<numeric>(D).is_negative() ? A : B;
  return smin(A, B).hold();
}
REGISTER_FUNCTION(smax, eval_func(smax_eval))
REGISTER_FUNCTION(smin, eval_func(smin_eval))

namespace {

/// Expressions with more nodes than this are dropped and the value becomes its
/// own symbol, which is always sound.
constexpr unsigned MaxNodes = 64;
/// The maximum number of max/min terms to split on when deciding a
/// comparison.
constexpr unsigned MaxSplits = 5;

/// Returns the number of nodes of \p E. Stops counting once the count
/// exceeds \p Limit.
unsigned nodes(const ex &E, unsigned Limit) {
  unsigned N = 1;
  for (size_t I = 0; I < E.nops() && N <= Limit; ++I)
    N += nodes(E.op(I), Limit - N);
  return N;
}

/// Returns the symbol of \p V.
ex self(Value *V) { return ginac_glue::symbolFor(V); }

/// Returns true if \p Phi is a sigma node.
bool isSigma(const PHINode *Phi) { return Phi->getMetadata("sigma") != nullptr; }

/// Returns true if \p E is a number.
bool isNumber(const ex &E) { return is_a<numeric>(E); }

/// Returns true if \p A and \p B are equal as polynomials.
bool same(const ex &A, const ex &B) { return (A - B).expand().is_zero(); }

/// Returns the value that \p V copies through sigma nodes.
Value *throughSigmas(Value *V) {
  while (auto *Phi = dyn_cast<PHINode>(V)) {
    if (!isSigma(Phi))
      break;
    V = Phi->getIncomingValue(0);
  }
  return V;
}

/// Collects into \p Out the symbols that occur in \p E.
void symbolsOf(const ex &E, exset &Out) {
  if (is_a<symbol>(E)) {
    Out.insert(E);
    return;
  }
  for (size_t I = 0; I < E.nops(); ++I)
    symbolsOf(E.op(I), Out);
}

/// Returns an innermost smax or smin of \p E, one whose arguments contain
/// none.
std::optional<ex> innermostMinMax(const ex &E) {
  for (size_t I = 0; I < E.nops(); ++I)
    if (auto In = innermostMinMax(E.op(I)))
      return In;
  if (is_ex_the_function(E, smax) || is_ex_the_function(E, smin))
    return E;
  return std::nullopt;
}

/// Returns false if the constraints \p C >= 0 are infeasible over the
/// rationals, by Fourier-Motzkin elimination. Non-linear constraints are
/// ignored, so the answer errs towards feasible.
bool feasible(std::vector<ex> C) {
  // Keep the linear constraints.
  symbol T("t");
  std::vector<ex> Lin;
  for (const ex &E : C) {
    exset Syms;
    symbolsOf(E, Syms);
    exmap Scale;
    for (const ex &S : Syms)
      Scale[S] = T * S;
    ex Scaled = E.subs(Scale).expand();
    if (Scaled.is_polynomial(T) && Scaled.degree(T) <= 1)
      Lin.push_back(E.expand());
  }
  for (unsigned Step = 0; Step < 8; ++Step) {
    for (const ex &E : Lin)
      if (isNumber(E) && ex_to<numeric>(E).is_negative())
        return false;
    exset Syms;
    for (const ex &E : Lin)
      symbolsOf(E, Syms);
    if (Syms.empty())
      return true;
    ex X = *Syms.begin();
    std::vector<ex> Pos, Neg, Next;
    for (const ex &E : Lin) {
      ex K = E.coeff(X, 1);
      if (!isNumber(K))
        return true;
      if (ex_to<numeric>(K).is_positive())
        Pos.push_back(E);
      else if (ex_to<numeric>(K).is_negative())
        Neg.push_back(E);
      else
        Next.push_back(E);
    }
    for (const ex &P : Pos)
      for (const ex &N : Neg)
        Next.push_back((P * -N.coeff(X, 1) + N * P.coeff(X, 1)).expand());
    if (Next.size() > 200)
      return true;
    Lin = std::move(Next);
  }
  return true;
}

} // namespace

ExactValues::ExactValues(Function &F, LoopInfo &LI, DominatorTree &DT,
                         std::function<bool(Value *)> NonNeg)
    : F(F), LI(LI), DT(DT), NonNeg(std::move(NonNeg)) {
  // Evaluate with the loop relations found so far until deriving them again
  // gives the same relations. A stable relation holds on loop entry and is
  // preserved by an iteration, so it holds by induction. If the relations do
  // not settle, none is used.
  evaluate();
  bool Stable = false;
  for (unsigned Round = 0; Round < 8 && !Stable; ++Round) {
    Stable = !deriveLoopFacts();
    if (!Stable)
      evaluate();
  }
  if (!Stable) {
    Counters.clear();
    Exits.clear();
    evaluate();
  }
  if (Debug) {
    errs() << "sra-exact: " << F.getName() << (Stable ? "" : " (unstable)") << "\n";
    for (auto &[Phi, E] : Counters)
      errs() << "  counter " << Phi->getName() << " = " << str(E) << "\n";
    for (auto &[Sigma, X] : Exits)
      errs() << "  exit " << Sigma->getName() << " (" << X.Counter->getName()
             << ") = " << str(X.Value) << "\n";
  }
}

GiNaC::ex ExactValues::get(Value *V) {
  if (auto *CI = dyn_cast<ConstantInt>(V))
    return ginac_glue::toNumeric(CI->getValue());
  auto It = Val.find(V);
  return It == Val.end() ? self(V) : It->second;
}

void ExactValues::evaluate() {
  Val.clear();
  ReversePostOrderTraversal<Function *> RPOT(&F);
  for (BasicBlock *BB : RPOT) {
    // The phis of a join come first, since the rest of the block uses them.
    if (!LI.isLoopHeader(BB))
      joinBlock(BB);
    for (Instruction &I : *BB) {
      if (!I.getType()->isIntegerTy())
        continue;
      if (auto *Phi = dyn_cast<PHINode>(&I); Phi && !isSigma(Phi) &&
                                             !LI.isLoopHeader(BB))
        continue; // Handled by joinBlock().
      ex E = transfer(&I);
      if (nodes(E, MaxNodes) > MaxNodes)
        E = self(&I);
      Val[&I] = E;
    }
  }
}

GiNaC::ex ExactValues::transfer(Value *V) {
  auto *I = cast<Instruction>(V);
  if (auto *Phi = dyn_cast<PHINode>(I)) {
    if (isSigma(Phi)) {
      auto X = Exits.find(Phi);
      return X != Exits.end() ? X->second.Value : get(Phi->getIncomingValue(0));
    }
    auto C = Counters.find(Phi);
    return C != Counters.end() ? C->second : self(Phi);
  }
  if (auto *Bin = dyn_cast<BinaryOperator>(I)) {
    auto *OBO = dyn_cast<OverflowingBinaryOperator>(Bin);
    if (!OBO || !OBO->hasNoSignedWrap())
      return self(I);
    ex A = get(Bin->getOperand(0)), B = get(Bin->getOperand(1));
    switch (Bin->getOpcode()) {
    case Instruction::Add:
      return (A + B).expand();
    case Instruction::Sub:
      return (A - B).expand();
    case Instruction::Mul:
      return (A * B).expand();
    case Instruction::Shl:
      // x << k with nsw is x * 2^k; k >= width would be poison.
      if (auto *K = dyn_cast<ConstantInt>(Bin->getOperand(1)))
        if (K->getValue().ult(Bin->getType()->getIntegerBitWidth()))
          return (A * pow(numeric(2), numeric(K->getZExtValue()))).expand();
      return self(I);
    default:
      return self(I);
    }
  }
  if (auto *Cast = dyn_cast<CastInst>(I)) {
    Value *X = Cast->getOperand(0);
    if (!X->getType()->isIntegerTy())
      return self(I);
    if (isa<SExtInst>(Cast))
      return get(X);
    // A zero extension keeps the signed value of a non-negative value only.
    if (isa<ZExtInst>(Cast) && (Cast->hasNonNeg() || NonNeg(X)))
      return get(X);
    return self(I);
  }
  if (auto *Sel = dyn_cast<SelectInst>(I)) {
    ex T = get(Sel->getTrueValue()), E = get(Sel->getFalseValue());
    return same(T, E) ? T : self(I);
  }
  // Loads, calls, freeze (a frozen poison can be any value), division,
  // bitwise operations and the rest are unknowns of their own.
  return self(I);
}

void ExactValues::joinBlock(BasicBlock *BB) {
  // The value on each incoming edge, or none if a value is undefined or not
  // evaluated yet (a back edge of an irreducible loop).
  SmallVector<PHINode *, 4> Phis;
  SmallVector<SmallVector<ex, 4>, 4> In;
  for (PHINode &Phi : BB->phis()) {
    if (!Phi.getType()->isIntegerTy() || isSigma(&Phi))
      continue;
    SmallVector<ex, 4> Vals;
    bool Ok = Phi.getNumIncomingValues() > 0;
    for (unsigned I = 0; I < Phi.getNumIncomingValues() && Ok; ++I) {
      Value *V = Phi.getIncomingValue(I);
      auto *VI = dyn_cast<Instruction>(V);
      if (isa<UndefValue>(V) || (VI && VI->getType()->isIntegerTy() && !Val.count(VI)))
        Ok = false;
      else
        Vals.push_back(get(V));
    }
    Phis.push_back(&Phi);
    In.push_back(Ok ? Vals : SmallVector<ex, 4>());
  }
  // A phi whose incoming values are all equal is that value. The others are
  // their own symbols, and each may be related to another one R by
  // Q = a * R + D on every edge, with R staying its own symbol.
  SmallVector<bool, 4> Free(Phis.size(), false);
  for (unsigned P = 0; P < Phis.size(); ++P) {
    const auto &V = In[P];
    bool Same = !V.empty();
    for (unsigned I = 1; I < V.size() && Same; ++I)
      Same = same(V[I], V[0]);
    Val[Phis[P]] = Same ? V[0] : self(Phis[P]);
    Free[P] = !Same && !V.empty();
  }
  SmallVector<bool, 4> IsReference(Phis.size(), false);
  for (unsigned Q = 0; Q < Phis.size(); ++Q) {
    if (!Free[Q])
      continue;
    unsigned N = In[Q].size();
    for (unsigned R = 0; R < Phis.size(); ++R) {
      if (R == Q || !Free[R] || In[R].size() != N)
        continue;
      // The reference R must still be its own symbol.
      if (!same(Val[Phis[R]], self(Phis[R])))
        continue;
      // Line up the incoming blocks, which each phi lists in its own order.
      SmallVector<ex, 4> RIn;
      bool Ok = true;
      for (unsigned I = 0; I < N && Ok; ++I) {
        int K = Phis[R]->getBasicBlockIndex(Phis[Q]->getIncomingBlock(I));
        if (K < 0)
          Ok = false;
        else
          RIn.push_back(get(Phis[R]->getIncomingValue(K)));
      }
      if (!Ok)
        continue;
      std::optional<ex> A;
      for (unsigned I = 1; I < N && !A; ++I) {
        ex DR = (RIn[I] - RIn[0]).expand();
        if (DR.is_zero())
          continue;
        ex Ratio = ((In[Q][I] - In[Q][0]) / DR).normal();
        if (!isNumber(Ratio))
          break;
        A = Ratio;
      }
      if (!A)
        continue;
      ex D = (In[Q][0] - *A * RIn[0]).expand();
      for (unsigned I = 1; I < N && Ok; ++I)
        Ok = same(In[Q][I] - *A * RIn[I], D);
      if (!Ok)
        continue;
      Val[Phis[Q]] = (*A * self(Phis[R]) + D).expand();
      IsReference[R] = true;
      Free[Q] = false; // Q is related, so it cannot be a reference.
      break;
    }
  }
}

bool ExactValues::deriveLoopFacts() {
  DenseMap<PHINode *, ex> NewCounters;
  DenseMap<PHINode *, ExitFact> NewExits;
  struct Cand {
    PHINode *Phi;
    ex Start, Step;
  };
  DenseMap<PHINode *, Cand> CandOf;
  for (Loop *L : LI.getLoopsInPreorder()) {
    BasicBlock *H = L->getHeader();
    SmallVector<Cand, 4> Cands;
    for (PHINode &Phi : H->phis()) {
      if (!Phi.getType()->isIntegerTy() || isSigma(&Phi))
        continue;
      std::optional<ex> Start, Step;
      bool Ok = true;
      for (unsigned I = 0; I < Phi.getNumIncomingValues() && Ok; ++I) {
        Value *V = Phi.getIncomingValue(I);
        if (isa<UndefValue>(V)) {
          Ok = false;
        } else if (L->contains(Phi.getIncomingBlock(I))) {
          // The change over one iteration, the same on every back edge.
          ex S = (get(V) - get(&Phi)).expand();
          Ok = !Step || same(S, *Step);
          Step = S;
        } else {
          // The one value from outside the loop, possibly on several edges.
          ex S = get(V);
          Ok = !Start || same(S, *Start);
          Start = S;
        }
      }
      if (Ok && Start && Step) {
        Cands.push_back({&Phi, *Start, *Step});
        CandOf[&Phi] = Cands.back();
      }
    }
    // The primary counter P0 is the first one that changes and is its own
    // symbol. Another counter Pj whose change is always a times that of P0
    // keeps Pj - a * P0 constant, so Pj = start_j + a * (P0 - start_0).
    const Cand *P0 = nullptr;
    for (const Cand &C : Cands)
      if (!C.Step.is_zero() && !Counters.count(C.Phi)) {
        P0 = &C;
        break;
      }
    for (const Cand &C : Cands) {
      if (P0 && &C == P0)
        continue;
      if (C.Step.is_zero()) {
        NewCounters[C.Phi] = C.Start; // Never changes.
        continue;
      }
      if (!P0)
        continue;
      ex A = (C.Step / P0->Step).normal();
      if (isNumber(A))
        NewCounters[C.Phi] = (C.Start + A * (self(P0->Phi) - P0->Start)).expand();
    }
  }
  // Exit values: on the edge that leaves loop L from its header when P < B
  // fails, with P a counter of L stepping by +1 from s and B invariant, P is
  // max(s, B); counting down by -1 is symmetric. The sigma node of P on that
  // edge gets this value.
  for (BasicBlock &BB : F)
    for (PHINode &Sigma : BB.phis()) {
      if (!isSigma(&Sigma) || !Sigma.getType()->isIntegerTy())
        continue;
      BasicBlock *Hd = Sigma.getIncomingBlock(0);
      Loop *L = LI.getLoopFor(Hd);
      if (!L || L->getHeader() != Hd || L->contains(&BB))
        continue;
      auto *Br = dyn_cast<BranchInst>(Hd->getTerminator());
      auto *Cmp = Br && Br->isConditional() ? dyn_cast<ICmpInst>(Br->getCondition()) : nullptr;
      if (!Cmp)
        continue;
      auto *P = dyn_cast<PHINode>(throughSigmas(Sigma.getIncomingValue(0)));
      if (!P || P->getParent() != Hd || !CandOf.count(P))
        continue;
      // The predicate that holds on this edge, with P on the left.
      CmpInst::Predicate Pred = Cmp->getPredicate();
      if (Br->getSuccessor(0) != &BB)
        Pred = CmpInst::getInversePredicate(Pred);
      Value *B;
      if (throughSigmas(Cmp->getOperand(0)) == P) {
        B = Cmp->getOperand(1);
      } else if (throughSigmas(Cmp->getOperand(1)) == P) {
        B = Cmp->getOperand(0);
        Pred = CmpInst::getSwappedPredicate(Pred);
      } else {
        continue;
      }
      // The bound must be the same on every iteration, so its exact value
      // may only use values from outside the loop.
      bool Invariant = true;
      exset BSyms;
      symbolsOf(get(B), BSyms);
      for (const ex &Sym : BSyms)
        if (auto *BI = dyn_cast_or_null<Instruction>(ginac_glue::valueFor(Sym)))
          Invariant &= !L->contains(BI);
      if (!Invariant)
        continue;
      const Cand &C = CandOf[P];
      if (!isNumber(C.Step))
        continue;
      const numeric &S = ex_to<numeric>(C.Step);
      ex Bound = get(B), Start = C.Start;
      std::optional<ex> X;
      if (S.is_equal(numeric(1)) && Pred == CmpInst::ICMP_SGE)
        X = smax(Start, Bound);
      else if (S.is_equal(numeric(1)) && Pred == CmpInst::ICMP_SGT)
        X = smax(Start, Bound + 1);
      else if (S.is_equal(numeric(-1)) && Pred == CmpInst::ICMP_SLE)
        X = smin(Start, Bound);
      else if (S.is_equal(numeric(-1)) && Pred == CmpInst::ICMP_SLT)
        X = smin(Start, Bound - 1);
      if (X)
        NewExits[&Sigma] = {P, *X};
    }
  bool Changed = NewCounters.size() != Counters.size() || NewExits.size() != Exits.size();
  for (auto &[Phi, E] : NewCounters) {
    auto It = Counters.find(Phi);
    Changed |= It == Counters.end() || !same(It->second, E);
  }
  for (auto &[Sigma, X] : NewExits) {
    auto It = Exits.find(Sigma);
    Changed |= It == Exits.end() || It->second.Counter != X.Counter ||
               !same(It->second.Value, X.Value);
  }
  Counters = std::move(NewCounters);
  Exits = std::move(NewExits);
  return Changed;
}

std::optional<bool> ExactValues::decide(ICmpInst &Cmp) {
  Type *Ty = Cmp.getOperand(0)->getType();
  if (!Ty->isIntegerTy() || Ty->getIntegerBitWidth() < 2)
    return std::nullopt;
  ex D = (get(Cmp.getOperand(0)) - get(Cmp.getOperand(1))).expand();
  // A counter whose exit edge dominates the comparison has its exit value
  // there.
  for (unsigned Round = 0; Round < 3; ++Round) {
    exmap Sub;
    for (auto &[Sigma, X] : Exits) {
      if (!DT.dominates(Sigma->getParent(), Cmp.getParent()))
        continue;
      // With counter = c * s + rest, where s is the free symbol of the
      // counter's loop, s is (exit value - rest) / c on the exit edge.
      ex E = get(X.Counter);
      Loop *L = LI.getLoopFor(X.Counter->getParent());
      exset Syms;
      symbolsOf(E, Syms);
      for (const ex &Sym : Syms) {
        auto *SP = dyn_cast_or_null<PHINode>(ginac_glue::valueFor(Sym));
        if (!SP || SP->getParent() != L->getHeader())
          continue;
        ex C = E.coeff(Sym, 1);
        if (E.degree(Sym) != 1 || !isNumber(C) || C.is_zero())
          continue;
        Sub[Sym] = ((X.Value - (E - C * Sym)) / C).expand();
        break;
      }
    }
    ex Next = D.subs(Sub).expand();
    if (same(Next, D))
      break;
    D = Next;
  }
  if (Debug)
    errs() << "sra-exact: " << F.getName() << ": " << Cmp.getName() << ": " << str(D) << "\n";
  CmpInst::Predicate P = Cmp.getPredicate();
  // Values are signed. Between non-negative values the unsigned order is the
  // signed one.
  if (ICmpInst::isUnsigned(P)) {
    if (!NonNeg(Cmp.getOperand(0)) || !NonNeg(Cmp.getOperand(1)))
      return std::nullopt;
    P = ICmpInst::getSignedPredicate(P);
  }
  auto Holds = [&](const numeric &N) -> std::optional<bool> {
    switch (P) {
    case CmpInst::ICMP_EQ:
      return N.is_zero();
    case CmpInst::ICMP_NE:
      return !N.is_zero();
    case CmpInst::ICMP_SLT:
      return N.is_negative();
    case CmpInst::ICMP_SLE:
      return N.is_negative() || N.is_zero();
    case CmpInst::ICMP_SGT:
      return N.is_positive();
    case CmpInst::ICMP_SGE:
      return N.is_positive() || N.is_zero();
    default:
      return std::nullopt;
    }
  };
  // Split on every max/min, innermost first. In each feasible case the
  // difference must be a number, and all cases must give the same answer.
  std::optional<bool> Answer;
  bool Undecided = false;
  std::function<void(const ex &, std::vector<ex> &, unsigned)> Split =
      [&](const ex &E, std::vector<ex> &C, unsigned Depth) {
        if (Undecided)
          return;
        auto M = innermostMinMax(E);
        if (!M) {
          if (!feasible(C))
            return;
          std::optional<bool> R = isNumber(E) ? Holds(ex_to<numeric>(E)) : std::nullopt;
          if (!R || (Answer && *Answer != *R))
            Undecided = true;
          else
            Answer = R;
          return;
        }
        if (Depth >= MaxSplits) {
          Undecided = true;
          return;
        }
        bool IsMax = is_ex_the_function(*M, smax);
        ex A = M->op(0), B = M->op(1);
        // If A >= B, max is A and min is B; if A <= B - 1, the opposite.
        C.push_back((A - B).expand());
        Split(E.subs(*M == (IsMax ? A : B)).expand(), C, Depth + 1);
        C.back() = (B - A - 1).expand();
        Split(E.subs(*M == (IsMax ? B : A)).expand(), C, Depth + 1);
        C.pop_back();
      };
  std::vector<ex> C;
  Split(D, C, 0);
  if (Undecided)
    return std::nullopt;
  return Answer;
}

} // namespace exactvalues
