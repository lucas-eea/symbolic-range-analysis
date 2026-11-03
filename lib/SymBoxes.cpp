//===- SymBoxes.cpp - Symbolic interval domain ----------------------------===//
//
/// \file
/// Implements SymExpr and the interval evaluation declared in SymBoxes.h.
//
//===----------------------------------------------------------------------===//

#include "SymBoxes.h"
#include <algorithm>
#include <sstream>
#include <unordered_map>

using namespace GiNaC;

namespace symboxes {

NumInterval evaluate(const SymExpr &E, SymbolBoundsFn Bounds);

unsigned SymExpr::MaxArgs = 8;
unsigned SymExpr::MaxNodes = 64;

using BoundsFunction =
    std::function<std::optional<std::pair<numeric, numeric>>(llvm::Value *)>;
static const BoundsFunction *ContextBounds = nullptr;

void setContextBounds(const BoundsFunction *F) { ContextBounds = F; }

static const std::function<SymFacts(llvm::Value *)> *SymbolicFacts = nullptr;
static unsigned FactDepth = 0;

void setSymbolicFacts(const std::function<SymFacts(llvm::Value *)> *F) {
  SymbolicFacts = F;
}

/// Memo tables for expanded sums and differences, which depend only on the
/// expressions. The solver asks the same questions in every round.
bool UseMemo = true;

namespace {
using ExPair = std::pair<ex, ex>;
struct ExPairHash {
  size_t operator()(const ExPair &P) const {
    return P.first.gethash() * 31u + P.second.gethash();
  }
};
struct ExPairEq {
  bool operator()(const ExPair &A, const ExPair &B) const {
    return A.first.is_equal(B.first) && A.second.is_equal(B.second);
  }
};
using ExMemo = std::unordered_map<ExPair, ex, ExPairHash, ExPairEq>;
constexpr size_t MaxMemo = 1 << 20;

/// Returns (A + B).expand(), or (B - A).expand() if \p Negate, memoized.
ex memoSum(ExMemo &M, const ex &A, const ex &B, bool Negate) {
  if (!symboxes::UseMemo)
    return (Negate ? B - A : A + B).expand();
  if (M.size() > MaxMemo)
    M.clear();
  auto [It, New] = M.try_emplace(ExPair(A, B));
  if (New)
    It->second = (Negate ? B - A : A + B).expand();
  return It->second;
}
ExMemo &sumMemo() {
  static ExMemo M;
  return M;
}
ExMemo &diffMemo() {
  static ExMemo M;
  return M;
}
} // namespace

/// Decomposes a polynomial of the form s + c, with s a symbol and c a number.
static std::optional<std::pair<llvm::Value *, numeric>>
symbolPlusConst(const ex &E) {
  if (is_a<symbol>(E))
    if (llvm::Value *V = ginac_glue::valueFor(E))
      return std::make_pair(V, numeric(0));
  if (is_a<add>(E) && E.nops() == 2)
    for (unsigned K = 0; K < 2; ++K)
      if (is_a<symbol>(E.op(K)) && is_exactly_a<numeric>(E.op(1 - K)))
        if (llvm::Value *V = ginac_glue::valueFor(E.op(K)))
          return std::make_pair(V, ex_to<numeric>(E.op(1 - K)));
  return std::nullopt;
}

/// Returns the largest constant, the signed maximum of SymExpr::Width bits.
static const numeric &maxConst() {
  static const numeric M = pow(numeric(2), numeric(SymExpr::Width - 1)) - 1;
  return M;
}
/// Returns the smallest constant, the signed minimum of SymExpr::Width bits.
static const numeric &minConst() {
  static const numeric M = -maxConst() - 1;
  return M;
}

/// Returns Max for Min and Min for Max.
static SymExpr::Kind flip(SymExpr::Kind K) {
  return K == SymExpr::Min ? SymExpr::Max : SymExpr::Min;
}

static const std::vector<SymExpr> &noArgs() {
  static const std::vector<SymExpr> None;
  return None;
}

const std::vector<SymExpr> &SymExpr::args() const {
  return Args ? *Args : noArgs();
}

SymExpr SymExpr::fromPoly(const ex &E) {
  ex X = E.expand();
  if (is_exactly_a<numeric>(X)) {
    const numeric &N = ex_to<numeric>(X);
    if (N > maxConst())
      return inf();
    if (N < minConst())
      return negInf();
  }
  SymExpr R(Poly);
  R.P = X;
  return R;
}

SymExpr SymExpr::num(int64_t C) { return fromPoly(numeric(static_cast<long>(C))); }

SymExpr SymExpr::num(const llvm::APInt &C) {
  assert(C.getBitWidth() <= Width && "constant wider than SymExpr::Width");
  return fromPoly(ginac_glue::toNumeric(C));
}

SymExpr SymExpr::sym(llvm::Value *V) {
  return fromPoly(ginac_glue::symbolFor(V));
}

bool SymExpr::isConst() const {
  return K == Poly && is_exactly_a<numeric>(P);
}

llvm::APInt SymExpr::constVal() const {
  assert(isConst() && "not a constant");
  return *ginac_glue::toAPInt(ex_to<numeric>(P), Width);
}

SymExpr SymExpr::neg(const SymExpr &A) {
  switch (A.K) {
  case Poly:
    return fromPoly(-A.P);
  case PosInf:
    return negInf();
  case NegInf:
    return inf();
  case Top:
    return top();
  case Min:
  case Max: {
    std::vector<SymExpr> Args;
    for (const SymExpr &X : A.args())
      Args.push_back(neg(X));
    return minMax(flip(A.K), std::move(Args));
  }
  }
  llvm_unreachable("covered switch");
}

SymExpr SymExpr::add(const SymExpr &A, const SymExpr &B) {
  if (A.K == Top || B.K == Top)
    return top();
  if (A.K == NegInf || B.K == NegInf)
    return negInf();
  if (A.K == PosInf || B.K == PosInf)
    return inf();
  // Addition is monotone: push it inside min/max.
  if (A.K == Min || A.K == Max) {
    std::vector<SymExpr> Args;
    for (const SymExpr &X : A.args())
      Args.push_back(add(X, B));
    return minMax(A.K, std::move(Args));
  }
  if (B.K == Min || B.K == Max)
    return add(B, A);
  return fromPoly(memoSum(sumMemo(), A.P, B.P, false));
}

SymExpr SymExpr::sub(const SymExpr &A, const SymExpr &B) {
  return add(A, neg(B));
}

SymExpr SymExpr::scale(const SymExpr &E, const numeric &C) {
  if (C.is_zero())
    return num(0);
  switch (E.K) {
  case Poly:
    return fromPoly(C * E.P);
  case PosInf:
  case NegInf:
    return C.is_positive() ? E : neg(E);
  case Top:
    return top();
  case Min:
  case Max: {
    std::vector<SymExpr> Args;
    for (const SymExpr &X : E.args())
      Args.push_back(scale(X, C));
    return minMax(C.is_positive() ? E.K : flip(E.K), std::move(Args));
  }
  }
  llvm_unreachable("covered switch");
}

SymExpr SymExpr::mul(const SymExpr &A, const SymExpr &B) {
  if (A.isConst())
    return scale(B, ex_to<numeric>(A.P));
  if (B.isConst())
    return scale(A, ex_to<numeric>(B.P));
  if (A.K == Top || B.K == Top)
    return top();
  if (A.K == Poly && B.K == Poly)
    return fromPoly(A.P * B.P);
  // The sign of a symbolic factor is unknown, so the product is not
  // representable.
  return top();
}

SymExpr SymExpr::div(const SymExpr &A, const SymExpr &B) {
  if (!B.isConst())
    return top();
  const numeric &C = ex_to<numeric>(B.P);
  if (C.is_zero())
    return num(0);
  switch (A.K) {
  case Poly:
    return fromPoly(ginac_glue::idiv(A.P, C));
  case PosInf:
  case NegInf:
    return C.is_positive() ? A : neg(A);
  case Top:
    return top();
  case Min:
  case Max: {
    // Truncating division by a constant is monotone (non-increasing for a
    // negative divisor).
    std::vector<SymExpr> Args;
    for (const SymExpr &X : A.args())
      Args.push_back(div(X, B));
    return minMax(C.is_positive() ? A.K : flip(A.K), std::move(Args));
  }
  }
  llvm_unreachable("covered switch");
}

bool SymExpr::provablyLE(const SymExpr &A, const SymExpr &B) {
  if (A.K == Top || B.K == Top)
    return false;
  if (A.K == NegInf || B.K == PosInf)
    return true;
  if (A.K == PosInf || B.K == NegInf)
    return false;
  if (A == B)
    return true;
  if (A.K == Poly && B.K == Poly) {
    ex D = memoSum(diffMemo(), A.P, B.P, true);
    if (is_exactly_a<numeric>(D))
      return !ex_to<numeric>(D).is_negative();
    // Symbolic facts: s + c <= B if upper(s) + c <= B; A <= t + d if
    // A <= lower(t) + d. The depth limit stops chains of facts.
    if (SymbolicFacts && FactDepth < 2) {
      ++FactDepth;
      bool Proved = false;
      if (auto SC = symbolPlusConst(A.P))
        if (auto U = (*SymbolicFacts)(SC->first).second)
          Proved = provablyLE(add(*U, fromPoly(SC->second)), B);
      if (!Proved)
        if (auto TD = symbolPlusConst(B.P))
          if (auto L = (*SymbolicFacts)(TD->first).first)
            Proved = provablyLE(A, add(*L, fromPoly(TD->second)));
      --FactDepth;
      if (Proved)
        return true;
    }
    // Numeric bounds where the expression is built: n >= 1 proves n - 1 >= 0.
    if (ContextBounds) {
      NumInterval I = evaluate(fromPoly(D), *ContextBounds);
      return I.Lo && !I.Lo->is_negative();
    }
    return false;
  }
  // min(a_i) <= B if some a_i <= B; A <= max(b_i) if A <= some b_i.
  if (A.K == Min)
    for (const SymExpr &X : A.args())
      if (provablyLE(X, B))
        return true;
  if (B.K == Max)
    for (const SymExpr &X : B.args())
      if (provablyLE(A, X))
        return true;
  // max(a_i) <= B if every a_i <= B; A <= min(b_i) if A <= every b_i.
  if (A.K == Max &&
      std::all_of(A.args().begin(), A.args().end(),
                  [&](const SymExpr &X) { return provablyLE(X, B); }))
    return true;
  if (B.K == Min &&
      std::all_of(B.args().begin(), B.args().end(),
                  [&](const SymExpr &X) { return provablyLE(A, X); }))
    return true;
  return false;
}

SymExpr SymExpr::minMax(Kind K, std::vector<SymExpr> In) {
  assert(K == Min || K == Max);
  // Flatten nested min/max of the same kind; fold infinities.
  std::vector<SymExpr> Flat;
  for (SymExpr &E : In) {
    if (E.K == Top)
      return top();
    if (E.K == K) {
      Flat.insert(Flat.end(), E.args().begin(), E.args().end());
      continue;
    }
    if ((K == Min && E.K == NegInf) || (K == Max && E.K == PosInf))
      return E; // Absorbing.
    if ((K == Min && E.K == PosInf) || (K == Max && E.K == NegInf))
      continue; // Neutral.
    Flat.push_back(std::move(E));
  }
  if (Flat.empty())
    return K == Min ? inf() : negInf();

  // Drop the arguments that another argument provably dominates.
  auto Dominates = [K](const SymExpr &X, const SymExpr &Y) {
    return K == Min ? provablyLE(X, Y) : provablyLE(Y, X);
  };
  std::vector<SymExpr> Kept;
  for (SymExpr &E : Flat) {
    if (std::any_of(Kept.begin(), Kept.end(),
                    [&](const SymExpr &O) { return Dominates(O, E); }))
      continue;
    Kept.erase(std::remove_if(Kept.begin(), Kept.end(),
                              [&](const SymExpr &O) { return Dominates(E, O); }),
               Kept.end());
    Kept.push_back(std::move(E));
  }
  if (Kept.size() == 1)
    return Kept.front();
  if (Kept.size() > MaxArgs)
    return top();
  std::sort(Kept.begin(), Kept.end(), [](const SymExpr &X, const SymExpr &Y) {
    return compare(X, Y) < 0;
  });
  unsigned Nodes = 1;
  for (const SymExpr &E : Kept)
    Nodes += E.Nodes;
  if (Nodes > MaxNodes)
    return top();
  SymExpr R(K);
  R.Args = std::make_shared<const std::vector<SymExpr>>(std::move(Kept));
  R.Nodes = Nodes;
  return R;
}

SymExpr SymExpr::mkMin(const SymExpr &A, const SymExpr &B) {
  return minMax(Min, {A, B});
}

SymExpr SymExpr::mkMax(const SymExpr &A, const SymExpr &B) {
  return minMax(Max, {A, B});
}

bool SymExpr::operator==(const SymExpr &O) const {
  if (K != O.K)
    return false;
  switch (K) {
  case Poly:
    return P.is_equal(O.P);
  case Min:
  case Max: {
    const auto &A = args(), &B = O.args();
    return A.size() == B.size() && std::equal(A.begin(), A.end(), B.begin());
  }
  default:
    return true;
  }
}

int SymExpr::compare(const SymExpr &A, const SymExpr &B) {
  if (A.K != B.K)
    return A.K < B.K ? -1 : 1;
  switch (A.K) {
  case Poly:
    return A.P.compare(B.P);
  case Min:
  case Max: {
    const auto &X = A.args(), &Y = B.args();
    if (X.size() != Y.size())
      return X.size() < Y.size() ? -1 : 1;
    for (size_t I = 0; I < X.size(); ++I)
      if (int C = compare(X[I], Y[I]))
        return C;
    return 0;
  }
  default:
    return 0;
  }
}

/// Prints a GiNaC expression in a deterministic order, since GiNaC's own
/// order depends on hash values that vary between runs. Constants come first
/// in sums and numeric coefficients first in products; other terms and
/// factors are sorted by their text.
static std::string printEx(const ex &E) {
  auto Default = [](const ex &X) {
    std::ostringstream SS;
    SS << X;
    return SS.str();
  };
  if (is_a<add>(E)) {
    std::string Const;
    std::vector<std::string> Terms;
    for (size_t I = 0; I < E.nops(); ++I) {
      if (is_exactly_a<numeric>(E.op(I)))
        Const = printEx(E.op(I));
      else
        Terms.push_back(printEx(E.op(I)));
    }
    std::sort(Terms.begin(), Terms.end());
    if (!Const.empty())
      Terms.insert(Terms.begin(), Const);
    std::string Out;
    for (const std::string &T : Terms)
      Out += (Out.empty() || T[0] == '-') ? T : "+" + T;
    return Out;
  }
  if (is_a<mul>(E)) {
    numeric Coeff(1);
    std::vector<std::string> Factors;
    for (size_t I = 0; I < E.nops(); ++I) {
      const ex &F = E.op(I);
      if (is_exactly_a<numeric>(F))
        Coeff *= ex_to<numeric>(F);
      else
        Factors.push_back(is_a<add>(F) ? "(" + printEx(F) + ")" : printEx(F));
    }
    std::sort(Factors.begin(), Factors.end());
    std::string Out;
    for (const std::string &F : Factors)
      Out += (Out.empty() ? "" : "*") + F;
    if (Coeff.is_equal(numeric(1)))
      return Out;
    if (Coeff.is_equal(numeric(-1)))
      return "-" + Out;
    return Default(Coeff) + "*" + Out;
  }
  if (is_a<power>(E)) {
    const ex &B = E.op(0);
    std::string Base = printEx(B);
    if (is_a<add>(B) || is_a<mul>(B))
      Base = "(" + Base + ")";
    return Base + "^" + printEx(E.op(1));
  }
  if (is_a<function>(E)) {
    std::string Out = ex_to<function>(E).get_name() + "(";
    for (size_t I = 0; I < E.nops(); ++I)
      Out += (I ? "," : "") + printEx(E.op(I));
    return Out + ")";
  }
  return Default(E);
}

void SymExpr::print(llvm::raw_ostream &OS) const {
  switch (K) {
  case Poly:
    OS << printEx(P);
    return;
  case PosInf:
    OS << "+∞";
    return;
  case NegInf:
    OS << "-∞";
    return;
  case Top:
    OS << "⊤";
    return;
  case Min:
  case Max: {
    std::vector<std::string> Texts;
    for (const SymExpr &X : args()) {
      std::string T;
      llvm::raw_string_ostream TS(T);
      X.print(TS);
      Texts.push_back(T);
    }
    std::sort(Texts.begin(), Texts.end());
    OS << (K == Min ? "min(" : "max(");
    for (size_t I = 0; I < Texts.size(); ++I)
      OS << (I ? ", " : "") << Texts[I];
    OS << ")";
    return;
  }
  }
}

//===----------------------------------------------------------------------===//
// Interval evaluation
//===----------------------------------------------------------------------===//

static NumInterval point(const numeric &N) { return {N, N}; }

static NumInterval addIv(const NumInterval &A, const NumInterval &B) {
  NumInterval R;
  if (A.Lo && B.Lo)
    R.Lo = *A.Lo + *B.Lo;
  if (A.Hi && B.Hi)
    R.Hi = *A.Hi + *B.Hi;
  return R;
}

static bool isZero(const NumInterval &A) {
  return A.Lo && A.Hi && A.Lo->is_zero() && A.Hi->is_zero();
}

static NumInterval mulIv(const NumInterval &A, const NumInterval &B) {
  if (isZero(A) || isZero(B))
    return point(0);
  if (!A.Lo || !A.Hi || !B.Lo || !B.Hi)
    return {};
  numeric C[] = {*A.Lo * *B.Lo, *A.Lo * *B.Hi, *A.Hi * *B.Lo, *A.Hi * *B.Hi};
  return {*std::min_element(std::begin(C), std::end(C)),
          *std::max_element(std::begin(C), std::end(C))};
}

static NumInterval evalEx(const ex &E, SymbolBoundsFn Bounds) {
  if (is_exactly_a<numeric>(E))
    return point(ex_to<numeric>(E));
  if (is_a<symbol>(E)) {
    if (llvm::Value *V = ginac_glue::valueFor(E))
      if (auto B = Bounds(V))
        return {B->first, B->second};
    return {};
  }
  if (is_a<add>(E)) {
    NumInterval R = point(0);
    for (size_t I = 0; I < E.nops(); ++I)
      R = addIv(R, evalEx(E.op(I), Bounds));
    return R;
  }
  if (is_a<mul>(E)) {
    NumInterval R = point(1);
    for (size_t I = 0; I < E.nops(); ++I)
      R = mulIv(R, evalEx(E.op(I), Bounds));
    return R;
  }
  if (is_a<power>(E) && is_exactly_a<numeric>(E.op(1))) {
    const numeric &K = ex_to<numeric>(E.op(1));
    if (K.is_pos_integer() && K <= 16) {
      NumInterval Base = evalEx(E.op(0), Bounds), R = point(1);
      for (long I = 0; I < K.to_long(); ++I)
        R = mulIv(R, Base);
      return R;
    }
    return {};
  }
  if (is_a<function>(E) &&
      ex_to<function>(E).get_serial() == ginac_glue::idiv_SERIAL::serial &&
      is_exactly_a<numeric>(E.op(1))) {
    const numeric &D = ex_to<numeric>(E.op(1));
    if (D.is_zero() || !D.is_integer())
      return {};
    NumInterval N = evalEx(E.op(0), Bounds);
    // Truncating division by a constant is monotone; floor the rational
    // bounds first so iquo sees integers.
    auto Q = [&](const numeric &X) { return iquo(X.is_integer() ? X : numeric(0), D); };
    if (N.Lo && !N.Lo->is_integer())
      N.Lo.reset();
    if (N.Hi && !N.Hi->is_integer())
      N.Hi.reset();
    NumInterval R;
    if (D.is_positive()) {
      if (N.Lo)
        R.Lo = Q(*N.Lo);
      if (N.Hi)
        R.Hi = Q(*N.Hi);
    } else {
      if (N.Hi)
        R.Lo = Q(*N.Hi);
      if (N.Lo)
        R.Hi = Q(*N.Lo);
    }
    return R;
  }
  return {};
}

SymExpr SymExpr::resolve(const SymExpr &E, bool Upper,
                         llvm::function_ref<bool(llvm::Value *)> Drop,
                         SymbolBoundsFn Bounds) {
  SymExpr Unbounded = Upper ? inf() : negInf();
  switch (E.K) {
  case PosInf:
  case NegInf:
    return E;
  case Top:
    return Unbounded;
  case Min:
  case Max: {
    // min and max are monotone in each argument, so a bound of every argument
    // gives a bound of the whole.
    std::optional<SymExpr> R;
    for (const SymExpr &A : E.args()) {
      SymExpr X = resolve(A, Upper, Drop, Bounds);
      R = !R ? X : E.K == Min ? mkMin(*R, X) : mkMax(*R, X);
    }
    return R ? *R : Unbounded;
  }
  case Poly:
    break;
  }

  std::vector<symbol> Dropped;
  for (auto It = E.P.preorder_begin(); It != E.P.preorder_end(); ++It)
    if (is_a<symbol>(*It))
      if (llvm::Value *V = ginac_glue::valueFor(*It); V && Drop(V)) {
        const symbol &S = ex_to<symbol>(*It);
        if (std::none_of(Dropped.begin(), Dropped.end(),
                         [&](const symbol &D) { return D.is_equal(S); }))
          Dropped.push_back(S);
      }
  if (Dropped.empty())
    return E;

  // Linear occurrences: E = C*s + Rest, with s absent from Rest.
  ex P = E.P;
  for (const symbol &S : Dropped) {
    ex C = P.coeff(S, 1);
    if (!is_exactly_a<numeric>(C) || ex_to<numeric>(C).is_zero())
      continue;
    ex Rest = (P - C * S).expand();
    if (Rest.has(S))
      continue;
    auto B = Bounds(ginac_glue::valueFor(S));
    if (!B)
      return Unbounded;
    bool UseHi = Upper == ex_to<numeric>(C).is_positive();
    P = (Rest + C * (UseHi ? B->second : B->first)).expand();
  }
  if (std::none_of(Dropped.begin(), Dropped.end(),
                   [&](const symbol &S) { return P.has(S); }))
    return fromPoly(P);

  // Any other occurrence (products, idiv) is evaluated numerically.
  NumInterval I = evaluate(fromPoly(P), Bounds);
  std::optional<numeric> N = Upper ? I.Hi : I.Lo;
  return N ? fromPoly(*N) : Unbounded;
}

NumInterval evaluate(const SymExpr &E, SymbolBoundsFn Bounds) {
  switch (E.kind()) {
  case SymExpr::Poly:
    return evalEx(E.poly(), Bounds);
  case SymExpr::Min:
  case SymExpr::Max: {
    bool IsMin = E.kind() == SymExpr::Min;
    // The lower bound of a min needs the lower bound of every argument; its
    // upper bound needs the upper bound of any one. Max is symmetric.
    std::optional<numeric> Lo, Hi;
    bool AllLo = true, AllHi = true;
    for (const SymExpr &X : E.args()) {
      NumInterval I = evaluate(X, Bounds);
      if (IsMin) {
        if (!I.Lo)
          AllLo = false;
        else if (!Lo || *I.Lo < *Lo)
          Lo = I.Lo;
        if (I.Hi && (!Hi || *I.Hi < *Hi))
          Hi = I.Hi;
      } else {
        if (!I.Hi)
          AllHi = false;
        else if (!Hi || *I.Hi > *Hi)
          Hi = I.Hi;
        if (I.Lo && (!Lo || *I.Lo > *Lo))
          Lo = I.Lo;
      }
    }
    if (!AllLo)
      Lo.reset();
    if (!AllHi)
      Hi.reset();
    return {Lo, Hi};
  }
  default:
    return {};
  }
}

} // namespace symboxes
