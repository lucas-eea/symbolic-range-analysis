//===- GiNaCGlue.cpp - GiNaC bridge for symbolic expressions --------------===//
//
/// \file
/// Implements the bridge between LLVM values and GiNaC declared in
/// GiNaCGlue.h.
//
//===----------------------------------------------------------------------===//

#include "GiNaCGlue.h"
#include "SymBoxes.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <sstream>
#include <unordered_map>

using namespace GiNaC;

namespace ginac_glue {

/// Evaluates idiv(\p N, \p D) when the result is exact, otherwise keeps it
/// as an opaque term.
static ex idiv_eval(const ex &N, const ex &D) {
  if (!is_exactly_a<numeric>(D))
    return idiv(N, D).hold();
  const numeric &Den = ex_to<numeric>(D);
  if (Den.is_zero())
    return idiv(N, D).hold();
  if (Den.is_equal(numeric(1)))
    return N;
  if (is_exactly_a<numeric>(N) && ex_to<numeric>(N).is_integer() &&
      Den.is_integer())
    return iquo(ex_to<numeric>(N), Den);
  // If every coefficient is divisible by D, N / D is an integer for every
  // integer value of the symbols, so truncation does nothing.
  try {
    numeric Content = N.expand().integer_content();
    if (Content.is_integer() && Den.is_integer() &&
        irem(Content, Den).is_zero())
      return (N / D).expand();
  } catch (const std::exception &) {
    // GiNaC cannot take the content of N: keep the term opaque.
  }
  return idiv(N, D).hold();
}

REGISTER_FUNCTION(idiv, eval_func(idiv_eval))

namespace {
/// The symbols of the LLVM values seen since the last resetSymbols().
struct Registry {
  std::unordered_map<llvm::Value *, symbol> Symbols;
  std::map<ex, llvm::Value *, ex_is_less> Values;
  unsigned Unnamed = 0;
};
Registry &registry() {
  static Registry R;
  return R;
}
} // namespace

void resetSymbols() {
  Registry &R = registry();
  R.Symbols.clear();
  R.Values.clear();
  R.Unnamed = 0;
}

const symbol &symbolFor(llvm::Value *V) {
  Registry &R = registry();
  auto It = R.Symbols.find(V);
  // A different name means that another Value reused the address.
  if (It != R.Symbols.end() &&
      (!V || !V->hasName() || It->second.get_name() == V->getName()))
    return It->second;
  if (It != R.Symbols.end()) {
    R.Values.erase(It->second);
    R.Symbols.erase(It);
  }
  std::string Name = V && V->hasName() ? V->getName().str()
                                       : "v" + std::to_string(R.Unnamed++);
  symbol S(Name);
  R.Values.emplace(S, V);
  return R.Symbols.emplace(V, S).first->second;
}

llvm::Value *valueFor(const ex &S) {
  Registry &R = registry();
  auto It = R.Values.find(S);
  return It == R.Values.end() ? nullptr : It->second;
}

numeric toNumeric(const llvm::APInt &C) {
  if (C.isSignedIntN(64))
    return numeric(static_cast<long>(C.getSExtValue()));
  return numeric(llvm::toString(C, 10, /*Signed=*/true).c_str());
}

std::optional<llvm::APInt> toAPInt(const numeric &N, unsigned Width) {
  if (!N.is_integer())
    return std::nullopt;
  numeric Max = pow(numeric(2), numeric(Width - 1)) - 1;
  if (N > Max || N < -Max - 1)
    return std::nullopt;
  std::ostringstream SS;
  SS << N;
  return llvm::APInt(Width, SS.str(), 10);
}

void print(const symboxes::SymExpr &E, llvm::raw_ostream &OS) { E.print(OS); }

bool equals(const symboxes::SymRange &A, const symboxes::SymRange &B) {
  if (A.isBottom || B.isBottom)
    return A.isBottom == B.isBottom;
  return A.Lower == B.Lower && A.Upper == B.Upper;
}

} // namespace ginac_glue
