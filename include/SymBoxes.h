//===- SymBoxes.h - Symbolic interval domain --------------------*- C++ -*-===//
//
/// \file
/// Defines SymExpr, a symbolic expression over integer constants and LLVM
/// Values, and SymRange, a symbolic interval [Lower, Upper] used as the
/// abstract domain for range analysis.
///
/// Expressions are kept in a canonical form, simplified on every operation:
///  - arithmetic lives in GiNaC polynomials, expanded (so (b+1)-1 is b);
///    integer division by a constant is the GiNaC function idiv;
///  - min and max are n-ary, flattened (min(min(a,b),c) = min(a,b,c)), with
///    arithmetic pushed inside (min(a,b)+c = min(a+c,b+c)), arguments that
///    are provably dominated removed (min(a, a+1) = a) and the rest sorted;
///  - an expression that grows beyond the size limits becomes Top (unknown),
///    which a range turns into -inf as a lower bound and +inf as an upper one.
/// Canonical forms make equality structural and cheap.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SYMBOXES_H
#define LLVM_SYMBOXES_H

#include "GiNaCGlue.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

namespace symboxes {

/// Memoizes GiNaC sums and differences. The results are the same either way.
extern bool UseMemo;

/// A symbolic expression: a polynomial over LLVM values, an n-ary min or max
/// of expressions, +inf, -inf, or Top (unknown).
class SymExpr {
public:
  enum Kind { Poly, Min, Max, PosInf, NegInf, Top };

  /// Constants are signed integers of at most this many bits. Arithmetic
  /// whose constant result does not fit saturates to -inf or +inf.
  static constexpr unsigned Width = 128;
  /// A min/max with more arguments than this becomes Top.
  static unsigned MaxArgs;
  /// An expression with more nodes than this becomes Top.
  static unsigned MaxNodes;

  SymExpr() : K(Poly), P(0) {}

  static SymExpr num(int64_t C);
  /// \p C is interpreted as signed and must be at most \c Width bits wide.
  static SymExpr num(const llvm::APInt &C);
  static SymExpr sym(llvm::Value *V);
  static SymExpr inf() { return SymExpr(PosInf); }
  static SymExpr negInf() { return SymExpr(NegInf); }
  static SymExpr top() { return SymExpr(Top); }

  static SymExpr add(const SymExpr &A, const SymExpr &B);
  static SymExpr sub(const SymExpr &A, const SymExpr &B);
  static SymExpr neg(const SymExpr &A);
  static SymExpr mul(const SymExpr &A, const SymExpr &B);
  /// Integer division, truncating toward zero. Division by zero yields 0, so
  /// that unreachable paths do not poison downstream ranges.
  static SymExpr div(const SymExpr &A, const SymExpr &B);
  static SymExpr mkMin(const SymExpr &A, const SymExpr &B);
  static SymExpr mkMax(const SymExpr &A, const SymExpr &B);

  Kind kind() const { return K; }
  bool isConst() const;
  /// Returns the value of a constant (see isConst()) as a Width-bit APInt.
  llvm::APInt constVal() const;
  bool isInf() const { return K == PosInf || K == NegInf; }
  const GiNaC::ex &poly() const { return P; }
  const std::vector<SymExpr> &args() const;
  /// Returns the number of nodes; a polynomial counts as one.
  unsigned size() const { return Nodes; }

  /// Returns true if \p A <= \p B holds for every value of the symbols. The
  /// check is sound but incomplete.
  static bool provablyLE(const SymExpr &A, const SymExpr &B);

  /// Returns a bound of \p E (upper if \p Upper, else lower) that does not
  /// mention the symbols selected by \p Drop and holds for every value they
  /// take within their numeric \p Bounds. A dropped symbol with a constant
  /// coefficient is replaced by its bound in the right direction, min and max
  /// are resolved argument by argument, and any other use makes the bound
  /// numeric. Unknown bounds give -inf or +inf.
  static SymExpr
  resolve(const SymExpr &E, bool Upper,
          llvm::function_ref<bool(llvm::Value *)> Drop,
          llvm::function_ref<std::optional<
              std::pair<GiNaC::numeric, GiNaC::numeric>>(llvm::Value *)>
              Bounds);

  bool operator==(const SymExpr &O) const;
  bool operator!=(const SymExpr &O) const { return !(*this == O); }
  /// Orders canonical expressions totally; used to sort min/max arguments.
  static int compare(const SymExpr &A, const SymExpr &B);

  void print(llvm::raw_ostream &OS) const;

private:
  explicit SymExpr(Kind K) : K(K), P(0) {}
  static SymExpr fromPoly(const GiNaC::ex &E);
  static SymExpr minMax(Kind K, std::vector<SymExpr> In);
  static SymExpr scale(const SymExpr &E, const GiNaC::numeric &C);

  Kind K;
  GiNaC::ex P; ///< Poly: an expanded polynomial with integer coefficients.
  std::shared_ptr<const std::vector<SymExpr>> Args; ///< Min/Max: sorted.
  unsigned Nodes = 1;
};

/// A numeric interval; an absent bound is unbounded.
struct NumInterval {
  std::optional<GiNaC::numeric> Lo, Hi;
};

/// Returns the numeric bounds of a symbol, or std::nullopt if unknown.
using SymbolBoundsFn = llvm::function_ref<
    std::optional<std::pair<GiNaC::numeric, GiNaC::numeric>>(llvm::Value *)>;

/// Evaluates \p E by interval arithmetic, each symbol ranging over the bounds
/// given by \p Bounds.
NumInterval evaluate(const SymExpr &E, SymbolBoundsFn Bounds);

/// Sets the numeric bounds of the symbols where expressions are being built,
/// such as n >= 1 inside `if (n > 0)`. When set, SymExpr::provablyLE falls
/// back to checking B - A >= 0 numerically under these bounds. Null means no
/// bounds.
void setContextBounds(const std::function<
    std::optional<std::pair<GiNaC::numeric, GiNaC::numeric>>(llvm::Value *)> *F);

/// Symbolic bounds (lower, upper) of a symbol in terms of other symbols,
/// such as i <= n - 1 for a parameter i that every call passes below n.
using SymFacts = std::pair<std::optional<SymExpr>, std::optional<SymExpr>>;
/// Sets the symbolic bounds SymExpr::provablyLE may use: s + c <= B follows
/// from upper(s) + c <= B. Null means no bounds.
void setSymbolicFacts(const std::function<SymFacts(llvm::Value *)> *F);

/// A symbolic interval [Lower, Upper] over SymExpr.
///
/// \c isBottom marks the bottom element of the lattice (no value, or
/// unreachable). The top element is [-inf, +inf].
struct SymRange {
  SymExpr Lower, Upper;
  /// True if this is the bottom element.
  bool isBottom = true;

  static SymRange bottom() {
    SymRange R;
    R.Lower = SymExpr::negInf();
    R.Upper = SymExpr::inf();
    R.isBottom = true;
    return R;
  }

  static SymRange full() { return of(SymExpr::negInf(), SymExpr::inf()); }

  static SymRange single(const SymExpr &E) { return of(E, E); }

  /// Returns [\p Lo, \p Hi]. A Top lower bound becomes -inf and a Top upper
  /// bound +inf.
  static SymRange of(SymExpr Lo, SymExpr Hi) {
    SymRange R;
    R.Lower = Lo.kind() == SymExpr::Top ? SymExpr::negInf() : std::move(Lo);
    R.Upper = Hi.kind() == SymExpr::Top ? SymExpr::inf() : std::move(Hi);
    R.isBottom = false;
    return R;
  }

  bool isFull() const {
    return !isBottom && Lower.kind() == SymExpr::NegInf &&
           Upper.kind() == SymExpr::PosInf;
  }

  /// Returns the smallest interval that contains both intervals.
  SymRange join(const SymRange &O) const {
    if (isBottom)
      return O;
    if (O.isBottom)
      return *this;
    return of(SymExpr::mkMin(Lower, O.Lower), SymExpr::mkMax(Upper, O.Upper));
  }

  /// Widens \c *this with \p Next: each bound that changed becomes -inf or
  /// +inf.
  SymRange widen(const SymRange &Next) const {
    if (isBottom)
      return Next;
    if (Next.isBottom)
      return *this;
    SymExpr Lo = (Lower == Next.Lower) ? Lower : SymExpr::negInf();
    SymExpr Hi = (Upper == Next.Upper) ? Upper : SymExpr::inf();
    return of(Lo, Hi);
  }

  /// Narrows \c *this with \p Next, a sound re-evaluation: each bound is
  /// replaced by the bound of \p Next if that one is provably tighter, which
  /// recovers the infinite bounds introduced by widening. The caller limits
  /// the number of narrowing rounds.
  SymRange narrow(const SymRange &Next) const {
    if (isBottom || Next.isBottom)
      return *this;
    SymExpr Lo = SymExpr::provablyLE(Lower, Next.Lower) ? Next.Lower : Lower;
    SymExpr Hi = SymExpr::provablyLE(Next.Upper, Upper) ? Next.Upper : Upper;
    return of(Lo, Hi);
  }

  bool operator==(const SymRange &O) const {
    return ginac_glue::equals(*this, O);
  }

  void print(llvm::raw_ostream &OS) const {
    if (isBottom) {
      OS << "∅";
      return;
    }
    OS << "[";
    Lower.print(OS);
    OS << ", ";
    Upper.print(OS);
    OS << "]";
  }
};

} // namespace symboxes

#endif // LLVM_SYMBOXES_H
