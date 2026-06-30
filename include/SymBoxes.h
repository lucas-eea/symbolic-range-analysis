//===- SymBoxes.h - Symbolic interval domain --------------------*- C++ -*-===//
//
/// \file
/// Defines SymExpr, a symbolic expression tree over integer constants and
/// LLVM Values, and SymRange, a symbolic interval [Lower, Upper] used as the
/// abstract domain for range analysis.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SYMBOXES_H
#define LLVM_SYMBOXES_H

#include "GiNaCGlue.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cstdint>
#include <memory>

namespace symboxes {

/// A node in a symbolic expression tree.
///
/// Leaves are integer constants (Const) or LLVM Values (Sym).
/// Interior nodes are arithmetic (Add, Sub, Mul, Div) or lattice
/// (Min, Max) operations.  PosInf and NegInf represent ±∞.
struct SymExpr {
  enum Production {
    Const,
    Sym,
    Add,
    Sub,
    Mul,
    Div,
    Min,
    Max,
    PosInf,
    NegInf,
  };

  Production P = Const;
  int64_t C = 0;
  llvm::Value *V = nullptr;
  std::shared_ptr<SymExpr> L, R;

  static SymExpr inf() {
    SymExpr E;
    E.P = PosInf;
    return E;
  }

  static SymExpr negInf() {
    SymExpr E;
    E.P = NegInf;
    return E;
  }

  static SymExpr num(int64_t C) {
    SymExpr E;
    E.P = Const;
    E.C = C;
    return E;
  }

  static SymExpr sym(llvm::Value *V) {
    SymExpr E;
    E.P = Sym;
    E.V = V;
    return E;
  }

  static SymExpr add(const SymExpr &A, const SymExpr &B) {
    if (A.P == NegInf || B.P == NegInf)
      return negInf();
    if (A.P == PosInf || B.P == PosInf)
      return inf();
    if (A.P == Const && B.P == Const)
      return num(A.C + B.C);
    if (A.P == Const && A.C == 0)
      return B;
    if (B.P == Const && B.C == 0)
      return A;
    SymExpr R;
    R.P = Add;
    R.L = std::make_shared<SymExpr>(A);
    R.R = std::make_shared<SymExpr>(B);
    return R;
  }

  static SymExpr sub(const SymExpr &A, const SymExpr &B) {
    if (A.P == NegInf || B.P == PosInf)
      return negInf();
    if (A.P == PosInf || B.P == NegInf)
      return inf();
    if (A.P == Const && B.P == Const)
      return num(A.C - B.C);
    if (B.P == Const && B.C == 0)
      return A;
    SymExpr R;
    R.P = Sub;
    R.L = std::make_shared<SymExpr>(A);
    R.R = std::make_shared<SymExpr>(B);
    return R;
  }

  static SymExpr mul(const SymExpr &A, const SymExpr &B) {
    if (A.P == Const && A.C == 0)
      return num(0);
    if (B.P == Const && B.C == 0)
      return num(0);
    if (A.P == Const && A.C == 1)
      return B;
    if (B.P == Const && B.C == 1)
      return A;
    if (A.P == Const && B.P == Const)
      return num(A.C * B.C);
    SymExpr R;
    R.P = Mul;
    R.L = std::make_shared<SymExpr>(A);
    R.R = std::make_shared<SymExpr>(B);
    return R;
  }

  /// Symbolic division.  Division by zero returns 0 rather than bottom so
  /// that unreachable paths do not poison downstream ranges.
  static SymExpr div(const SymExpr &A, const SymExpr &B) {
    if (B.P == Const && B.C == 0)
      return num(0);
    if (A.P == Const && B.P == Const)
      return num(A.C / B.C);
    if (B.P == Const && B.C == 1)
      return A;
    if (A.P == PosInf)
      return (B.P == Const && B.C < 0) ? negInf() : inf();
    if (A.P == NegInf)
      return (B.P == Const && B.C < 0) ? inf() : negInf();
    SymExpr R;
    R.P = Div;
    R.L = std::make_shared<SymExpr>(A);
    R.R = std::make_shared<SymExpr>(B);
    return R;
  }

  /// Returns min(A, B), with the simplification that when one argument is a
  /// concrete constant and the other is a pure symbol, the constant is
  /// returned.  This is a sound over-approximation when used as an upper
  /// bound: const ≥ min(const, sym) always, so the interval only widens.
  static SymExpr mkMin(const SymExpr &A, const SymExpr &B) {
    if (A.P == PosInf)
      return B;
    if (B.P == PosInf)
      return A;
    if (A.P == NegInf || B.P == NegInf)
      return negInf();
    if (A.P == Const && B.P == Const)
      return num(std::min(A.C, B.C));
    if (A.P == Const && B.P == Sym)
      return A;
    if (A.P == Sym && B.P == Const)
      return B;
    SymExpr R;
    R.P = Min;
    R.L = std::make_shared<SymExpr>(A);
    R.R = std::make_shared<SymExpr>(B);
    return R;
  }

  /// Returns max(A, B), with the same const-vs-sym simplification as mkMin.
  /// When used as a lower bound, returning the constant is sound: the interval
  /// only widens since const ≤ max(const, sym) always.
  static SymExpr mkMax(const SymExpr &A, const SymExpr &B) {
    if (A.P == NegInf)
      return B;
    if (B.P == NegInf)
      return A;
    if (A.P == PosInf || B.P == PosInf)
      return inf();
    if (A.P == Const && B.P == Const)
      return num(std::max(A.C, B.C));
    if (A.P == Const && B.P == Sym)
      return A;
    if (A.P == Sym && B.P == Const)
      return B;
    SymExpr R;
    R.P = Max;
    R.L = std::make_shared<SymExpr>(A);
    R.R = std::make_shared<SymExpr>(B);
    return R;
  }

  /// Structural equality, backed by GiNaC polynomial normalization for
  /// expressions that cannot be compared syntactically (e.g. (b+1)-1 vs b).
  bool operator==(const SymExpr &O) const {
    if (P == Const && O.P == Const)
      return C == O.C;
    if (P == Sym && O.P == Sym)
      return V == O.V;
    if (P == PosInf && O.P == PosInf)
      return true;
    if (P == NegInf && O.P == NegInf)
      return true;
    std::unordered_map<llvm::Value *, GiNaC::symbol> Syms;
    GiNaC::ex Lhs = ginac_glue::toGiNaC(*this, Syms);
    GiNaC::ex Rhs = ginac_glue::toGiNaC(O, Syms);
    return GiNaC::expand(Lhs - Rhs).is_zero();
  }

  bool operator!=(const SymExpr &O) const { return !(*this == O); }

  void print(llvm::raw_ostream &OS) const {
    switch (P) {
    case Const:
      OS << C;
      break;
    case Sym:
      OS << (V ? V->getName() : llvm::StringRef("?"));
      break;
    case PosInf:
      OS << "+∞";
      break;
    case NegInf:
      OS << "-∞";
      break;
    case Add:
      OS << "(";
      L->print(OS);
      OS << " + ";
      R->print(OS);
      OS << ")";
      break;
    case Sub:
      OS << "(";
      L->print(OS);
      OS << " - ";
      R->print(OS);
      OS << ")";
      break;
    case Mul:
      OS << "(";
      L->print(OS);
      OS << " * ";
      R->print(OS);
      OS << ")";
      break;
    case Div:
      OS << "(";
      L->print(OS);
      OS << " / ";
      R->print(OS);
      OS << ")";
      break;
    case Min:
      OS << "min(";
      L->print(OS);
      OS << ", ";
      R->print(OS);
      OS << ")";
      break;
    case Max:
      OS << "max(";
      L->print(OS);
      OS << ", ";
      R->print(OS);
      OS << ")";
      break;
    }
  }
};

/// A symbolic interval [Lower, Upper] over SymExpr.
///
/// \c isBottom marks the bottom element of the lattice (empty / unreachable).
/// The top element is [-∞, +∞] with \c isBottom == false.
struct SymRange {
  SymExpr Lower, Upper;
  /// True iff this is the bottom element (no possible value).
  bool isBottom = true;

  static SymRange bottom() {
    SymRange R;
    R.Lower = SymExpr::negInf();
    R.Upper = SymExpr::inf();
    R.isBottom = true;
    return R;
  }

  static SymRange full() { return {SymExpr::negInf(), SymExpr::inf(), false}; }

  static SymRange single(SymExpr E) { return {E, E, false}; }

  static SymRange of(SymExpr Lo, SymExpr Hi) { return {Lo, Hi, false}; }

  /// Lattice join: returns the smallest interval containing both \c *this and
  /// \p O.
  SymRange join(const SymRange &O) const {
    if (isBottom)
      return O;
    if (O.isBottom)
      return *this;
    return of(SymExpr::mkMin(Lower, O.Lower), SymExpr::mkMax(Upper, O.Upper));
  }

  /// Widening operator: bounds that did not stabilize between \c *this and
  /// \p Next are replaced by ±∞ to force convergence.
  SymRange widen(const SymRange &Next) const {
    if (isBottom)
      return Next;
    if (Next.isBottom)
      return *this;
    SymExpr Lo = (Lower == Next.Lower) ? Lower : SymExpr::negInf();
    SymExpr Hi = (Upper == Next.Upper) ? Upper : SymExpr::inf();
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
