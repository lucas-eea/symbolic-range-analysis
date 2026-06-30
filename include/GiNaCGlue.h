//===- GiNaCGlue.h - GiNaC bridge for symbolic expressions ------*- C++ -*-===//
//
/// \file
/// Provides utilities for converting SymExpr trees to GiNaC expressions and
/// for comparing symbolic ranges using GiNaC's algebraic simplifier.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_GINAC_GLUE_H
#define LLVM_GINAC_GLUE_H

#include <ginac/ginac.h>
#include <unordered_map>

namespace llvm {
class raw_ostream;
} // namespace llvm

namespace llvm {
class Value;
} // namespace llvm

namespace symboxes {
class SymExpr;
class SymRange;
} // namespace symboxes

namespace ginac_glue {

/// Converts a SymExpr tree to a GiNaC expression.
/// \p Syms maps LLVM Values to GiNaC symbols; entries are created on demand.
GiNaC::ex toGiNaC(const symboxes::SymExpr &E,
                   std::unordered_map<llvm::Value *, GiNaC::symbol> &Syms);

/// Prints \p E to \p OS, using GiNaC's expand() to simplify arithmetic
/// sub-expressions. Min/Max/Inf nodes are printed structurally.
void print(const symboxes::SymExpr &E, llvm::raw_ostream &OS);

/// Returns true if \p A and \p B represent the same symbolic range.
/// Equality of bounds is decided by GiNaC algebraic simplification.
bool equals(const symboxes::SymRange &A, const symboxes::SymRange &B);

} // namespace ginac_glue

#endif // LLVM_GINAC_GLUE_H
