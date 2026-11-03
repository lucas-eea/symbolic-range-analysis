//===- GiNaCGlue.h - GiNaC bridge for symbolic expressions ------*- C++ -*-===//
//
/// \file
/// Bridges LLVM values and constants to GiNaC: a persistent map from LLVM
/// Values to GiNaC symbols, conversions between APInt and GiNaC numbers, and
/// the `idiv` GiNaC function, which represents C (truncating) integer division
/// inside polynomials.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_GINAC_GLUE_H
#define LLVM_GINAC_GLUE_H

#include "llvm/ADT/APInt.h"
#include <ginac/ginac.h>
#include <optional>

namespace llvm {
class raw_ostream;
class Value;
} // namespace llvm

namespace symboxes {
class SymExpr;
struct SymRange;
} // namespace symboxes

namespace ginac_glue {

/// idiv(n, d): integer division truncating toward zero, as in C. Evaluates
/// when both operands are numbers, or when every coefficient of n is
/// divisible by the number d; otherwise it stays an opaque term.
DECLARE_FUNCTION_2P(idiv)

/// Returns the GiNaC symbol that stands for \p V. The same Value always maps
/// to the same symbol, so polynomials over it can be compared and cancelled.
const GiNaC::symbol &symbolFor(llvm::Value *V);

/// Forgets every symbol. Symbols never cross functions, so the analysis
/// resets them per function; a Value's address may be reused afterwards.
void resetSymbols();

/// Returns the Value a symbol stands for, or null if \p S is not one.
llvm::Value *valueFor(const GiNaC::ex &S);

/// Converts a signed APInt to a GiNaC integer.
GiNaC::numeric toNumeric(const llvm::APInt &C);

/// Converts an integer to a signed APInt of \p Width bits, if it fits.
std::optional<llvm::APInt> toAPInt(const GiNaC::numeric &N, unsigned Width);

/// Prints \p E; the same as E.print(OS).
void print(const symboxes::SymExpr &E, llvm::raw_ostream &OS);

/// Returns true if \p A and \p B represent the same symbolic range.
bool equals(const symboxes::SymRange &A, const symboxes::SymRange &B);

} // namespace ginac_glue

#endif // LLVM_GINAC_GLUE_H
