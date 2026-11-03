//===- ExactValues.h - Exact symbolic values of SSA integers ----*- C++ -*-===//
//
/// \file
/// Declares ExactValues, a sparse analysis that gives every integer SSA
/// value an exact symbolic value: a GiNaC polynomial over the symbols of
/// other SSA values, or the value's own symbol. It complements the intervals
/// of SymbolicRangeAnalysis with linear equalities between variables, such
/// as j == 3 * i after a loop that adds 1 to i and 3 to j:
///
///  - arithmetic that cannot wrap (nsw) is computed exactly;
///  - joins: if Q - a * R is the same on every incoming edge of two phis Q
///    and R of a block, with a a number, then Q = a * R + (Q - a * R);
///  - loop counters: if the change of a header phi Pj over an iteration is
///    always a times the change of the primary counter P0, with a a number,
///    then Pj = start_j + a * (P0 - start_0);
///  - exit values: leaving for (i = s; i < b; ++i) at its test, i is
///    max(s, b), and min(s, b) when counting down. Comparisons of values
///    with max/min are decided by splitting on which argument is larger and
///    keeping the feasible cases (Fourier-Motzkin).
///
/// A comparison whose operands differ by a number is decided.
///
/// Values are signed and arithmetic is over the integers, which is exact for
/// operations that cannot wrap; an nsw operation that wraps is poison.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_EXACT_VALUES_H
#define LLVM_EXACT_VALUES_H

#include <ginac/ginac.h>
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <functional>
#include <optional>

namespace llvm {
class BasicBlock;
class DominatorTree;
class Function;
class ICmpInst;
class LoopInfo;
class PHINode;
class Value;
} // namespace llvm

namespace exactvalues {

/// The exact values of the integers of one function.
class ExactValues {
public:
  /// Computes the exact values of \p F. \p NonNeg returns true for a value
  /// the interval analysis proves non-negative, which zero extensions and
  /// unsigned comparisons need.
  ExactValues(llvm::Function &F, llvm::LoopInfo &LI, llvm::DominatorTree &DT,
              std::function<bool(llvm::Value *)> NonNeg);

  /// Returns the value of \p Cmp wherever it is evaluated, if its operands
  /// differ by a number.
  std::optional<bool> decide(llvm::ICmpInst &Cmp);

  /// Returns the exact value of \p V, or its own symbol.
  GiNaC::ex get(llvm::Value *V);

private:
  /// Evaluates the whole function once, with the current loop facts
  /// (Counters and Exits).
  void evaluate();
  /// Returns the exact value of the instruction \p V from its operands.
  GiNaC::ex transfer(llvm::Value *V);
  /// Computes the values of the phis of \p BB, a block that is not a loop
  /// header: an equal incoming value, or a relation to another phi.
  void joinBlock(llvm::BasicBlock *BB);
  /// Derives the loop facts from the current values. Returns true if they
  /// changed.
  bool deriveLoopFacts();

  llvm::Function &F;
  llvm::LoopInfo &LI;
  llvm::DominatorTree &DT;
  std::function<bool(llvm::Value *)> NonNeg;
  llvm::DenseMap<llvm::Value *, GiNaC::ex> Val;
  /// Loop header phis related to their loop's primary counter, or constant.
  llvm::DenseMap<llvm::PHINode *, GiNaC::ex> Counters;
  /// The value of a loop counter on the edge that leaves its loop at the
  /// header test, max or min of start and bound, keyed by the counter's sigma
  /// node on that edge.
  struct ExitFact {
    llvm::PHINode *Counter;
    GiNaC::ex Value;
  };
  llvm::DenseMap<llvm::PHINode *, ExitFact> Exits;
};

} // namespace exactvalues

#endif // LLVM_EXACT_VALUES_H
