//===- GiNaCGlue.cpp - GiNaC bridge for symbolic expressions --------------===//

#include "GiNaCGlue.h"
#include "SymBoxes.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

static GiNaC::ex normalize(const GiNaC::ex &E) { return E.expand().normal(); }

GiNaC::ex ginac_glue::toGiNaC(const symboxes::SymExpr &E,
                                std::unordered_map<llvm::Value *, GiNaC::symbol> &Syms) {
  switch (E.P) {
  case symboxes::SymExpr::Const:
    return GiNaC::numeric(E.C);
  case symboxes::SymExpr::Sym: {
    std::string Name = E.V ? E.V->getName().str() : "?";
    auto [It, Inserted] = Syms.emplace(E.V, GiNaC::symbol(Name));
    return It->second;
  }
  case symboxes::SymExpr::Add:
    return toGiNaC(*E.L, Syms) + toGiNaC(*E.R, Syms);
  case symboxes::SymExpr::Sub:
    return toGiNaC(*E.L, Syms) - toGiNaC(*E.R, Syms);
  case symboxes::SymExpr::Mul:
    return toGiNaC(*E.L, Syms) * toGiNaC(*E.R, Syms);
  case symboxes::SymExpr::Div:
    return toGiNaC(*E.L, Syms) / toGiNaC(*E.R, Syms);
  default:
    return GiNaC::numeric(0);
  }
}

void ginac_glue::print(const symboxes::SymExpr &E, llvm::raw_ostream &OS) {
  using symboxes::SymExpr;
  switch (E.P) {
  case SymExpr::PosInf: OS << "+∞"; return;
  case SymExpr::NegInf: OS << "-∞"; return;
  case SymExpr::Min:
    OS << "min("; print(*E.L, OS); OS << ", "; print(*E.R, OS); OS << ")"; return;
  case SymExpr::Max:
    OS << "max("; print(*E.L, OS); OS << ", "; print(*E.R, OS); OS << ")"; return;
  default: break;
  }
  std::unordered_map<llvm::Value *, GiNaC::symbol> Syms;
  std::ostringstream SS;
  SS << toGiNaC(E, Syms).expand();
  OS << SS.str();
}

bool ginac_glue::equals(const symboxes::SymRange &A,
                        const symboxes::SymRange &B) {
  if (A.isBottom && B.isBottom)
    return true;
  if (A.isBottom != B.isBottom)
    return false;
  return A.Lower == B.Lower && A.Upper == B.Upper;
}
