#include "GiNaCGlue.h"
#include "SymBoxes.h"

GiNaC::ex normalize(const GiNaC::ex &e) {
  return e.expand().normal();
}

bool ginac_glue::equals(const symboxes::SymRange &a, const symboxes::SymRange &b) {
    if (a.isBottom && b.isBottom) return true;
    if (a.isBottom != b.isBottom) return false;
    return a.Lower == b.Lower && a.Upper == b.Upper;
}

GiNaC::ex ginac_glue::toGiNaC(const symboxes::SymExpr &e,
    std::unordered_map<llvm::Value*, GiNaC::symbol> &syms)
{
    switch (e.P) {
    case symboxes::SymExpr::Const:  return GiNaC::numeric(e.C);
    case symboxes::SymExpr::Sym: {
        auto [it, inserted] = syms.emplace(e.V, GiNaC::symbol());
        return it->second;
    }
    case symboxes::SymExpr::Add: return toGiNaC(*e.L, syms) + toGiNaC(*e.R, syms);
    case symboxes::SymExpr::Sub: return toGiNaC(*e.L, syms) - toGiNaC(*e.R, syms);
    case symboxes::SymExpr::Mul: return toGiNaC(*e.L, syms) * toGiNaC(*e.R, syms);
    default: return GiNaC::numeric(0);
    }
}

