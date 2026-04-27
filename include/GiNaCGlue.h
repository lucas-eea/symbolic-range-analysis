#pragma once

#include <ginac/ginac.h>
#include <unordered_map>

namespace llvm {
    class Value;
}

namespace symboxes {
    class SymExpr;
    class SymRange;
}

namespace ginac_glue{

GiNaC::ex toGiNaC(const symboxes::SymExpr &e,
                  std::unordered_map<llvm::Value*, GiNaC::symbol> &symMap);

GiNaC::ex normalize(const GiNaC::ex &e);

bool equals(const symboxes::SymRange &a, const symboxes::SymRange &b);

}
