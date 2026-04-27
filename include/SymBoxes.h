#pragma once

#include "GiNaCGlue.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cstdint>
#include <memory>

namespace symboxes {
	
struct SymExpr{
  enum Production{
    Const,
    Sym,
    Add, Sub,
    Mul,
    Min, Max,
    PosInf, NegInf
  };

  Production P = Const;
  int64_t    C = 0;
  llvm::Value     *V = nullptr;
  std::shared_ptr<SymExpr> L, R;

  static SymExpr inf()    { SymExpr e; e.P = PosInf; return e; }
  static SymExpr negInf() { SymExpr e; e.P = NegInf; return e; }
  static SymExpr num(int64_t c) { SymExpr e; e.P = Const; e.C = c; return e; }
  static SymExpr sym(llvm::Value *v)  { SymExpr e; e.P = Sym;   e.V = v; return e; }

  static SymExpr add(const SymExpr &a, const SymExpr &b){
    if (a.P == NegInf || b.P == NegInf) return negInf();
    if (a.P == PosInf || b.P == PosInf) return inf();
    if (a.P == Const && b.P == Const)   return num(a.C + b.C);
    if (a.P == Const && a.C == 0)       return b;
    if (b.P == Const && b.C == 0)       return a;
    SymExpr r; r.P = Add;
    r.L = std::make_shared<SymExpr>(a);
    r.R = std::make_shared<SymExpr>(b);
    return r;
  }

  static SymExpr sub(const SymExpr &a, const SymExpr &b){
    if (a.P == NegInf || b.P == PosInf) return negInf();
    if (a.P == PosInf || b.P == NegInf) return inf();
    if (a.P == Const && b.P == Const)   return num(a.C - b.C);
    if (b.P == Const && b.C == 0)       return a;
    SymExpr r; r.P = Sub;
    r.L = std::make_shared<SymExpr>(a);
    r.R = std::make_shared<SymExpr>(b);
    return r;
  }

  static SymExpr mul(const SymExpr &a, const SymExpr &b){
    if (a.P == Const && a.C == 0) return num(0);
    if (b.P == Const && b.C == 0) return num(0);
    if (a.P == Const && a.C == 1) return b;
    if (b.P == Const && b.C == 1) return a;
    if (a.P == Const && b.P == Const) return num(a.C * b.C);
    SymExpr r; r.P = Mul;
    r.L = std::make_shared<SymExpr>(a);
    r.R = std::make_shared<SymExpr>(b);
    return r;
  }

  static SymExpr mkMin(const SymExpr &a, const SymExpr &b){
    if (a.P == PosInf) return b;
    if (b.P == PosInf) return a;
    if (a.P == NegInf || b.P == NegInf) return negInf();
    if (a.P == Const && b.P == Const)
      return num(std::min(a.C, b.C));
    SymExpr r; r.P = Min;
    r.L = std::make_shared<SymExpr>(a);
    r.R = std::make_shared<SymExpr>(b);
    return r;
  }

  static SymExpr mkMax(const SymExpr &a, const SymExpr &b){
    if (a.P == NegInf) return b;
    if (b.P == NegInf) return a;
    if (a.P == PosInf || b.P == PosInf) return inf();
    if (a.P == Const && b.P == Const)
      return num(std::max(a.C, b.C));
    SymExpr r; r.P = Max;
    r.L = std::make_shared<SymExpr>(a);
    r.R = std::make_shared<SymExpr>(b);
    return r;
  }
  
bool operator==(const SymExpr &o) const {
    if (P == Const && o.P == Const)   return C == o.C;
    if (P == Sym   && o.P == Sym)     return V == o.V;
    if (P == PosInf && o.P == PosInf) return true;
    if (P == NegInf && o.P == NegInf) return true;
    std::unordered_map<llvm::Value*, GiNaC::symbol> syms;
    GiNaC::ex lhs = ginac_glue::toGiNaC(*this, syms);
    GiNaC::ex rhs = ginac_glue::toGiNaC(o, syms);
    return GiNaC::expand(lhs - rhs).is_zero();
}

  bool operator!=(const SymExpr &o) const { return !(*this == o);}

  void print(llvm::raw_ostream &OS) const{
    switch (P) {
    case Const:  OS << C; break;
    case Sym:    OS << (V ? V->getName() : llvm::StringRef("?")); break;
    case PosInf: OS << "+∞"; break;
    case NegInf: OS << "-∞"; break;
    case Add: OS << "("; L->print(OS); OS << " + "; R->print(OS); OS << ")"; break;
    case Sub: OS << "("; L->print(OS); OS << " - "; R->print(OS); OS << ")"; break;
    case Mul: OS << "("; L->print(OS); OS << " * "; R->print(OS); OS << ")"; break;
    case Min: OS << "min("; L->print(OS); OS << ", "; R->print(OS); OS << ")"; break;
    case Max: OS << "max("; L->print(OS); OS << ", "; R->print(OS); OS << ")"; break;
    }
  }
};

struct SymRange{
  SymExpr Lower, Upper;
  bool    isBottom = true;

  static SymRange bottom(){
    SymRange r;
    r.Lower = SymExpr::negInf();
    r.Upper = SymExpr::inf();
    r.isBottom = true;
    return r;
  }

  static SymRange full() {
    return {SymExpr::negInf(), SymExpr::inf(), false};
  }

  static SymRange single(SymExpr e) { return {e, e, false}; }

  static SymRange of(SymExpr lo, SymExpr hi){return {lo, hi, false};}

  SymRange join(const SymRange &o) const{
    if (isBottom)   return o;
    if (o.isBottom) return *this;
    return of(SymExpr::mkMin(Lower, o.Lower),
              SymExpr::mkMax(Upper, o.Upper));
  }

  SymRange widen(const SymRange &next) const{
    if (isBottom)      return next;
    if (next.isBottom) return *this;
    SymExpr lo = (Lower == next.Lower) ? Lower : SymExpr::negInf();
    SymExpr hi = (Upper == next.Upper) ? Upper : SymExpr::inf();
    return of(lo, hi);
  }

  bool operator==(const SymRange &o) const{
    return ginac_glue::equals(*this, o);
  }


  void print(llvm::raw_ostream &OS) const{
    if (isBottom) { OS << "∅"; return;}
    OS << "["; Lower.print(OS); OS << ", "; Upper.print(OS); OS << "]";
  }
};
}

