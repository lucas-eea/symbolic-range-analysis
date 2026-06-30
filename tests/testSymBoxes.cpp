#include "GiNaCGlue.h"
#include "SymBoxes.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/raw_ostream.h"

using namespace symboxes;

static bool pass(bool cond) { return cond; }

// ── SymExpr ──────────────────────────────────────────────────────────────────

static void testExprConstants() {
  llvm::outs() << "=== SymExpr: constants ===\n";
  auto z  = SymExpr::num(0);
  auto o  = SymExpr::num(1);
  auto n5 = SymExpr::num(5);

  llvm::outs() << "0 == 0: "  << (pass(z  == z)  ? "true" : "false") << "\n";
  llvm::outs() << "0 == 1: "  << (pass(z  == o)  ? "true" : "false") << "\n";
  llvm::outs() << "0 + 5 == 5: " << (pass(SymExpr::add(z, n5) == n5) ? "true" : "false") << "\n";
  llvm::outs() << "5 + 0 == 5: " << (pass(SymExpr::add(n5, z) == n5) ? "true" : "false") << "\n";
  llvm::outs() << "5 - 0 == 5: " << (pass(SymExpr::sub(n5, z) == n5) ? "true" : "false") << "\n";
  llvm::outs() << "5 - 5 == 0: " << (pass(SymExpr::sub(n5, n5) == z) ? "true" : "false") << "\n";
  llvm::outs() << "0 * 5 == 0: " << (pass(SymExpr::mul(z, n5) == z)  ? "true" : "false") << "\n";
  llvm::outs() << "1 * 5 == 5: " << (pass(SymExpr::mul(o, n5) == n5) ? "true" : "false") << "\n";
  llvm::outs() << "5 / 1 == 5: " << (pass(SymExpr::div(n5, o) == n5) ? "true" : "false") << "\n";
  llvm::outs() << "5 / 0 == 0: " << (pass(SymExpr::div(n5, z) == z)  ? "true" : "false") << "\n";
}

static void testExprInfinity() {
  llvm::outs() << "=== SymExpr: infinity ===\n";
  auto inf    = SymExpr::inf();
  auto negInf = SymExpr::negInf();
  auto one    = SymExpr::num(1);

  llvm::outs() << "+∞ + 1 == +∞: "    << ((SymExpr::add(inf, one)    == inf)    ? "true" : "false") << "\n";
  llvm::outs() << "-∞ - 1 == -∞: "    << ((SymExpr::sub(negInf, one) == negInf) ? "true" : "false") << "\n";
  llvm::outs() << "+∞ + (-∞): "       << (SymExpr::add(inf, negInf)  == negInf  ? "true" : "false") << "\n";
  llvm::outs() << "+∞ / -1 == -∞: "   << ((SymExpr::div(inf, SymExpr::num(-1)) == negInf) ? "true" : "false") << "\n";
  llvm::outs() << "-∞ / -1 == +∞: "   << ((SymExpr::div(negInf, SymExpr::num(-1)) == inf) ? "true" : "false") << "\n";
}

static void testExprEquality() {
  llvm::outs() << "=== SymExpr: equality ===\n";
  llvm::LLVMContext ctx;
  llvm::Type *i64 = llvm::Type::getInt64Ty(ctx);
  llvm::Argument V(i64, "V");
  llvm::Argument S(i64, "S");

  auto v = SymExpr::sym(&V);
  auto s = SymExpr::sym(&S);

  llvm::outs() << "v == v: "         << (pass(v == v)                                         ? "true" : "false") << "\n";
  llvm::outs() << "v == s: "         << (pass(v == s)                                         ? "true" : "false") << "\n";
  llvm::outs() << "v+s == s+v: "     << (pass(SymExpr::add(v,s) == SymExpr::add(s,v))        ? "true" : "false") << "\n";
  llvm::outs() << "v+s == v+v: "     << (pass(SymExpr::add(v,s) == SymExpr::add(v,v))        ? "true" : "false") << "\n";
  llvm::outs() << "v*s == s*v: "     << (pass(SymExpr::mul(v,s) == SymExpr::mul(s,v))        ? "true" : "false") << "\n";
  llvm::outs() << "(v+s)-s == v: "   << (pass(SymExpr::sub(SymExpr::add(v,s),s) == v)        ? "true" : "false") << "\n";
}

static void testExprDistributivity() {
  llvm::outs() << "=== SymExpr: distributivity ===\n";
  llvm::LLVMContext ctx;
  llvm::Type *i64 = llvm::Type::getInt64Ty(ctx);
  llvm::Argument A(i64, "A");
  llvm::Argument B(i64, "B");
  llvm::Argument C(i64, "C");

  auto a = SymExpr::sym(&A);
  auto b = SymExpr::sym(&B);
  auto c = SymExpr::sym(&C);

  // (a+b)*c == a*c + b*c
  auto lhs = SymExpr::mul(SymExpr::add(a, b), c);
  auto rhs = SymExpr::add(SymExpr::mul(a,c), SymExpr::mul(b,c));
  llvm::outs() << "(a+b)*c == a*c+b*c: " << (pass(lhs == rhs) ? "true" : "false") << "\n";

  // (a-b)*c == a*c - b*c
  auto lhs2 = SymExpr::mul(SymExpr::sub(a, b), c);
  auto rhs2 = SymExpr::sub(SymExpr::mul(a,c), SymExpr::mul(b,c));
  llvm::outs() << "(a-b)*c == a*c-b*c: " << (pass(lhs2 == rhs2) ? "true" : "false") << "\n";
}

static void testExprPrint() {
  llvm::outs() << "=== SymExpr: print ===\n";
  llvm::LLVMContext ctx;
  llvm::Type *i64 = llvm::Type::getInt64Ty(ctx);
  llvm::Argument X(i64, "x");

  auto x   = SymExpr::sym(&X);
  auto one = SymExpr::num(1);
  auto e   = SymExpr::add(x, one);

  llvm::outs() << "x+1 prints as: "; e.print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "+∞ prints as: "; SymExpr::inf().print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "-∞ prints as: "; SymExpr::negInf().print(llvm::outs()); llvm::outs() << "\n";
}

// ── SymRange ─────────────────────────────────────────────────────────────────

static void testRangeBasic() {
  llvm::outs() << "=== SymRange: basic ===\n";
  auto z   = SymExpr::num(0);
  auto ten = SymExpr::num(10);

  auto r = SymRange::of(z, ten);
  llvm::outs() << "[0,10] prints as: "; r.print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "∅ prints as: ";      SymRange::bottom().print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "full prints as: ";   SymRange::full().print(llvm::outs()); llvm::outs() << "\n";

  llvm::outs() << "[0,10] == [0,10]: "  << (SymRange::of(z,ten) == SymRange::of(z,ten) ? "true" : "false") << "\n";
  llvm::outs() << "∅ == ∅: "            << (SymRange::bottom() == SymRange::bottom()   ? "true" : "false") << "\n";
  llvm::outs() << "[0,10] == ∅: "       << (r == SymRange::bottom()                    ? "true" : "false") << "\n";
}

static void testRangeJoin() {
  llvm::outs() << "=== SymRange: join ===\n";
  auto z   = SymExpr::num(0);
  auto one = SymExpr::num(1);
  auto n5  = SymExpr::num(5);
  auto ten = SymExpr::num(10);

  auto r3 = SymRange::of(z, n5);
  auto r4 = SymRange::of(one, ten);
  auto bot = SymRange::bottom();
  auto top = SymRange::full();

  llvm::outs() << "[0,5] ⊔ [1,10] = ";   r3.join(r4).print(llvm::outs());  llvm::outs() << "\n";
  llvm::outs() << "∅ ⊔ [0,5] = ";        bot.join(r3).print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "[0,5] ⊔ ∅ = ";        r3.join(bot).print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "[0,10] ⊔ [-∞,+∞] = "; SymRange::of(z,ten).join(top).print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "[-∞,+∞] ⊔ [0,10] = "; top.join(SymRange::of(z,ten)).print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "∅ ⊔ ∅ = ";            bot.join(bot).print(llvm::outs()); llvm::outs() << "\n";
}

static void testRangeWiden() {
  llvm::outs() << "=== SymRange: widen ===\n";
  auto z   = SymExpr::num(0);
  auto one = SymExpr::num(1);
  auto n5  = SymExpr::num(5);
  auto ten = SymExpr::num(10);
  auto bot = SymRange::bottom();

  // lower stable, upper grows → upper becomes +∞
  llvm::outs() << "[0,5] ∇ [0,10] = ";  SymRange::of(z,n5).widen(SymRange::of(z,ten)).print(llvm::outs());  llvm::outs() << "\n";
  // upper stable, lower shrinks → lower becomes -∞
  llvm::outs() << "[1,5] ∇ [0,5] = ";   SymRange::of(one,n5).widen(SymRange::of(z,n5)).print(llvm::outs()); llvm::outs() << "\n";
  // both change → [-∞, +∞]
  llvm::outs() << "[0,5] ∇ [1,10] = ";  SymRange::of(z,n5).widen(SymRange::of(one,ten)).print(llvm::outs()); llvm::outs() << "\n";
  // stable → unchanged
  llvm::outs() << "[0,5] ∇ [0,5] = ";   SymRange::of(z,n5).widen(SymRange::of(z,n5)).print(llvm::outs());  llvm::outs() << "\n";
  // bottom lhs → rhs
  llvm::outs() << "∅ ∇ [0,5] = ";       bot.widen(SymRange::of(z,n5)).print(llvm::outs()); llvm::outs() << "\n";
  // bottom rhs → lhs
  llvm::outs() << "[0,5] ∇ ∅ = ";       SymRange::of(z,n5).widen(bot).print(llvm::outs()); llvm::outs() << "\n";
}

static void testRangeSymbolic() {
  llvm::outs() << "=== SymRange: symbolic bounds ===\n";
  llvm::LLVMContext ctx;
  llvm::Type *i64 = llvm::Type::getInt64Ty(ctx);
  llvm::Argument N(i64, "N");

  auto n   = SymExpr::sym(&N);
  auto z   = SymExpr::num(0);
  auto one = SymExpr::num(1);

  auto r1 = SymRange::of(z, n);
  auto r2 = SymRange::of(z, SymExpr::add(n, one));

  llvm::outs() << "[0,N] prints as: ";     r1.print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "[0,N+1] prints as: ";   r2.print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "[0,N] == [0,N]: "       << (r1 == SymRange::of(z, n) ? "true" : "false") << "\n";
  llvm::outs() << "[0,N] == [0,N+1]: "     << (r1 == r2                 ? "true" : "false") << "\n";

  // join with symbolic: [0,N] ⊔ [0,N+1] should produce [0, N+1] (or wider)
  auto joined = r1.join(r2);
  llvm::outs() << "[0,N] ⊔ [0,N+1] prints as: "; joined.print(llvm::outs()); llvm::outs() << "\n";
}

int main() {
  testExprConstants();
  testExprInfinity();
  testExprEquality();
  testExprDistributivity();
  testExprPrint();
  testRangeBasic();
  testRangeJoin();
  testRangeWiden();
  testRangeSymbolic();
  return 0;
}
