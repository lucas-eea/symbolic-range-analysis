#include "GiNaCGlue.h"
#include "SymBoxes.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <sstream>
#include <string>

using namespace symboxes;

static bool pass(bool cond) { return cond; }

//===-- SymExpr -----------------------------------------------------------===//

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

static void testExprOverflow() {
  llvm::outs() << "=== SymExpr: APInt constants and overflow ===\n";
  using llvm::APInt;
  const unsigned W = SymExpr::Width;
  auto max = SymExpr::num(APInt::getSignedMaxValue(W));
  auto min = SymExpr::num(APInt::getSignedMinValue(W));
  auto one = SymExpr::num(1);
  auto two = SymExpr::num(2);
  auto m1  = SymExpr::num(-1);
  auto i64max = SymExpr::num(INT64_MAX);

  llvm::outs() << "INT64_MAX + 1 prints as: "; SymExpr::add(i64max, one).print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "i128 -1 prints as: "; SymExpr::num(APInt::getAllOnes(128)).print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "MAX + 1 == +∞: " << ((SymExpr::add(max, one) == SymExpr::inf()) ? "true" : "false") << "\n";
  llvm::outs() << "MIN - 1 == -∞: " << ((SymExpr::sub(min, one) == SymExpr::negInf()) ? "true" : "false") << "\n";
  llvm::outs() << "MAX * 2 == +∞: " << ((SymExpr::mul(max, two) == SymExpr::inf()) ? "true" : "false") << "\n";
  llvm::outs() << "MAX * -2 == -∞: " << ((SymExpr::mul(max, SymExpr::num(-2)) == SymExpr::negInf()) ? "true" : "false") << "\n";
  llvm::outs() << "MIN / -1 == +∞: " << ((SymExpr::div(min, m1) == SymExpr::inf()) ? "true" : "false") << "\n";
  llvm::outs() << "min(-1, 2) == -1: " << ((SymExpr::mkMin(m1, two) == m1) ? "true" : "false") << "\n";
  llvm::outs() << "max(-1, 2) == 2: " << ((SymExpr::mkMax(m1, two) == two) ? "true" : "false") << "\n";
}

static void testExprMinMax() {
  llvm::outs() << "=== SymExpr: min/max ===\n";
  llvm::LLVMContext ctx;
  llvm::Type *i64 = llvm::Type::getInt64Ty(ctx);
  llvm::Argument A(i64, "a");
  llvm::Argument B(i64, "b");
  auto a = SymExpr::sym(&A);
  auto b = SymExpr::sym(&B);
  auto zero = SymExpr::num(0);
  auto three = SymExpr::num(3);
  auto minAB = SymExpr::mkMin(a, b);

  llvm::outs() << "+∞ == 0: " << (SymExpr::inf() == zero ? "true" : "false") << "\n";
  llvm::outs() << "-∞ == 0: " << (SymExpr::negInf() == zero ? "true" : "false") << "\n";
  llvm::outs() << "min(a,b) == max(a,b): " << (minAB == SymExpr::mkMax(a, b) ? "true" : "false") << "\n";
  llvm::outs() << "min(a,b) == min(b,a): " << (minAB == SymExpr::mkMin(b, a) ? "true" : "false") << "\n";
  llvm::outs() << "min(a,b)+1 == 1: " << (SymExpr::add(minAB, SymExpr::num(1)) == SymExpr::num(1) ? "true" : "false") << "\n";
  llvm::outs() << "min(a,a) prints as: "; SymExpr::mkMin(a, a).print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "min(3,b) prints as: "; SymExpr::mkMin(three, b).print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "max(3,b) prints as: "; SymExpr::mkMax(three, b).print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "[3,3] ⊔ [b,b] = "; SymRange::single(three).join(SymRange::single(b)).print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "min(a,b)+1 metadata: "; ginac_glue::print(SymExpr::add(minAB, SymExpr::num(1)), llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "(min(a,b)+1)*2 metadata: "; ginac_glue::print(SymExpr::mul(SymExpr::add(minAB, SymExpr::num(1)), SymExpr::num(2)), llvm::outs()); llvm::outs() << "\n";
}

static std::string str(const SymExpr &E) {
  std::string S;
  llvm::raw_string_ostream OS(S);
  E.print(OS);
  return S;
}

static void testCanonicalForm() {
  llvm::outs() << "=== SymExpr: canonical form ===\n";
  llvm::LLVMContext ctx;
  llvm::Type *i8 = llvm::Type::getInt8Ty(ctx);
  llvm::Type *i64 = llvm::Type::getInt64Ty(ctx);
  llvm::Argument A(i64, "a"), B(i64, "b"), C(i64, "c"), X(i8, "x");
  auto a = SymExpr::sym(&A), b = SymExpr::sym(&B), c = SymExpr::sym(&C);
  auto n = [](int64_t K) { return SymExpr::num(K); };

  llvm::outs() << "min(a, a+1) = " << str(SymExpr::mkMin(a, SymExpr::add(a, n(1)))) << "\n";
  llvm::outs() << "max(a+3, a, a+1) = "
               << str(SymExpr::mkMax(SymExpr::mkMax(SymExpr::add(a, n(3)), a), SymExpr::add(a, n(1)))) << "\n";
  llvm::outs() << "min(min(a,b),c) = " << str(SymExpr::mkMin(SymExpr::mkMin(a, b), c)) << "\n";
  llvm::outs() << "min(a, max(a,b)) = " << str(SymExpr::mkMin(a, SymExpr::mkMax(a, b))) << "\n";
  llvm::outs() << "-min(a,b) = " << str(SymExpr::neg(SymExpr::mkMin(a, b))) << "\n";
  llvm::outs() << "(4a+8)/4 = " << str(SymExpr::div(SymExpr::add(SymExpr::mul(n(4), a), n(8)), n(4))) << "\n";
  llvm::outs() << "a/4 = " << str(SymExpr::div(a, n(4))) << "\n";
  llvm::outs() << "a/4 - a/4 == 0: " << (SymExpr::sub(SymExpr::div(a, n(4)), SymExpr::div(a, n(4))) == n(0) ? "true" : "false") << "\n";
  llvm::outs() << "-7/2 = " << str(SymExpr::div(n(-7), n(2))) << "\n";
  llvm::outs() << "a*b sign unknown times min = top: " << (SymExpr::mul(SymExpr::mkMin(a, b), c).kind() == SymExpr::Top ? "true" : "false") << "\n";

  // Size cap: a min of more than MaxArgs unrelated symbols becomes Top.
  std::vector<std::unique_ptr<llvm::Argument>> Args;
  SymExpr M = SymExpr::inf();
  for (unsigned I = 0; I <= SymExpr::MaxArgs; ++I) {
    Args.push_back(std::make_unique<llvm::Argument>(i64, "s" + std::to_string(I)));
    M = SymExpr::mkMin(M, SymExpr::sym(Args.back().get()));
  }
  llvm::outs() << "min of " << SymExpr::MaxArgs + 1 << " symbols is top: " << (M.kind() == SymExpr::Top ? "true" : "false") << "\n";
  llvm::outs() << "as a range: "; SymRange::of(M, M).print(llvm::outs()); llvm::outs() << "\n";

  // Interval evaluation, x in [-128, 127] and a in [0, 10].
  auto Bounds = [&](llvm::Value *V) -> std::optional<std::pair<GiNaC::numeric, GiNaC::numeric>> {
    if (V == &X) return std::make_pair(GiNaC::numeric(-128), GiNaC::numeric(127));
    if (V == &A) return std::make_pair(GiNaC::numeric(0), GiNaC::numeric(10));
    return std::nullopt;
  };
  auto show = [&](const char *Name, const SymExpr &E) {
    NumInterval I = evaluate(E, Bounds);
    llvm::outs() << "eval " << Name << " = [";
    std::ostringstream L, H;
    if (I.Lo) L << *I.Lo; else L << "-inf";
    if (I.Hi) H << *I.Hi; else H << "+inf";
    llvm::outs() << L.str() << ", " << H.str() << "]\n";
  };
  auto x = SymExpr::sym(&X);
  show("x+1", SymExpr::add(x, n(1)));
  show("min(a+1, 5)", SymExpr::mkMin(SymExpr::add(a, n(1)), n(5)));
  show("max(a, b)", SymExpr::mkMax(a, b));
  show("a*x", SymExpr::mul(a, x));
  show("x/4", SymExpr::div(x, n(4)));

  llvm::outs() << "[0,+inf] narrow [0,200] = "; SymRange::of(n(0), SymExpr::inf()).narrow(SymRange::of(n(0), n(200))).print(llvm::outs()); llvm::outs() << "\n";
  llvm::outs() << "[0,5] narrow [0,3] = "; SymRange::of(n(0), n(5)).narrow(SymRange::of(n(0), n(3))).print(llvm::outs()); llvm::outs() << "\n";
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

//===-- SymRange ----------------------------------------------------------===//

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

  // lower stable, upper grows -> upper becomes +inf
  llvm::outs() << "[0,5] ∇ [0,10] = ";  SymRange::of(z,n5).widen(SymRange::of(z,ten)).print(llvm::outs());  llvm::outs() << "\n";
  // upper stable, lower shrinks -> lower becomes -inf
  llvm::outs() << "[1,5] ∇ [0,5] = ";   SymRange::of(one,n5).widen(SymRange::of(z,n5)).print(llvm::outs()); llvm::outs() << "\n";
  // both change -> [-inf, +inf]
  llvm::outs() << "[0,5] ∇ [1,10] = ";  SymRange::of(z,n5).widen(SymRange::of(one,ten)).print(llvm::outs()); llvm::outs() << "\n";
  // stable -> unchanged
  llvm::outs() << "[0,5] ∇ [0,5] = ";   SymRange::of(z,n5).widen(SymRange::of(z,n5)).print(llvm::outs());  llvm::outs() << "\n";
  // bottom lhs -> rhs
  llvm::outs() << "∅ ∇ [0,5] = ";       bot.widen(SymRange::of(z,n5)).print(llvm::outs()); llvm::outs() << "\n";
  // bottom rhs -> lhs
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

  // join with symbolic: [0,N] join [0,N+1] should produce [0, N+1] (or wider)
  auto joined = r1.join(r2);
  llvm::outs() << "[0,N] ⊔ [0,N+1] prints as: "; joined.print(llvm::outs()); llvm::outs() << "\n";
}

int main() {
  testExprConstants();
  testExprInfinity();
  testExprOverflow();
  testExprMinMax();
  testCanonicalForm();
  testExprEquality();
  testExprDistributivity();
  testExprPrint();
  testRangeBasic();
  testRangeJoin();
  testRangeWiden();
  testRangeSymbolic();
  return 0;
}
