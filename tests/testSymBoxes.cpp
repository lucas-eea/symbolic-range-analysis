#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/DerivedTypes.h"
#include "SymBoxes.h"
#include "GiNaCGlue.h"


void testRange(){
  llvm::outs() << "Range tests \n";
  auto zero = symboxes::SymExpr::num(0);
  auto one = symboxes::SymExpr::num(1);
  auto five = symboxes::SymExpr::num(5);
  auto ten = symboxes::SymExpr::num(10);

  auto r1 = symboxes::SymRange::of(zero, ten);
  auto r2 = symboxes::SymRange::of(zero, ten);
  llvm::outs() << "[0,10] == [0,10]: " << (r1 == r2 ? "true" : "false") << "\n";

  // Join
  auto r3 = symboxes::SymRange::of(zero, five);
  auto r4 = symboxes::SymRange::of(one, ten);
  auto joined = r3.join(r4);
  llvm::outs() << "[0,5] join [1,10] = "; joined.print(llvm::outs()); llvm::outs() << "\n";

  // Join with bottom
  auto bot = symboxes::SymRange::bottom();
  auto r5  = bot.join(r3);
  llvm::outs() << "∅ ⊔ [0,5] = "; r5.print(llvm::outs()); llvm::outs() << "\n";
  auto r5b = r3.join(bot);
  llvm::outs() << "[0,5] ⊔ ∅ = "; r5b.print(llvm::outs()); llvm::outs() << "\n";

  // Join with greatest element
  auto greatest = symboxes::SymRange::full();
  auto r6 = symboxes::SymRange::of(zero, ten);
  auto r6b = r6.join(greatest);
  llvm::outs() << "[0,10] ⊔ [-∞, +∞] = "; r6b.print(llvm::outs()); llvm::outs() << "\n";
  auto r6c = greatest.join(r6);
  llvm::outs() << "[-∞, +∞] ⊔ [0,10] = "; r6b.print(llvm::outs()); llvm::outs() << "\n"; 

  // Widen operator
  // Lower same but upper grows
  auto r7 = symboxes::SymRange::of(zero, five);
  auto r8 = symboxes::SymRange::of(zero, ten);
  auto w1 = r7.widen(r8);
  llvm::outs() << "[0,5] ∇ [0,10] = "; w1.print(llvm::outs()); llvm::outs() << "\n";

  // Upper same but lower shrinks
  auto r9 = symboxes::SymRange::of(one, five);
  auto r10 = symboxes::SymRange::of(zero, five);
  auto w2 = r9.widen(r10);
  llvm::outs() << "[1,5] ∇ [0,5] = "; w2.print(llvm::outs()); llvm::outs() << "\n";

  // Both change
  auto r11 = symboxes::SymRange::of(zero, five);
  auto r12 = symboxes::SymRange::of(one, ten);
  auto w3 = r11.widen(r12);
  llvm::outs() << "[0,5] ∇ [1,10] = "; w3.print(llvm::outs()); llvm::outs() << "\n";

  // No change
  auto r13 = symboxes::SymRange::of(zero, five);
  auto r14 = symboxes::SymRange::of(zero, five);
  auto w4 = r13.widen(r14);
  llvm::outs() << "[0,5] ∇ [0,5] = "; w4.print(llvm::outs()); llvm::outs() << "\n";
}
void testExprDistributivity(){
  llvm::outs() << "Distributivity test \n";
  llvm::LLVMContext ctx;
  llvm::Type *i64 = llvm::Type::getInt64Ty(ctx);
  llvm::Argument A(i64, "A");
  llvm::Argument B(i64, "B");
  llvm::Argument C(i64, "C");

  auto a = symboxes::SymExpr::sym(&A);
  auto b = symboxes::SymExpr::sym(&B);
  auto c = symboxes::SymExpr::sym(&C);
  
  auto e1 = symboxes::SymExpr::add(a,b);
  e1 = symboxes::SymExpr::mul(e1,c);

  auto e2 = symboxes::SymExpr::mul(a, c);
  e2 = symboxes::SymExpr::add(e2, symboxes::SymExpr::mul(b,c));

  llvm::outs() << "(a+b)*c == a*c + b*c: " << ((e1 == e2) ? "true" : "false");
}

void testExprAssociativity(){
  llvm::outs() << "Associativity test \n";
  llvm::LLVMContext ctx;
  llvm::Type *i64 = llvm::Type::getInt64Ty(ctx);
  llvm::Argument A(i64, "A");
  llvm::Argument B(i64, "B");

  auto a = symboxes::SymExpr::sym(&A);
  auto b = symboxes::SymExpr::sym(&B);

  auto e1 = symboxes::SymExpr::add(a,b);
  auto e2 = symboxes::SymExpr::add(b,a);

  llvm::outs() << "(a+b) == (b+a): " << ((e1 == e2) ? "true" : "false") << "\n";
}

void testExprEquality() {
  llvm::outs() << "Equality test \n"; 
  llvm::LLVMContext ctx;
  llvm::Type *i64 = llvm::Type::getInt64Ty(ctx);

  llvm::Argument V(i64, "V");
  llvm::Argument S(i64, "B");

  auto v = symboxes::SymExpr::sym(&V);
  auto s = symboxes::SymExpr::sym(&S);

  // v + s == s + v
  auto lhs = symboxes::SymExpr::add(v, s);
  auto rhs = symboxes::SymExpr::add(s, v);

  llvm::outs() << "v + s == s + v: " << (lhs == rhs ? "true" : "false") << "\n";

  // v + s != v + v
  auto rhs2 = symboxes::SymExpr::add(v, v);
  llvm::outs() << "v + s == v + v: " << (lhs == rhs2 ? "true" : "false") << "\n";

  // v == v
  llvm::outs() << "v == v: " << (v == v ? "true" : "false") << "\n";

  // v != s
  llvm::outs() << "v == s: " << (v == s ? "true" : "false") << "\n";
}

int main(){

  llvm::outs() << "SymExpr tests: \n";
  testExprEquality();
  testExprAssociativity();
  testExprDistributivity();

  llvm::outs() << "SymRange tests: \n";
  testRange();
  return 0;
}
