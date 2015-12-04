#include "expr.h"

#include <cstdlib>
#include <iostream>

struct my_test_visitor {

  void visit_expr(expr::expr_t<char>& e) {
    std::cout << "expression...";
    e.term.accept(*this);
  }

  void visit_term(expr::term_t<char>& t) {
    std::cout << "term...";
    for (auto& p : t.products) {
      p.accept(*this);
    }
  }

  void visit_linear_product(expr::linear_product_t<char>& p) {
    std::cout << "linear product...";
  }

};

int main(int argc, char* argv[]) {
  expr::linear_product_t<char> p1;
  p1.factor = 42;
  p1.variable = 'a';

  expr::linear_product_t<char> p2;
  p2.factor = 33;
  p2.variable = 'b';

  expr::term_t<char> t;
  t.constant = 5;
  t.products.push_back(p1);
  t.products.push_back(p2);

  expr::expr_t<char> ex;
  ex.op = expr::NEQ;
  ex.term.constant = 5;
  ex.term.products.push_back(p1);
  ex.term.products.push_back(p2);

  std::cout << ex << std::endl;

  my_test_visitor v;
  ex.accept(v);
  std::cout << std::endl;

  expr::variable_substitution_t<char, char> subst;
  subst.substitution_map.insert({ 'a', 'A' });
  subst.substitution_map.insert({ 'b', 'B' });
  expr::expr_t<char> ex2 = ex.accept<expr::variable_substitution_t<char, char>, expr::expr_t<char>>(subst);
  std::cout << ex2 << std::endl;

  return EXIT_SUCCESS;
}
