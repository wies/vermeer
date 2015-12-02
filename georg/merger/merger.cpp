#include <cstdlib>
#include <iostream>

#include <map>
#include <set>
#include <vector>

#include "error.h"
#include "trace.h"
#include "xml.h"

#include "alphabet.h"

#include "expr.h"

#if 0
struct thread_id_t {

  const int unique_id;

  inline
  bool operator==(const thread_id_t& other) const {
    return unique_id == other.unique_id;
  }

  inline
  bool operator!=(const thread_id_t& other) const {
    return !(*this == other);
  }

  inline
  bool operator<(const thread_id_t& other) const {
    return unique_id < other.unique_id;
  }

};
#endif

struct thread_local_position_t {
  //thread_id_t thread;
  int thread;
  int position;

  friend std::ostream& operator<<(std::ostream& out, const thread_local_position_t p) {
    out << "(T" << p.thread << ",P" << p.position << ")";
    return out;
  }
};

std::set<int> extract_variables(const exe::expression_t& e) {
  std::set<int> variable_ids;

  for (const exe::linear_product_t& p : e.term.products) {
    variable_ids.insert(p.variable_id);
  }

  return variable_ids;
}

#if 0
std::vector<thread_local_position_t> extract_thread_local_positions(const exe::execution_t& e) {
  std::vector<thread_local_position_t> v;

  // thread_id x thread-local position
  std::map<int, int> thread_local_counters;

  // variable_id x global position
  std::map<int, int> variable_definitions;

  // variable_id x set of global positions
  std::map<int, std::set<int> > variable_uses;

  // TODO do we assume that statements are ordered according to their position attribute?
  for (auto const& s : e.statements) {
    int pos = thread_local_counters[s->thread];
    v.push_back({ s->thread, pos });
    thread_local_counters[s->thread] = pos + 1;

    // track variable definition
    if (s->type == exe::ASSIGNMENT) {
      variable_definitions[s->variable_id] = s->position;
      std::cout << "Variable " << s->variable_id << " is defined at " << v[variable_definitions[s->variable_id]] << std::endl;
    }

    // track variable usage
    // a) guards
    std::set<int> variable_ids;
    for (auto const& e : s->guard.exprs) {
      auto var_ids = extract_variables(e);
      variable_ids.insert(var_ids.begin(), var_ids.end());
    }

    // b) variables in other expressions
    switch (s->type) {
      case exe::ASSIGNMENT:
        for (auto const& p : s->rhs.products) {
          if (e.variable_declarations[p.variable_id].thread < 0) { // global variable
            std::cout << "G" << p.variable_id;
          }
          variable_ids.insert(p.variable_id);
        }
        break;
      case exe::ASSERTION:
      case exe::ASSUMPTION:
        for (auto const& e : s->exprs) {
          auto var_ids = extract_variables(e);
          variable_ids.insert(var_ids.begin(), var_ids.end());
        }
        break;
    }

    for (int var_id : variable_ids) {
      if (e.variable_declarations[var_id].thread < 0) { // global variable
        std::cout << "g";
      }
      std::cout << var_id << " ";
    }
    std::cout << std::endl;
  }

  for (auto const& p : variable_uses) {
    std::cout << p.first << std::endl;
  }

  return v;
}
#endif

struct local_execution_extractor_t : public exe::stmt_visitor_t {

  std::map<int, std::vector<alphabet::stmt_t*>> local_executions;
  std::vector<exe::variable_declaration_t> variable_declarations;

  void visit_execution(exe::execution_t& e) override {
    for (auto& s : e.statements) {
      s->accept(*this);
    }
  }

  void visit_assignment(exe::assignment_t& a) override {

    // a) is lhs a global variable?
    auto& vd = variable_declarations[a.variable_id];

    if (vd.thread < 0) {
      // assignment to a shared variable
      std::cout << "Assignment to a shared variable: " /*<< a*/ << std::endl;
      // a) check that all variables in the rhs are local variables!

    }
    else {
      // assignment to a local variable
      std::cout << "Assignment to a local variable: " /*<< a*/ << std::endl;
      // a) does the rhs involve shared variables?
      // b) If not, local assigment
      // c) Else global assignment
    }


    std::vector<alphabet::stmt_t*>& v = local_executions[a.thread];
    v.push_back((alphabet::stmt_t*)new alphabet::local_assignment_t);

    /*for (auto& p : a.rhs.products) {
      std::cout << p.variable_id << std::endl;
    }
    ERROR("I cannot handle this case for the moment");*/
    // TODO put the statement into its respective thread
    std::cout << "thread: " << a.thread << std::endl;
  }

  void visit_assertion(exe::assertion_t& a) override {
    std::vector<alphabet::stmt_t*>& v = local_executions[a.thread];
    v.push_back((alphabet::stmt_t*)new alphabet::local_assignment_t);

    //ERROR("I cannot handle this case for the moment");
    std::cout << "thread: " << a.thread << std::endl;
  }

  void visit_assumption(exe::assumption_t& a) override {
    std::vector<alphabet::stmt_t*>& v = local_executions[a.thread];
    v.push_back((alphabet::stmt_t*)new alphabet::local_assignment_t);

    //ERROR("I cannot handle this case for the moment");
    std::cout << "thread: " << a.thread << std::endl;
  }

};

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
  exe::execution_t e = read_execution("example.xml");

  std::cout << e << std::endl;

  local_execution_extractor_t lee;
  lee.variable_declarations.insert(lee.variable_declarations.end(), e.variable_declarations.begin(), e.variable_declarations.end()); // TODO replace
  e.accept(lee);

  for (auto& p : lee.local_executions) {
    std::cout << "Thread " << p.first << ": " << p.second.size() << std::endl;
  }

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
  ex.op = expr::expr_t<char>::NEQ;
  ex.term.constant = 5;
  ex.term.products.push_back(p1);
  ex.term.products.push_back(p2);

  std::cout << ex << std::endl;

  my_test_visitor v;
  ex.accept(v);

#if 0
  auto pos = extract_thread_local_positions(e);

  for (auto const& p : pos) {
    std::cout << p << std::endl;
  }
#endif

  return EXIT_SUCCESS;
}

