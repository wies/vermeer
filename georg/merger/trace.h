#ifndef TRACE_H_INCLUDED
#define TRACE_H_INCLUDED

#include <vector>

namespace exe {

struct execution_t;
struct assignment_t;
struct assertion_t;
struct assumption_t;

struct stmt_visitor_t {

  virtual void visit_execution(execution_t& e) = 0;
  virtual void visit_assignment(assignment_t& a) = 0;
  virtual void visit_assertion(assertion_t& a) = 0;
  virtual void visit_assumption(assumption_t& a) = 0;

};

enum variable_types_t {
  INT
};

struct variable_declaration_t {
  int id;
  int variable;
  int ssa_index;
  variable_types_t type;
  int thread;
};

struct linear_product_t {
  int variable_id;
  int factor;
};

struct term_t {
  std::vector<linear_product_t> products;
  int constant;
};

enum ops {
  EQ, NEQ, LT, LEQ, GT, GEQ
};

struct expression_t {
  ops op;
  term_t term;
};

struct guard_t {
  std::vector<expression_t> exprs;
};

struct stmt_t {

  virtual ~stmt_t() {}

  guard_t guard;
  int position;
  int thread;

  virtual void accept(stmt_visitor_t& v) = 0;

};

struct assignment_t : public stmt_t {

  virtual ~assignment_t() {}

  int variable_id;
  term_t rhs;

  virtual void accept(stmt_visitor_t& v) override {
    v.visit_assignment(*this);
  }

};

struct assertion_t : public stmt_t {

  virtual ~assertion_t() {}

  std::vector<expression_t> exprs;

  virtual void accept(stmt_visitor_t& v) override {
    v.visit_assertion(*this);
  }

};

struct assumption_t : public stmt_t {

  virtual ~assumption_t() {}

  std::vector<expression_t> exprs;

  virtual void accept(stmt_visitor_t& v) override {
    v.visit_assumption(*this);
  }

};

// TODO we have to make sure that variable_declarations and statements are ordered according to their id and position, respectively. We don't need vectors, we can preallocate arrays.
struct execution_t {
  std::vector<variable_declaration_t> variable_declarations;
  std::vector<stmt_t*> statements;
  int nr_of_threads;

  ~execution_t() {
    for (auto& s : statements) {
      delete s;
    }
  }

  void accept(stmt_visitor_t& v) {
    v.visit_execution(*this);
  }

};

}

#endif // TRACE_H_INCLUDED
