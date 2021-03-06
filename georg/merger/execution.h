#ifndef TRACE_H_INCLUDED
#define TRACE_H_INCLUDED

#include "expr.h"
#include "program_location.h"

#include <set>
#include <vector>

namespace exe {

struct execution_t;
struct assignment_t;
struct assertion_t;
struct assumption_t;

struct stmt_visitor_t {

  virtual ~stmt_visitor_t() {}

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
  
  bool is_shared() const {
    return (thread < 0);  
  }
  
  bool is_local() const {
    return !is_shared();  
  }
  
};

struct guard_t {
  std::vector<expr::expr_t<int>> exprs;
};

struct stmt_t {

  virtual ~stmt_t() {}

  guard_t guard;
  int position_in_execution;

  thread_local_position_t program_location;

  virtual void accept(stmt_visitor_t& v) = 0;

};

struct assignment_t : public stmt_t {

  virtual ~assignment_t();

  int variable_id;
  expr::term_t<int> rhs;

  virtual void accept(stmt_visitor_t& v) override;

};

struct assertion_t : public stmt_t {

  virtual ~assertion_t();

  std::vector<expr::expr_t<int>> exprs;

  virtual void accept(stmt_visitor_t& v) override;

};

struct assumption_t : public stmt_t {

  virtual ~assumption_t();

  std::vector<expr::expr_t<int>> exprs;

  virtual void accept(stmt_visitor_t& v) override;

};

// TODO we have to make sure that variable_declarations and statements are ordered according to their id and position, respectively. We don't need vectors, we can preallocate arrays.
struct execution_t {
  std::vector<variable_declaration_t> variable_declarations;
  std::vector<stmt_t*> statements;
  int nr_of_threads;

  ~execution_t();

  void accept(stmt_visitor_t& v);
  std::set<int> shared_variables();

};

}

#endif // TRACE_H_INCLUDED
