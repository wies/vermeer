#ifndef TRACE_H_INCLUDED
#define TRACE_H_INCLUDED

#include <vector>

namespace exe {

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

enum statement_type_t {
  ASSIGNMENT, ASSERTION, ASSUMPTION
};

struct statement_t {
  statement_type_t type;
  int variable_id;
  term_t rhs;
  guard_t guard;
  int position;
  int thread;
  std::vector<expression_t> exprs;
};

// TODO we have to make sure that variable_declarations and statements are ordered according to their id and position, respectively. We don't need vectors, we can preallocate arrays.
struct execution_t {
  std::vector<variable_declaration_t> variable_declarations;
  std::vector<statement_t> statements;
  int nr_of_threads;
};

}

#endif // TRACE_H_INCLUDED
