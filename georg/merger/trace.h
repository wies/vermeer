#ifndef TRACE_H_INCLUDED
#define TRACE_H_INCLUDED

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

struct product_t {
  int variable_id;
  int factor;
};

struct term_t {
  std::vector<product_t> products;
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

struct trace_t {
  std::vector<variable_declaration_t> variable_declarations;
  std::vector<statement_t> statements;
  int nr_of_threads;
};

#endif // TRACE_H_INCLUDED
