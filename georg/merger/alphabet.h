#ifndef ALPHABET_H_INCLUDED
#define ALPHABET_H_INCLUDED

namespace alphabet {

struct ssa_variable_t {
  int unique_id;
  int variable_id;
  /* type, currently: INT */
  int thread_id;
  int ssa_index;
};

struct pi_assignment_t;
struct local_assignment_t;
struct phi_assignment_t;

struct stmt_visitor_t {

  virtual void visit_pi_assignment(pi_assignment_t& a) = 0;
  virtual void visit_local_assignment(local_assignment_t& a) = 0;
  virtual void visit_phi_assignment(phi_assignment_t& a) = 0;

};

struct stmt_t {

  virtual void accept(stmt_visitor_t& visitor) = 0;

};

struct pi_assignment_t : public stmt_t {
  ssa_variable_t variable;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_pi_assignment(*this);
  }

};

struct local_assignment_t : public stmt_t {
  ssa_variable_t variable;
  /* ... */

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_local_assignment(*this);
  }

};

struct phi_assignment_t : public stmt_t {
  ssa_variable_t variable;
  /* ... */

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_phi_assignment(*this);
  }

};

struct local_execution_t {
  std::vector<stmt_t*> stmts;
};

}

#endif // ALPHABET_H_INCLUDED
