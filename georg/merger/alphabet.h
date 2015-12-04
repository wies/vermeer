#ifndef ALPHABET_H_INCLUDED
#define ALPHABET_H_INCLUDED

namespace alphabet {

struct ssa_variable_t {

  //int unique_id;
  int variable_id;

  /* type, currently: INT */

  struct ssa_index_t {
    int thread_id;
    int thread_local_index;
  } ssa_index;

  friend std::ostream& operator<<(std::ostream& out, const ssa_variable_t& v) {
    out << "var(" << v.variable_id << ")_{T" << v.ssa_index.thread_id << "," << v.ssa_index.thread_local_index << "}";
    return out;
  }

};

struct pi_assignment_t;
struct local_assignment_t;
struct global_assignment_t;
struct phi_assignment_t;
struct local_execution_t;

struct stmt_visitor_t {

  virtual void visit_pi_assignment(pi_assignment_t& a) = 0;
  virtual void visit_local_assignment(local_assignment_t& a) = 0;
  virtual void visit_global_assignment(global_assignment_t& a) = 0;
  virtual void visit_phi_assignment(phi_assignment_t& a) = 0;
  virtual void visit_local_execution(local_execution_t& e) = 0;

};

struct stmt_t {

  virtual void accept(stmt_visitor_t& visitor) = 0;

};

struct local_assignment_t : public stmt_t {
  ssa_variable_t local_variable; // lhs
  expr::term_t<ssa_variable_t> rhs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_local_assignment(*this);
  }

};

struct pi_assignment_t : public stmt_t {
  ssa_variable_t local_variable; // lhs
  ssa_variable_t shared_variable; // rhs

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_pi_assignment(*this);
  }

};

struct global_assignment_t : public stmt_t {
  ssa_variable_t shared_variable; // lhs
  expr::term_t<ssa_variable_t> rhs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_global_assignment(*this);
  }

};

struct phi_assignment_t : public stmt_t {
  ssa_variable_t variable; // lhs
  /* ... */

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_phi_assignment(*this);
  }

};

struct local_execution_t : public stmt_t {
  std::vector<stmt_t*> stmts;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_local_execution(*this);
  }

};

}

#endif // ALPHABET_H_INCLUDED
