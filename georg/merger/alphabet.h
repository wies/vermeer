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
struct assertion_t;
struct assumption_t;
struct local_execution_t;

struct stmt_visitor_t {

  virtual void visit_pi_assignment(pi_assignment_t& a) = 0;
  virtual void visit_local_assignment(local_assignment_t& a) = 0;
  virtual void visit_global_assignment(global_assignment_t& a) = 0;
  virtual void visit_phi_assignment(phi_assignment_t& a) = 0;
  virtual void visit_assertion(assertion_t& a) = 0;
  virtual void visit_assumption(assumption_t& a) = 0;
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

  friend std::ostream& operator<<(std::ostream& out, const local_assignment_t& a) {
    out << a.local_variable << " := " << a.rhs;
    return out;
  }

};

struct pi_assignment_t : public stmt_t {
  ssa_variable_t local_variable; // lhs
  ssa_variable_t shared_variable; // rhs

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_pi_assignment(*this);
  }

  friend std::ostream& operator<<(std::ostream& out, const pi_assignment_t& a) {
    out << a.local_variable << " := pi(" << a.shared_variable << ")";
    return out;
  }

};

struct global_assignment_t : public stmt_t {
  ssa_variable_t shared_variable; // lhs
  expr::term_t<ssa_variable_t> rhs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_global_assignment(*this);
  }

  friend std::ostream& operator<<(std::ostream& out, const global_assignment_t& a) {
    out << a.shared_variable << " := " << a.rhs;
    return out;
  }

};

struct phi_assignment_t : public stmt_t {
  ssa_variable_t variable; // lhs
  /* ... */

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_phi_assignment(*this);
  }

};

struct assertion_t : public stmt_t {

  std::vector<expr::expr_t<ssa_variable_t>> exprs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_assertion(*this);
  }

  friend std::ostream& operator<<(std::ostream& out, const assertion_t& a) {
    out << "assert(";
    switch (a.exprs.size()) {
      case 0:
        out << "true";
        break;
      case 1:
        out << a.exprs[0];
        break;
      default:
        out << "(" << a.exprs[0] << ")";
        for (size_t i = 1; i < a.exprs.size(); i++) {
          out << " && (" << a.exprs[i] << ")";
        }
        break;
    }
    out << ")";

    return out;
  }

};

struct assumption_t : public stmt_t {

  std::vector<expr::expr_t<ssa_variable_t>> exprs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_assumption(*this);
  }

  friend std::ostream& operator<<(std::ostream& out, const assumption_t& a) {
    out << "assume(";
    switch (a.exprs.size()) {
      case 0:
        out << "true";
        break;
      case 1:
        out << a.exprs[0];
        break;
      default:
        out << "(" << a.exprs[0] << ")";
        for (size_t i = 1; i < a.exprs.size(); i++) {
          out << " && (" << a.exprs[i] << ")";
        }
        break;
    }
    out << ")";

    return out;
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
