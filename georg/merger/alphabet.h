#ifndef ALPHABET_H_INCLUDED
#define ALPHABET_H_INCLUDED

#include "program_location.h"
#include "graph.h"

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

};

struct stmt_t {

  virtual ~stmt_t() {}

  std::vector<expr::expr_t<ssa_variable_t>> guards;
  thread_local_position_t program_location; // program location

  virtual void accept(stmt_visitor_t& visitor) = 0;

  void print_guards(std::ostream& out) const {
    out << "guard(";

    if (guards.empty()) {
      out << "true";
    }
    else if (guards.size() == 1) {
      out << guards[0];
    }
    else {
      out << "(" << guards[0] << ")";

      for (size_t i = 1; i < guards.size(); i++) {
        out << " && (" << guards[i] << ")";
      }
    }

    out << ") -> ";
  }

  virtual void print(std::ostream& out) const = 0;

  friend std::ostream& operator<<(std::ostream& out, const stmt_t& s) {
    out << s.program_location << ": ";
    s.print_guards(out);
    s.print(out);
    return out;
  }

};

struct local_assignment_t : public stmt_t {
  ssa_variable_t local_variable; // lhs
  expr::term_t<ssa_variable_t> rhs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_local_assignment(*this);
  }

  void print(std::ostream& out) const override {
    out << local_variable << " := " << rhs;
  }

};

struct pi_assignment_t : public stmt_t {
  ssa_variable_t local_variable; // lhs
  ssa_variable_t shared_variable; // rhs

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_pi_assignment(*this);
  }

  void print(std::ostream& out) const override {
    out << local_variable << " := pi(" << shared_variable << ")";
  }

};

struct global_assignment_t : public stmt_t {
  ssa_variable_t shared_variable; // lhs
  expr::term_t<ssa_variable_t> rhs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_global_assignment(*this);
  }

  void print(std::ostream& out) const override {
    out << shared_variable << " := " << rhs;
  }

};

struct phi_assignment_t : public stmt_t {
  ssa_variable_t variable; // lhs
  /* ... */

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_phi_assignment(*this);
  }

  void print(std::ostream& out) const override {
    out << "phi(...)";
  }

};

struct assertion_t : public stmt_t {

  std::vector<expr::expr_t<ssa_variable_t>> exprs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_assertion(*this);
  }

  void print(std::ostream& out) const override {
    out << "assert(";
    switch (exprs.size()) {
      case 0:
        out << "true";
        break;
      case 1:
        out << exprs[0];
        break;
      default:
        out << "(" << exprs[0] << ")";
        for (size_t i = 1; i < exprs.size(); i++) {
          out << " && (" << exprs[i] << ")";
        }
        break;
    }
    out << ")";
  }

};

struct assumption_t : public stmt_t {

  std::vector<expr::expr_t<ssa_variable_t>> exprs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_assumption(*this);
  }

  void print(std::ostream& out) const override {
    out << "assume(";
    switch (exprs.size()) {
      case 0:
        out << "true";
        break;
      case 1:
        out << exprs[0];
        break;
      default:
        out << "(" << exprs[0] << ")";
        for (size_t i = 1; i < exprs.size(); i++) {
          out << " && (" << exprs[i] << ")";
        }
        break;
    }
    out << ")";
  }

};

struct projected_execution_t {

  std::map<int, std::vector<stmt_t*>> projections;

  ~projected_execution_t() {
    for (auto& p : projections) {
      for (auto& s : p.second) {
        delete s;
      }
    }
  }

  friend std::ostream& operator<<(std::ostream& out, const projected_execution_t& p) {
    for (auto& e : p.projections) {
      out << "Thread " << e.first << ": " << e.second.size() << std::endl;
      for (auto& s : e.second) {
        out << *s << std::endl;
      }
      out << std::endl;
    }

    return out;
  }

};

struct projected_executions_t {

  std::map<int, graph_t<int>> projections;

  projected_executions_t(const projected_execution_t& p) {
    // TODO initialize projections with p;
  }

};

}

#endif // ALPHABET_H_INCLUDED
