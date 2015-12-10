#ifndef ALPHABET_H_INCLUDED
#define ALPHABET_H_INCLUDED

#include "program_location.h"
#include "graph.h"

#include <functional>
#include <iostream>

namespace alphabet {

struct ssa_variable_t {

  //int unique_id;
  int variable_id;

  /* type, currently: INT */

  struct ssa_index_t {

    int thread_id;
    int thread_local_index;

    inline
    bool operator==(const ssa_index_t& i) const {
      return (thread_id == i.thread_id && thread_local_index == i.thread_local_index);
    }

    inline
    bool operator!=(const ssa_index_t& i) const {
      return !(*this == i);
    }

  } ssa_index;

  inline
  bool operator==(const ssa_variable_t& v) const {
    return (variable_id == v.variable_id && ssa_index == v.ssa_index);
  }

  inline
  bool operator!=(const ssa_variable_t& v) const {
    return !(*this == v);
  }

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

  enum stmt_type_t {
    PI_ASSIGNMENT,
    LOCAL_ASSIGNMENT,
    GLOBAL_ASSIGNMENT,
    PHI_ASSIGNMENT,
    ASSERTION,
    ASSUMPTION
  };

  friend std::ostream& operator<<(std::ostream& out, const stmt_type_t t) {
    switch (t) {
      case PI_ASSIGNMENT:
        out << "PI_ASSIGNMENT";
        break;
      case LOCAL_ASSIGNMENT:
        out << "LOCAL_ASSIGNMENT";
        break;
      case GLOBAL_ASSIGNMENT:
        out << "GLOBAL_ASSIGNMENT";
        break;
      case PHI_ASSIGNMENT:
        out << "PHI_ASSIGNMENT";
        break;
      case ASSERTION:
        out << "ASSERTION";
        break;
      case ASSUMPTION:
        out << "ASSUMPTION";
        break;
    }
    return out;
  }

  const stmt_type_t type;

  stmt_t(stmt_type_t t) : type(t) {}
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

  local_assignment_t() : stmt_t(LOCAL_ASSIGNMENT) {}

  inline
  bool operator==(const local_assignment_t& other) const {
    return (local_variable == other.local_variable && rhs == other.rhs);
  }

  inline
  bool operator!=(const local_assignment_t& other) const {
    return !(*this == other);
  }

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_local_assignment(*this);
  }

  void print(std::ostream& out) const override {
    out << local_variable << " := " << rhs;
  }

};

struct tagged_variable_t {

  ssa_variable_t shared_variable;
  int execution_id;

  friend std::ostream& operator<<(std::ostream& out, const tagged_variable_t& v) {
    out << v.shared_variable << "@" << v.execution_id;
    return out;
  }

};

struct pi_assignment_t : public stmt_t {
  ssa_variable_t local_variable; // lhs
  //ssa_variable_t shared_variable; // rhs
  std::vector<tagged_variable_t> shared_variables; // rhs: made it a list to enable merging

  pi_assignment_t() : stmt_t(PI_ASSIGNMENT) {}

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_pi_assignment(*this);
  }

  void print(std::ostream& out) const override {
    out << local_variable << " := pi(";

    for (auto& v : shared_variables) {
      out << v << ",";
    }

    out << ")";
  }

};

struct pi_assignments_t : public stmt_t {

  // TODO fix the type!!!
  pi_assignments_t() : stmt_t(PI_ASSIGNMENT) {}

  void accept(stmt_visitor_t& visitor) override {
    ERROR("Unsupported operation");
  }

  void print(std::ostream& out) const override {
    ERROR("Unsupported operation");
  }

};

struct global_assignment_t : public stmt_t {
  ssa_variable_t shared_variable; // lhs
  expr::term_t<ssa_variable_t> rhs;

  global_assignment_t() : stmt_t(GLOBAL_ASSIGNMENT) {}

  inline
  bool operator==(const global_assignment_t& other) const {
    return (shared_variable == other.shared_variable && rhs == other.rhs);
  }

  inline
  bool operator!=(const global_assignment_t& other) const {
    return !(*this == other);
  }

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

  phi_assignment_t() : stmt_t(PHI_ASSIGNMENT) {}

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_phi_assignment(*this);
  }

  void print(std::ostream& out) const override {
    out << "phi(...)";
  }

};

struct assertion_t : public stmt_t {

  std::vector<expr::expr_t<ssa_variable_t>> exprs;

  assertion_t() : stmt_t(ASSERTION) {}

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

  assumption_t() : stmt_t(ASSUMPTION) {}

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

}

#endif // ALPHABET_H_INCLUDED
