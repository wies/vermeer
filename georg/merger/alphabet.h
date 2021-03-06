#ifndef ALPHABET_H_INCLUDED
#define ALPHABET_H_INCLUDED

#include "program_location.h"
#include "graph.h"
#include "expr.h"
#include "tag.h"

#include <functional>
#include <iostream>

namespace alphabet {

struct ssa_variable_t {

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

  inline
  bool operator<(const ssa_variable_t& v) const {
    if (variable_id < v.variable_id) {
      return true;
    }

    if (variable_id == v.variable_id) {
      if (ssa_index.thread_id < v.ssa_index.thread_id) {
        return true;
      }

      if (ssa_index.thread_id == v.ssa_index.thread_id) {
        return (ssa_index.thread_local_index < v.ssa_index.thread_local_index);
      }
    }

    return false;
  }

  friend std::ostream& operator<<(std::ostream& out, const ssa_variable_t& v);

};

struct stmt_visitor_t;

struct stmt_t {

  enum stmt_type_t {
    PI_ASSIGNMENT,
    LOCAL_ASSIGNMENT,
    GLOBAL_ASSIGNMENT,
    ASSERTION,
    ASSUMPTION
  };

  friend std::ostream& operator<<(std::ostream& out, const stmt_type_t t);

  const stmt_type_t type;

  stmt_t(stmt_type_t t) : type(t) {}
  virtual ~stmt_t() {}

  std::vector<expr::expr_t<ssa_variable_t>> guards;
  thread_local_position_t program_location; // program location

  virtual void accept(stmt_visitor_t& visitor) = 0;

  void print_guards(std::ostream& out) const;
  virtual void print(std::ostream& out) const = 0;

  friend std::ostream& operator<<(std::ostream& out, const stmt_t& s);

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

  void accept(stmt_visitor_t& visitor) override;
  void print(std::ostream& out) const override;

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

  void accept(stmt_visitor_t& visitor) override;
  void print(std::ostream& out) const override;

};

struct pi_assignment_t : public stmt_t {
  ssa_variable_t local_variable; // lhs
  ssa_variable_t shared_variable; // rhs

  pi_assignment_t() : stmt_t(PI_ASSIGNMENT) {}

  inline
  bool operator==(const pi_assignment_t& other) const {
    return (local_variable == other.local_variable && shared_variable == other.shared_variable);
  }

  inline
  bool operator!=(const pi_assignment_t& other) const {
    return !(*this == other);
  }

  void accept(stmt_visitor_t& visitor) override;
  void print(std::ostream& out) const override;

};

struct assertion_t : public stmt_t {

  std::vector<expr::expr_t<ssa_variable_t>> exprs;

  assertion_t() : stmt_t(ASSERTION) {}

  inline
  bool operator==(const assertion_t& other) const {
    if (exprs.size() != other.exprs.size()) {
      return false;
    }

    for (size_t i = 0; i < exprs.size(); ++i) {
      if (exprs[i] != other.exprs[i]) {
        return false;
      }
    }

    return true;
  }

  inline
  bool operator!=(const assertion_t& other) const {
    return !(*this == other);
  }

  void accept(stmt_visitor_t& visitor) override;
  void print(std::ostream& out) const override;

};

struct assumption_t : public stmt_t {

  std::vector<expr::expr_t<ssa_variable_t>> exprs;

  assumption_t() : stmt_t(ASSUMPTION) {}

  inline
  bool operator==(const assumption_t& other) const {
    if (exprs.size() != other.exprs.size()) {
      return false;
    }

    for (size_t i = 0; i < exprs.size(); ++i) {
      if (exprs[i] != other.exprs[i]) {
        return false;
      }
    }

    return true;
  }

  inline
  bool operator!=(const assumption_t& other) const {
    return !(*this == other);
  }

  void accept(stmt_visitor_t& visitor) override;
  void print(std::ostream& out) const override;

};

struct stmt_visitor_t {

  virtual void visit_pi_assignment(pi_assignment_t& a) = 0;
  virtual void visit_local_assignment(local_assignment_t& a) = 0;
  virtual void visit_global_assignment(global_assignment_t& a) = 0;
  virtual void visit_assertion(assertion_t& a) = 0;
  virtual void visit_assumption(assumption_t& a) = 0;

};

}

#endif // ALPHABET_H_INCLUDED
