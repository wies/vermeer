#ifndef ALPHABET_H_INCLUDED
#define ALPHABET_H_INCLUDED

#include "program_location.h"
#include "graph.h"
#include "expr.h"

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

  friend std::ostream& operator<<(std::ostream& out, const ssa_variable_t& v);

};

template <class Tagged>
struct execution_tag_t {

  execution_tag_t(Tagged t_, int execution_id_) : t(t_), eid(execution_id_) {}
  execution_tag_t(const execution_tag_t& other) : t(other.t), eid(other.eid) {}

  const Tagged& element() const {
    return t;
  }

  int execution_id() const {
    return eid;
  }

  inline
  bool operator==(const execution_tag_t& other) const {
    return (eid == other.eid && t == other.t);
  }

  inline
  bool operator!=(const execution_tag_t& other) const {
    return !(*this == other);
  }

  friend std::ostream& operator<<(std::ostream& out, const execution_tag_t& t) {
    out << t.t << "@" << t.eid;
    return out;
  }

private:
  Tagged t;
  int eid;

};

struct stmt_visitor_t;

struct stmt_t {

  enum stmt_type_t {
    PI_ASSIGNMENT,
    LOCAL_ASSIGNMENT,
    GLOBAL_ASSIGNMENT,
    PHI_ASSIGNMENT,
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
  //ssa_variable_t shared_variable; // rhs
  //std::vector<tagged_variable_t> shared_variables; // rhs: made it a list to enable merging
  std::vector<execution_tag_t<ssa_variable_t>> shared_variables;

  pi_assignment_t() : stmt_t(PI_ASSIGNMENT) {}

  void accept(stmt_visitor_t& visitor) override;

  void print(std::ostream& out) const override;

};

struct phi_assignment_t : public stmt_t {
  ssa_variable_t variable; // lhs
  /* ... */

  phi_assignment_t() : stmt_t(PHI_ASSIGNMENT) {}

  void accept(stmt_visitor_t& visitor) override;

  void print(std::ostream& out) const override;

};

struct assertion_t : public stmt_t {

  std::vector<expr::expr_t<ssa_variable_t>> exprs;

  assertion_t() : stmt_t(ASSERTION) {}

  void accept(stmt_visitor_t& visitor) override;

  void print(std::ostream& out) const override;

};

struct assumption_t : public stmt_t {

  std::vector<expr::expr_t<ssa_variable_t>> exprs;

  assumption_t() : stmt_t(ASSUMPTION) {}

  void accept(stmt_visitor_t& visitor) override;

  void print(std::ostream& out) const override;

};

struct stmt_visitor_t {

  virtual void visit_pi_assignment(pi_assignment_t& a) = 0;
  virtual void visit_local_assignment(local_assignment_t& a) = 0;
  virtual void visit_global_assignment(global_assignment_t& a) = 0;
  virtual void visit_phi_assignment(phi_assignment_t& a) = 0;
  virtual void visit_assertion(assertion_t& a) = 0;
  virtual void visit_assumption(assumption_t& a) = 0;

};

}

#endif // ALPHABET_H_INCLUDED
