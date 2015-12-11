#include "alphabet.h"

#include "program_location.h"
#include "graph.h"
#include "expr.h"

#include <functional>
#include <iostream>
#include <vector>

namespace alphabet {

std::ostream& operator<<(std::ostream& out, const ssa_variable_t& v) {
  out << "var(" << v.variable_id << ")_{T" << v.ssa_index.thread_id << "," << v.ssa_index.thread_local_index << "}";
  return out;
}

std::ostream& operator<<(std::ostream& out, const stmt_t::stmt_type_t t) {
  switch (t) {
    case stmt_t::PI_ASSIGNMENT:
      out << "PI_ASSIGNMENT";
      break;
    case stmt_t::LOCAL_ASSIGNMENT:
      out << "LOCAL_ASSIGNMENT";
      break;
    case stmt_t::GLOBAL_ASSIGNMENT:
      out << "GLOBAL_ASSIGNMENT";
      break;
    case stmt_t::PHI_ASSIGNMENT:
      out << "PHI_ASSIGNMENT";
      break;
    case stmt_t::ASSERTION:
      out << "ASSERTION";
      break;
    case stmt_t::ASSUMPTION:
      out << "ASSUMPTION";
      break;
  }
  return out;
}

void stmt_t::print_guards(std::ostream& out) const {
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

std::ostream& operator<<(std::ostream& out, const stmt_t& s) {
  out << s.program_location << ": ";
  s.print_guards(out);
  s.print(out);
  return out;
}

void local_assignment_t::accept(stmt_visitor_t& visitor) {
  visitor.visit_local_assignment(*this);
}

void local_assignment_t::print(std::ostream& out) const {
  out << local_variable << " := " << rhs;
}

void pi_assignment_t::accept(stmt_visitor_t& visitor) {
  visitor.visit_pi_assignment(*this);
}

void pi_assignment_t::print(std::ostream& out) const {
  out << local_variable << " := pi(";
  for (auto& v : shared_variables) {
    out << v << ",";
  }
  out << ")";
}

void pi_assignments_t::accept(stmt_visitor_t& visitor) {
  ERROR("Unsupported operation");
}

void pi_assignments_t::print(std::ostream& out) const {
  ERROR("Unsupported operation");
}

void global_assignment_t::accept(stmt_visitor_t& visitor) {
  visitor.visit_global_assignment(*this);
}

void global_assignment_t::print(std::ostream& out) const {
  out << shared_variable << " := " << rhs;
}

void phi_assignment_t::accept(stmt_visitor_t& visitor) {
  visitor.visit_phi_assignment(*this);
}

void phi_assignment_t::print(std::ostream& out) const {
  out << "phi(...)";
}

void assertion_t::accept(stmt_visitor_t& visitor) {
  visitor.visit_assertion(*this);
}

void assertion_t::print(std::ostream& out) const {
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

void assumption_t::accept(stmt_visitor_t& visitor) {
  visitor.visit_assumption(*this);
}

void assumption_t::print(std::ostream& out) const {
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

}
