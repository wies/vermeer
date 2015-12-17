#include "execution2alphabet.h"

#include "alphabet.h"
#include "error.h"

#include <functional>
#include <ostream>
#include <map>
#include <vector>
#include <cassert>
#include <iostream>

// TODO make parameter e const! How to change accept?
projected_execution_t::projected_execution_t(exe::execution_t& e, int unique_id_) : unique_id(unique_id_) {
  local_execution_extractor_t lee(*this);
  e.accept(lee);
}

projected_execution_t::~projected_execution_t() {
  for (auto& p : projections) {
    for (auto& s : p.second) {
      delete s;
    }
  }
}

std::ostream& operator<<(std::ostream& out, const projected_execution_t& p) {
  for (auto& e : p.projections) {
    out << "Thread " << e.first << ": " << e.second.size() << std::endl;
    for (auto& s : e.second) {
      out << *s << std::endl;
    }
    out << std::endl;
  }

  return out;
}

local_execution_extractor_t::local_execution_extractor_t(projected_execution_t& p) : local_executions(p.projections), execution_id(p.unique_id) {}

int local_execution_extractor_t::get_ssa_index(int thread, int variable) {
  auto it_thread = thread_local_ssa_indices.find(thread);

  if (it_thread == thread_local_ssa_indices.end()) {
    return 0;
  }

  auto it_var = it_thread->second.find(variable);

  if (it_var == it_thread->second.end()) {
    return 0;
  }

  return it_var->second;
}

void local_execution_extractor_t::set_ssa_index(int thread, int variable, int index) {
  thread_local_ssa_indices[thread][variable] = index;
}

void local_execution_extractor_t::visit_execution(exe::execution_t& e) {
  // TODO should we reset data structures?
  variable_declarations.insert(variable_declarations.end(), e.variable_declarations.begin(), e.variable_declarations.end());

  for (auto& s : e.statements) {
    s->accept(*this);
  }
}

local_execution_extractor_t::term_purity local_execution_extractor_t::determine_purity(expr::term_t<int> t) {

  if (t.products.empty()) {
    return CONSTANT_ONLY;
  }

  bool saw_shared = false;
  bool saw_local = false;
  for (auto& p : t.products) {
    auto& vd = variable_declarations[p.variable];

    if (vd.thread < 0) {
      saw_shared = true;
    }
    else {
      saw_local = true;
    }
  }

  if (saw_shared) {
    if (!saw_local) {
      return SHARED_ONLY;
    }
    else {
      return MIXED;
    }
  }

  return LOCAL_ONLY;
}

void local_execution_extractor_t::visit_assignment(exe::assignment_t& a) {

  std::vector<alphabet::stmt_t*>& v = local_executions[a.program_location.thread];

  // a) is lhs a global variable?
   auto& vd = variable_declarations[a.variable_id];

  int lhs_local_ssa_index = get_ssa_index(a.program_location.thread, vd.variable);

  bool is_shared_var = (vd.thread < 0);

  auto purity = determine_purity(a.rhs);

  alphabet::stmt_t* stmt = nullptr;

  if (is_shared_var && purity != MIXED && purity != SHARED_ONLY) {
    // global assignment
    alphabet::global_assignment_t* ga = new alphabet::global_assignment_t;

    // we have to generate a ssa_variable_t:
    ga->shared_variable.variable_id = vd.variable;
    ga->shared_variable.ssa_index.thread_local_index = lhs_local_ssa_index + 1;
    ga->shared_variable.ssa_index.thread_id = a.program_location.thread;

    // substitute local variables
    ga->rhs = a.rhs.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>,expr::term_t<alphabet::ssa_variable_t>>(vsubst);

    stmt = (alphabet::stmt_t*)ga;
  }
  else if (!is_shared_var && purity != MIXED) {
    if (purity == SHARED_ONLY) {
      if (a.rhs.products.size() > 1 || a.rhs.products[0].factor != 1) {
        ERROR("Unhandled assignment!");
      }

      // pi assignment
      alphabet::pi_assignment_t* pa = new alphabet::pi_assignment_t;
      pa->local_variable.variable_id = vd.variable;
      pa->local_variable.ssa_index.thread_local_index = lhs_local_ssa_index + 1;
      pa->local_variable.ssa_index.thread_id = a.program_location.thread;
      pa->shared_variable = vsubst.substitution_map[a.rhs.products[0].variable];

      stmt = (alphabet::stmt_t*)pa;
    }
    else {
      // local assignment
      alphabet::local_assignment_t* la = new alphabet::local_assignment_t;

      la->local_variable.variable_id = vd.variable;
      la->local_variable.ssa_index.thread_local_index = lhs_local_ssa_index + 1;
      la->local_variable.ssa_index.thread_id = a.program_location.thread;

      // substitute local variables
      la->rhs = a.rhs.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>,expr::term_t<alphabet::ssa_variable_t>>(vsubst);

      stmt = (alphabet::stmt_t*)la;
    }
  }
  else {
    ERROR("Unhandled assignment!");
  }

  assert(stmt);

  stmt->program_location = a.program_location;

  for (auto& e : a.guard.exprs) {
    stmt->guards.push_back(e.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>,expr::expr_t<alphabet::ssa_variable_t>>(vsubst));
  }

  v.push_back(stmt);

  set_ssa_index(a.program_location.thread, vd.variable, lhs_local_ssa_index + 1);

  alphabet::ssa_variable_t var;
  var.variable_id = vd.variable;
  var.ssa_index.thread_id = a.program_location.thread;
  var.ssa_index.thread_local_index = lhs_local_ssa_index + 1;
  vsubst.substitution_map[vd.id] = var;
}

void local_execution_extractor_t::visit_assertion(exe::assertion_t& a) {
  std::vector<alphabet::stmt_t*>& v = local_executions[a.program_location.thread];

  alphabet::assertion_t* a_new = new alphabet::assertion_t;

  for (auto& e : a.exprs) {
    a_new->exprs.push_back(e.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>, expr::expr_t<alphabet::ssa_variable_t>>(vsubst));
  }

  for (auto& e : a.guard.exprs) {
    a_new->guards.push_back(e.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>,expr::expr_t<alphabet::ssa_variable_t>>(vsubst));
  }

  a_new->program_location = a.program_location;

  v.push_back((alphabet::stmt_t*)a_new);
}

void local_execution_extractor_t::visit_assumption(exe::assumption_t& a) {
  std::vector<alphabet::stmt_t*>& v = local_executions[a.program_location.thread];

  alphabet::assumption_t* a_new = new alphabet::assumption_t;

  for (auto& e : a.exprs) {
    a_new->exprs.push_back(e.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>, expr::expr_t<alphabet::ssa_variable_t>>(vsubst));
  }

  for (auto& e : a.guard.exprs) {
    a_new->guards.push_back(e.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>,expr::expr_t<alphabet::ssa_variable_t>>(vsubst));
  }

  a_new->program_location = a.program_location;

  v.push_back((alphabet::stmt_t*)a_new);
}
