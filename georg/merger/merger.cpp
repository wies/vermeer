#include <cstdlib>
#include <iostream>

#include <map>
#include <set>
#include <vector>

#include "error.h"
#include "execution.h"
#include "xml.h"

#include "alphabet.h"

#include "expr.h"

#if 0
struct thread_id_t {

  const int unique_id;

  inline
  bool operator==(const thread_id_t& other) const {
    return unique_id == other.unique_id;
  }

  inline
  bool operator!=(const thread_id_t& other) const {
    return !(*this == other);
  }

  inline
  bool operator<(const thread_id_t& other) const {
    return unique_id < other.unique_id;
  }

};
#endif

struct local_execution_extractor_t : public exe::stmt_visitor_t {

  std::map<int, std::vector<alphabet::stmt_t*>> local_executions;
  std::vector<exe::variable_declaration_t> variable_declarations;

  std::map<int, std::map<int, int>> thread_local_ssa_indices;

  int get_ssa_index(int thread, int variable) {
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

  void set_ssa_index(int thread, int variable, int index) {
    thread_local_ssa_indices[thread][variable] = index;
  }


  expr::variable_substitution_t<int, alphabet::ssa_variable_t> vsubst;


  void visit_execution(exe::execution_t& e) override {
    for (auto& s : e.statements) {
      s->accept(*this);
    }
  }

  enum term_purity {

    CONSTANT_ONLY,
    LOCAL_ONLY,
    SHARED_ONLY,
    MIXED

  };

  term_purity determine_purity(expr::term_t<int> t) {

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

  void visit_assignment(exe::assignment_t& a) override {

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

    std::cout << *stmt << std::endl;

    v.push_back(stmt);

    set_ssa_index(a.program_location.thread, vd.variable, lhs_local_ssa_index + 1);

    alphabet::ssa_variable_t var;
    var.variable_id = vd.variable;
    var.ssa_index.thread_id = a.program_location.thread;
    var.ssa_index.thread_local_index = lhs_local_ssa_index + 1;
    vsubst.substitution_map[vd.id] = var;
  }

  void visit_assertion(exe::assertion_t& a) override {
    std::vector<alphabet::stmt_t*>& v = local_executions[a.program_location.thread];

    alphabet::assertion_t* a_new = new alphabet::assertion_t;

    for (auto& e : a.exprs) {
      a_new->exprs.push_back(e.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>, expr::expr_t<alphabet::ssa_variable_t>>(vsubst));
    }

    for (auto& e : a.guard.exprs) {
      a_new->guards.push_back(e.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>,expr::expr_t<alphabet::ssa_variable_t>>(vsubst));
    }

    a_new->program_location = a.program_location;

    std::cout << *a_new << std::endl;

    v.push_back((alphabet::stmt_t*)a_new);
  }

  void visit_assumption(exe::assumption_t& a) override {
    std::vector<alphabet::stmt_t*>& v = local_executions[a.program_location.thread];

    alphabet::assumption_t* a_new = new alphabet::assumption_t;

    for (auto& e : a.exprs) {
      a_new->exprs.push_back(e.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>, expr::expr_t<alphabet::ssa_variable_t>>(vsubst));
    }

    for (auto& e : a.guard.exprs) {
      a_new->guards.push_back(e.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>,expr::expr_t<alphabet::ssa_variable_t>>(vsubst));
    }

    a_new->program_location = a.program_location;

    std::cout << *a_new << std::endl;

    v.push_back((alphabet::stmt_t*)a_new);
  }

};

int main(int argc, char* argv[]) {
  exe::execution_t e = read_execution("example.xml");

  std::cout << e << std::endl;
  std::cout << "******************************************" << std::endl;

  local_execution_extractor_t lee;
  lee.variable_declarations.insert(lee.variable_declarations.end(), e.variable_declarations.begin(), e.variable_declarations.end()); // TODO replace
  e.accept(lee);

  for (auto& p : lee.local_executions) {
    std::cout << "Thread " << p.first << ": " << p.second.size() << std::endl;
  }

  return EXIT_SUCCESS;
}

