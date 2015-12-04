#include <cstdlib>
#include <iostream>

#include <map>
#include <set>
#include <vector>

#include "error.h"
#include "trace.h"
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

struct thread_local_position_t {
  //thread_id_t thread;
  int thread;
  int position;

  friend std::ostream& operator<<(std::ostream& out, const thread_local_position_t p) {
    out << "(T" << p.thread << ",P" << p.position << ")";
    return out;
  }
};

#if 0
std::set<int> extract_variables(const exe::expression_t& e) {
  std::set<int> variable_ids;

  for (const exe::linear_product_t& p : e.term.products) {
    variable_ids.insert(p.variable_id);
  }

  return variable_ids;
}
#endif

#if 0
std::vector<thread_local_position_t> extract_thread_local_positions(const exe::execution_t& e) {
  std::vector<thread_local_position_t> v;

  // thread_id x thread-local position
  std::map<int, int> thread_local_counters;

  // variable_id x global position
  std::map<int, int> variable_definitions;

  // variable_id x set of global positions
  std::map<int, std::set<int> > variable_uses;

  // TODO do we assume that statements are ordered according to their position attribute?
  for (auto const& s : e.statements) {
    int pos = thread_local_counters[s->thread];
    v.push_back({ s->thread, pos });
    thread_local_counters[s->thread] = pos + 1;

    // track variable definition
    if (s->type == exe::ASSIGNMENT) {
      variable_definitions[s->variable_id] = s->position;
      std::cout << "Variable " << s->variable_id << " is defined at " << v[variable_definitions[s->variable_id]] << std::endl;
    }

    // track variable usage
    // a) guards
    std::set<int> variable_ids;
    for (auto const& e : s->guard.exprs) {
      auto var_ids = extract_variables(e);
      variable_ids.insert(var_ids.begin(), var_ids.end());
    }

    // b) variables in other expressions
    switch (s->type) {
      case exe::ASSIGNMENT:
        for (auto const& p : s->rhs.products) {
          if (e.variable_declarations[p.variable_id].thread < 0) { // global variable
            std::cout << "G" << p.variable_id;
          }
          variable_ids.insert(p.variable_id);
        }
        break;
      case exe::ASSERTION:
      case exe::ASSUMPTION:
        for (auto const& e : s->exprs) {
          auto var_ids = extract_variables(e);
          variable_ids.insert(var_ids.begin(), var_ids.end());
        }
        break;
    }

    for (int var_id : variable_ids) {
      if (e.variable_declarations[var_id].thread < 0) { // global variable
        std::cout << "g";
      }
      std::cout << var_id << " ";
    }
    std::cout << std::endl;
  }

  for (auto const& p : variable_uses) {
    std::cout << p.first << std::endl;
  }

  return v;
}
#endif

struct local_execution_extractor_t : public exe::stmt_visitor_t {

  std::map<int, std::vector<alphabet::stmt_t*>> local_executions;
  std::vector<exe::variable_declaration_t> variable_declarations;


  std::map<int, alphabet::ssa_variable_t> last_definition;

  alphabet::ssa_variable_t get_last_definition(int variable) {
    return last_definition[variable];
  }

  void set_last_definition(int variable, alphabet::ssa_variable_t& v) {
    last_definition[variable] = v;
  }


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

    std::vector<alphabet::stmt_t*>& v = local_executions[a.thread];

    // a) is lhs a global variable?
    auto& vd = variable_declarations[a.variable_id];

    int lhs_local_ssa_index = get_ssa_index(a.thread, vd.variable);

    bool is_shared_var = (vd.thread < 0);

    auto purity = determine_purity(a.rhs);

    alphabet::stmt_t* stmt = nullptr;

    if (is_shared_var && purity != MIXED && purity != SHARED_ONLY) {
      // global assignment
      alphabet::global_assignment_t* ga = new alphabet::global_assignment_t;

      // we have to generate a ssa_variable_t:
      ga->shared_variable.variable_id = vd.variable;
      ga->shared_variable.ssa_index.thread_local_index = lhs_local_ssa_index + 1;
      ga->shared_variable.ssa_index.thread_id = a.thread;

      // TODO eliminate vd.variable parameter?
      // TODO do we need this function at all?
      set_last_definition(vd.variable, ga->shared_variable);

      // substitute local variables
      ga->rhs = a.rhs.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>,expr::term_t<alphabet::ssa_variable_t>>(vsubst);
      std::cout << *ga << std::endl;

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
        pa->local_variable.ssa_index.thread_id = a.thread;
        pa->shared_variable = get_last_definition(a.rhs.products[0].variable);

        std::cout << *pa << std::endl;

        stmt = (alphabet::stmt_t*)pa;
      }
      else {
        // local assignment
        alphabet::local_assignment_t* la = new alphabet::local_assignment_t;

        la->local_variable.variable_id = vd.variable;
        la->local_variable.ssa_index.thread_local_index = lhs_local_ssa_index + 1;
        la->local_variable.ssa_index.thread_id = a.thread;

        // substitute local variables
        la->rhs = a.rhs.accept<expr::variable_substitution_t<int, alphabet::ssa_variable_t>,expr::term_t<alphabet::ssa_variable_t>>(vsubst);
        std::cout << *la << std::endl;

        stmt = (alphabet::stmt_t*)la;
      }
    }
    else {
      ERROR("Unhandled assignment!");
    }

    assert(stmt);
    v.push_back(stmt);

    set_ssa_index(a.thread, vd.variable, lhs_local_ssa_index + 1);

    alphabet::ssa_variable_t var;
    var.variable_id = vd.variable;
    var.ssa_index.thread_id = a.thread;
    var.ssa_index.thread_local_index = lhs_local_ssa_index + 1;
    vsubst.substitution_map[vd.id] = var;
  }

  void visit_assertion(exe::assertion_t& a) override {
    std::vector<alphabet::stmt_t*>& v = local_executions[a.thread];
    v.push_back((alphabet::stmt_t*)new alphabet::local_assignment_t);

    //ERROR("I cannot handle this case for the moment");
    std::cout << "thread: " << a.thread << std::endl;
  }

  void visit_assumption(exe::assumption_t& a) override {
    std::vector<alphabet::stmt_t*>& v = local_executions[a.thread];
    v.push_back((alphabet::stmt_t*)new alphabet::local_assignment_t);

    //ERROR("I cannot handle this case for the moment");
    std::cout << "thread: " << a.thread << std::endl;
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

#if 0
  auto pos = extract_thread_local_positions(e);

  for (auto const& p : pos) {
    std::cout << p << std::endl;
  }
#endif

  return EXIT_SUCCESS;
}

