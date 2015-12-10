#ifndef EXECUTION2ALPHABET_H_INCLUDED
#define EXECUTION2ALPHABET_H_INCLUDED

#include "execution.h"
#include "alphabet.h"

#include <cassert>
#include <map>
#include <iostream>
#include <ostream>
#include <vector>

struct local_execution_extractor_t;

struct projected_execution_t {

  std::map<int, std::vector<alphabet::stmt_t*>> projections;

  projected_execution_t(exe::execution_t& e, int execution_id);
  ~projected_execution_t();

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

struct local_execution_extractor_t : public exe::stmt_visitor_t {

  local_execution_extractor_t(projected_execution_t& p, int id) : local_executions(p.projections), execution_id(id) {}

  std::map<int, std::vector<alphabet::stmt_t*>>& local_executions;
  int execution_id;

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
    // TODO should we reset data structures?
    variable_declarations.insert(variable_declarations.end(), e.variable_declarations.begin(), e.variable_declarations.end());

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
        pa->shared_variables.push_back({ vsubst.substitution_map[a.rhs.products[0].variable], execution_id });
        //pa->shared_variable = vsubst.substitution_map[a.rhs.products[0].variable];

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

    v.push_back((alphabet::stmt_t*)a_new);
  }

};

struct projected_executions_t {

  std::map<int, graph_t<int>> projections;
  std::map<int, std::vector< graph_t<int>::edge_t >> edges;

  projected_executions_t(const projected_execution_t& pexe, int execution_id) {
    // TODO execution_id has to be used in \pi nodes!
    for (auto& p : pexe.projections) {
      graph_t<int>& g = projections[p.first];
      size_t source = g.create_node();
      for (auto& s : p.second) {
        size_t target = g.create_node();
        edges[p.first].push_back(g.add_edge(source, s->program_location.position, target));
        source = target;
      }
    }
  }

  void merge(
    const exe::execution_t& e,
    std::function<bool (const graph_t<int>::edge_t&, const alphabet::stmt_t&)> is_mergable,
    std::function<void (const graph_t<int>::edge_t&, const alphabet::stmt_t&)> do_merge,
    int execution_id // TODO this has to be used in \pi nodes!
  ) {
    // TODO in the following code, stmts get freed when p gets out of scope!
#if 0
    alphabet::projected_execution_t p;
    local_execution_extractor_t lee(p);
    e.accept(lee);

    merge(p, is_mergable, do_merge, execution_id);
#endif
  }

  /*
    We assume that every symbol in the alphabet appears at most once in a word,
    that there is a total order over the symbols in the alphabet, and that in
    each word the symbols respect this order.
  */
  void merge(
    const projected_execution_t& pexe,
    std::function<bool (const graph_t<int>::edge_t&, const alphabet::stmt_t&)> is_mergable,
    std::function<void (const graph_t<int>::edge_t&, const alphabet::stmt_t&)> do_merge,
    int execution_id // TODO this has to be used in \pi nodes!
  ) {
    std::map< alphabet::stmt_t* , graph_t<int>::edge_t > merge_map;
    std::map< int, std::vector< graph_t<int>::edge_t >> new_edges;

    // determine merging points
    for (auto& p : pexe.projections) {
      size_t last_match = -1;
      for (auto& e : edges[p.first]) {
        for (size_t i = last_match + 1; i < p.second.size(); i++) {
          alphabet::stmt_t* s = p.second[i];
          if (is_mergable(e, *s)) {
            // store for later merging
            merge_map[s] = e;

            last_match = i;
            break;
          }
        }
      }
    }

    // merge
    for (auto& p : pexe.projections) {
      graph_t<int>& g = projections[p.first];
      if (g.empty()) {
        // new graph -> create initial node
        g.create_node();
      }

      size_t source = 0; // the 0-node is always our initial node

      for (size_t i = 0; i < p.second.size(); i++) {
        alphabet::stmt_t* s = p.second[i];
        auto it = merge_map.find(s);

        if (it == merge_map.end()) {
          // no merge
          std::cout << "no merge" << std::endl;

          bool target_set = false;
          size_t target;

          // check whether successor is getting merged
          if (i < p.second.size() - 1) {
            alphabet::stmt_t* next_s = p.second[i + 1];

            auto next_it = merge_map.find(next_s);

            if (next_it != merge_map.end()) {
              // next statement is getting merged
              target = next_it->second.source;
              target_set = true;
            }
          }

          if (!target_set) {
            target = g.create_node();
          }

          new_edges[p.first].push_back(g.add_edge(source, s->program_location.position, target));

          source = target;
        }
        else {
          // merge
          std::cout << "merge" << std::endl;
          do_merge(it->second, *s);

          // nothing to do except updating the target
          source = it->second.target;
        }
      }
    }

    // insert new_edges into edges
    for (auto& p : new_edges) {
      auto& v = edges[p.first];
      v.insert(v.end(), p.second.begin(), p.second.end());
    }
  }

  friend std::ostream& operator<<(std::ostream& out, const projected_executions_t ps) {
    out << "{" << std::endl;
    for (auto& p : ps.projections) {
      out << "thread " << p.first << ":" << std::endl;
      out << p.second << std::endl;
    }
    out << "}" << std::endl;

    return out;
  }

};

#endif // EXECUTION2ALPHABET_H_INCLUDED
