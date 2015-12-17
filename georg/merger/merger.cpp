#include <cstdlib>
#include <iostream>

#include <cassert>
#include <map>
#include <set>
#include <vector>

#include "error.h"
#include "execution.h"
#include "xml.h"
#include "alphabet.h"
#include "expr.h"
#include "execution2alphabet.h"
#include "tag.h"

#include "projected_executions.h"

#include "ssa_map.h"

struct ssa_extractor_t : public alphabet::stmt_visitor_t {

  int variable_to_be_updated;
  bool do_update;

  void visit_pi_assignment(alphabet::pi_assignment_t& a) {
    variable_to_be_updated = a.local_variable.variable_id;
    do_update = true;
  }

  void visit_local_assignment(alphabet::local_assignment_t& a) {
    variable_to_be_updated = a.local_variable.variable_id;
    do_update = true;
  }

  void visit_global_assignment(alphabet::global_assignment_t& a) {
    //variable_to_be_updated = a.shared_variable.variable_id;
    //do_update = true;
    do_update = false; // we handle shared variables separately
  }

  void visit_phi_assignment(alphabet::phi_assignment_t& a) {
    ERROR("Unsupported statement!");
  }

  void visit_assertion(alphabet::assertion_t& a) {
    do_update = false;
  }

  void visit_assumption(alphabet::assumption_t& a) {
    do_update = false;
  }

};

void update_edge2map_map(
  size_t node,
  /*const*/ graph_t< size_t > g,
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts,
  const std::map<size_t /* i.e., node*/, ssa_map_t>& node2map,
  std::map<const graph_t<size_t>::edge_t, ssa_map_t>& edge2map
) {
  const auto& m = node2map.find(node)->second; // TODO we assume that a node always has an assigned map, implement more devensively?

  // for each outgoing edge from root create an ssa map and store in edge2map
  for (const graph_t<size_t>::edge_t& edge : g.outgoing_edges(node)) { // TODO outgoing_edges does not allow const -> change!
    ssa_map_t new_ssa_map(m);

    // TODO remove the cast!
    alphabet::stmt_t* s = (alphabet::stmt_t*)set_of_merged_stmts[edge.label][0].element();
    ssa_extractor_t ext;
    s->accept(ext);

    if (ext.do_update) {
      new_ssa_map.inc(ext.variable_to_be_updated);
    }

    edge2map.insert({ edge, new_ssa_map });
  }
}

void update_edge2map_map2(
  int thread_id,
  size_t node,
  /*const*/ graph_t< size_t > g,
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts,
  const std::map<size_t /* i.e., node*/, ssa_map_t>& node2map,
  std::map<const graph_t<size_t>::edge_t, ssa_map_t>& edge2map,
  id_partitioned_substitution_maps_t& local_subst_map
) {
  const auto& m = node2map.find(node)->second; // TODO we assume that a node always has an assigned map, implement more devensively?

  // for each outgoing edge from root create an ssa map and store in edge2map
  for (const graph_t<size_t>::edge_t& edge : g.outgoing_edges(node)) { // TODO outgoing_edges does not allow const -> change!
    ssa_map_t new_ssa_map(m);

    const alphabet::stmt_t* s = set_of_merged_stmts[edge.label][0].element();
    if (s->type == alphabet::stmt_t::LOCAL_ASSIGNMENT) {
      const alphabet::local_assignment_t* loc_s = (const alphabet::local_assignment_t*)s;
      new_ssa_map.inc(loc_s->local_variable.variable_id);

      for (const auto& t : set_of_merged_stmts[edge.label]) {
        const alphabet::local_assignment_t* other_s = (const alphabet::local_assignment_t*)t.element();

        alphabet::ssa_variable_t ssa_var;
        ssa_var.variable_id = other_s->local_variable.variable_id;
        ssa_var.ssa_index.thread_id = thread_id;
        ssa_var.ssa_index.thread_local_index = m[other_s->local_variable.variable_id];

        local_subst_map.map_to(t.execution_id(), other_s->local_variable, ssa_var);
      }
    }
    else if (s->type == alphabet::stmt_t::PI_ASSIGNMENT) {
      const alphabet::pi_assignment_t* loc_s = (const alphabet::pi_assignment_t*)s;
      new_ssa_map.inc(loc_s->local_variable.variable_id);

      for (const auto& t : set_of_merged_stmts[edge.label]) {
        const alphabet::pi_assignment_t* other_s = (const alphabet::pi_assignment_t*)t.element();

        alphabet::ssa_variable_t ssa_var;
        ssa_var.variable_id = other_s->local_variable.variable_id;
        ssa_var.ssa_index.thread_id = thread_id;
        ssa_var.ssa_index.thread_local_index = m[other_s->local_variable.variable_id];

        local_subst_map.map_to(t.execution_id(), other_s->local_variable, ssa_var);
      }
    }

    edge2map.insert({ edge, new_ssa_map });
  }
}

alphabet::stmt_t* unify_statements(const std::vector< execution_tag_t< const alphabet::stmt_t* > >& stmts) {
  assert(stmts.size() > 0);

  alphabet::stmt_t::stmt_type_t type = stmts[0].element()->type;
  for (size_t i = 0; i < stmts.size(); ++i) {
    assert(stmts[i].element()->type == type);
  }

  alphabet::stmt_t* s = nullptr;

  switch (type) {
    case alphabet::stmt_t::PI_ASSIGNMENT:
      s = new alphabet::pi_assignment_t;
      break;
    case alphabet::stmt_t::LOCAL_ASSIGNMENT:
      s = new alphabet::local_assignment_t;
      break;
    case alphabet::stmt_t::GLOBAL_ASSIGNMENT:
      s = new alphabet::global_assignment_t;
      break;
    case alphabet::stmt_t::ASSERTION:
      s = new alphabet::assertion_t;
      break;
    case alphabet::stmt_t::ASSUMPTION:
      s = new alphabet::assumption_t;
      break;
    default:
      break;
  }

  return s;
}

id_partitioned_substitution_maps_t extract_sharedvar_substmap(
  alternative::projected_executions_t<size_t>& pexes,
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts
) {

  id_partitioned_substitution_maps_t sharedvar_substmap;

  for (auto& it : pexes.projections) {
    graph_t< size_t >& g = it.second;
    auto order = g.dag_topological_sort(0);
    assert(order.size() > 0);

    using varid_t = int;
    std::map< varid_t, unsigned > sharedvar_counters;

    for (size_t node : order) {
      for (const auto& e : g.outgoing_edges(node)) {
        const auto& stmts = set_of_merged_stmts[e.label];
        const auto& first_stmt = stmts[0].element();

        if (first_stmt->type == alphabet::stmt_t::GLOBAL_ASSIGNMENT) {
          const alphabet::global_assignment_t* s = (const alphabet::global_assignment_t*)first_stmt;

          int var_id = s->shared_variable.variable_id;
          int counter = sharedvar_counters[var_id];
          sharedvar_counters[var_id] = counter + 1;

          alphabet::ssa_variable_t ssa_var;
          ssa_var.variable_id = var_id;
          ssa_var.ssa_index.thread_id = it.first;
          ssa_var.ssa_index.thread_local_index = counter;

          // we assume that all statements in stmts are global assignments
          for (const auto& stmt : stmts) {
            const alphabet::global_assignment_t* a = (const alphabet::global_assignment_t*)stmt.element();
            sharedvar_substmap.map_to(stmt.execution_id(), a->shared_variable, ssa_var);
          }
        }
      }
    }
  }

  return sharedvar_substmap;
}

id_partitioned_substitution_maps_t extract_localvar_substmap(
  alternative::projected_executions_t<size_t>& pexes,
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts
) {

  id_partitioned_substitution_maps_t localvar_substmap;

  using node_t = size_t;
  std::map< int, std::map<node_t, ssa_map_t> > thread2_node2ssa_map;
  std::map< int, std::map<const graph_t<node_t>::edge_t, ssa_map_t> > thread2_edge2ssa_map;

  // create ssa maps
  for (auto& it : pexes.projections) {
    graph_t< node_t >& g = it.second;
    auto order = g.dag_topological_sort(0);
    assert(order.size() > 0);

    std::map<node_t, ssa_map_t>& node2map = thread2_node2ssa_map[it.first];
    ssa_map_t empty_map;
    node2map.insert({ 0, empty_map });

    std::map<const graph_t<node_t>::edge_t, ssa_map_t>& edge2map = thread2_edge2ssa_map[it.first];

    update_edge2map_map2(it.first, 0, g, set_of_merged_stmts, node2map, edge2map, localvar_substmap);

    for (size_t i = 1; i < order.size(); ++i) {
      node_t node = order[i];

      // unify ssa maps of incoming edges to node in edge2map
      std::set<int> touched_variables;
      for (const auto& e : g.incoming_edges(node)) {
        const auto& m = edge2map[e];
        auto vars = m.variables();
        touched_variables.insert(vars.begin(), vars.end());
      }

      ssa_map_t unified_map;
      for (int v : touched_variables) {
        int max_value = 0;

        for (const auto& e : g.incoming_edges(node)) {
          const auto& m = edge2map[e];
          if (max_value < m[v]) {
            max_value = m[v];
          }
        }

        unified_map.set_value(v, max_value);
      }

      node2map.insert({ node, unified_map });

      update_edge2map_map2(it.first, node, g, set_of_merged_stmts, node2map, edge2map, localvar_substmap);
    }
  }

  return localvar_substmap;
}

std::vector< alphabet::stmt_t* > unify_statements(
  alternative::projected_executions_t<size_t>& pexes,
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts,
  const id_partitioned_substitution_maps_t& sharedvar_substmap,
  const id_partitioned_substitution_maps_t& localvar_substmap
) {
  std::vector< alphabet::stmt_t* > unified_stmts;

  for (const auto& v : set_of_merged_stmts) {
    // TODO we have to determine for which execution id's we get the same statements
    std::set< alphabet::stmt_t* > set_of_stmts; // TODO this will not be enough

    for (const auto& t : v) {
      int execution_id = t.execution_id();
      alphabet::stmt_t* s = (alphabet::stmt_t*)t.element(); // TODO remove cast!

      expr::variable_substitution_t< alphabet::ssa_variable_t, alphabet::ssa_variable_t > subst_visitor;

      auto it = localvar_substmap.id_partitioned_substitution_maps.find(execution_id);
      assert(it != localvar_substmap.id_partitioned_substitution_maps.end());
      subst_visitor.substitution_map.insert(it->second.begin(), it->second.end());

      // TODO for assertions, assumptions, etc. we should not have to insert the shared variable substitutions for guards! We have to change the runtime system!
      auto shared_it = sharedvar_substmap.id_partitioned_substitution_maps.find(execution_id);
      assert(shared_it != sharedvar_substmap.id_partitioned_substitution_maps.end());
      subst_visitor.substitution_map.insert(shared_it->second.begin(), shared_it->second.end());

      // TODO add content of new_guards into guards of the new statement
      alphabet::stmt_t* new_stmt = nullptr;

      switch (s->type) {
      case alphabet::stmt_t::ASSERTION:
        {
          alphabet::assertion_t* s_as = (alphabet::assertion_t*)s;

          alphabet::assertion_t* new_tmp_stmt = new alphabet::assertion_t;

          std::cout << "Translating assertion: " << std::endl;
          for (auto& expr : s_as->exprs) {
            std::cout << "  Old expression: " << expr << std::endl;

            // TODO We again have the problem of global variables in the expression!
            expr::expr_t< alphabet::ssa_variable_t > new_expr = expr.accept< expr::variable_substitution_t< alphabet::ssa_variable_t, alphabet::ssa_variable_t >, expr::expr_t< alphabet::ssa_variable_t > >(subst_visitor);

            std::cout << "  New expression: " << new_expr << std::endl;

            new_tmp_stmt->exprs.push_back(new_expr);
          }

          new_stmt = (alphabet::stmt_t*)new_tmp_stmt;

          break;
        }
      case alphabet::stmt_t::ASSUMPTION:
        {
          alphabet::assumption_t* s_as = (alphabet::assumption_t*)s;

          alphabet::assumption_t* new_tmp_stmt = new alphabet::assumption_t;

          std::cout << "Translating assumption: " << std::endl;
          for (auto& expr : s_as->exprs) {
            std::cout << "  Old expression: " << expr << std::endl;

            expr::expr_t< alphabet::ssa_variable_t > new_expr = expr.accept< expr::variable_substitution_t< alphabet::ssa_variable_t, alphabet::ssa_variable_t >, expr::expr_t< alphabet::ssa_variable_t > >(subst_visitor);

            std::cout << "  New expression: " << new_expr << std::endl;

            new_tmp_stmt->exprs.push_back(new_expr);
          }

          new_stmt = (alphabet::stmt_t*)new_tmp_stmt;

          break;
        }
      case alphabet::stmt_t::LOCAL_ASSIGNMENT:
        {
          alphabet::local_assignment_t* s_la = (alphabet::local_assignment_t*)s;

          alphabet::local_assignment_t* new_tmp_stmt = new alphabet::local_assignment_t;

          auto local_it = localvar_substmap.id_partitioned_substitution_maps.find(execution_id);
          assert(local_it != localvar_substmap.id_partitioned_substitution_maps.end());
          auto var_it = local_it->second.find(s_la->local_variable);
          assert(var_it != local_it->second.end());

          new_tmp_stmt->local_variable = var_it->second;

          std::cout << "Translating local assignment: " << std::endl;
          std::cout << "  Old local variable: " << s_la->local_variable << std::endl;
          std::cout << "  New local variable: " << new_tmp_stmt->local_variable << std::endl;

          new_tmp_stmt->rhs = s_la->rhs.accept< expr::variable_substitution_t< alphabet::ssa_variable_t, alphabet::ssa_variable_t >, expr::term_t< alphabet::ssa_variable_t > >(subst_visitor);

          std::cout << "  Old rhs: " << s_la->rhs << std::endl;
          std::cout << "  New rhs: " << new_tmp_stmt->rhs << std::endl;

          new_stmt = (alphabet::stmt_t*)new_tmp_stmt;

          break;
        }
      case alphabet::stmt_t::GLOBAL_ASSIGNMENT:
        {
          alphabet::global_assignment_t* s_ga = (alphabet::global_assignment_t*)s;

          alphabet::global_assignment_t* new_tmp_stmt = new alphabet::global_assignment_t;

          auto shared_it = sharedvar_substmap.id_partitioned_substitution_maps.find(execution_id);
          assert(shared_it != sharedvar_substmap.id_partitioned_substitution_maps.end());
          auto var_it = shared_it->second.find(s_ga->shared_variable);
          assert(var_it != shared_it->second.end());

          new_tmp_stmt->shared_variable = var_it->second;

          std::cout << "Translating shared assignment: " << std::endl;
          std::cout << "  Old shared variable: " << s_ga->shared_variable << std::endl;
          std::cout << "  New shared variable: " << new_tmp_stmt->shared_variable << std::endl;

          new_tmp_stmt->rhs = s_ga->rhs.accept< expr::variable_substitution_t< alphabet::ssa_variable_t, alphabet::ssa_variable_t >, expr::term_t< alphabet::ssa_variable_t > >(subst_visitor);

          std::cout << "  Old rhs: " << s_ga->rhs << std::endl;
          std::cout << "  New rhs: " << new_tmp_stmt->rhs << std::endl;

          new_stmt = (alphabet::stmt_t*)new_tmp_stmt;

          break;
        }
      case alphabet::stmt_t::PI_ASSIGNMENT:
        {
          alphabet::pi_assignment_t* s_pi = (alphabet::pi_assignment_t*)s;

          alphabet::pi_assignment_t* new_tmp_stmt = new alphabet::pi_assignment_t;

          std::cout << "Translating pi assignment: " << std::endl;

          auto local_it = localvar_substmap.id_partitioned_substitution_maps.find(execution_id);
          assert(local_it != localvar_substmap.id_partitioned_substitution_maps.end());
          auto var_it = local_it->second.find(s_pi->local_variable);
          assert(var_it != local_it->second.end());

          new_tmp_stmt->local_variable = var_it->second;

          std::cout << "  Old local variable: " << s_pi->local_variable << std::endl;
          std::cout << "  New local variable: " << new_tmp_stmt->local_variable << std::endl;

          auto shared_it = sharedvar_substmap.id_partitioned_substitution_maps.find(execution_id);
          assert(shared_it != sharedvar_substmap.id_partitioned_substitution_maps.end());
          auto shared_var_it = shared_it->second.find(s_pi->shared_variable);
          assert(shared_var_it != shared_it->second.end());

          new_tmp_stmt->shared_variable = shared_var_it->second;

          std::cout << "  Old shared variable: " << s_pi->shared_variable << std::endl;
          std::cout << "  New shared variable: " << new_tmp_stmt->shared_variable << std::endl;

          new_stmt = (alphabet::stmt_t*)new_tmp_stmt;

          break;
        }
      default:
        ERROR("Unsupported statement!");
        break;
      }

      assert(new_stmt);

      std::cout << "translating guards..." << std::endl;
      std::vector< expr::expr_t< alphabet::ssa_variable_t > > new_guards;
      for (auto& g : s->guards) {
        std::cout << "  Old guard: " << g << std::endl;

        // TODO shared variables in guards will definitely generate a problem! We do not have an explicit tracking of such data flow!
        // TODO problem: we have shared variables in our guards! That should not be the case!
        expr::expr_t< alphabet::ssa_variable_t > new_guard = g.accept< expr::variable_substitution_t< alphabet::ssa_variable_t, alphabet::ssa_variable_t >, expr::expr_t< alphabet::ssa_variable_t > >(subst_visitor);
        new_stmt->guards.push_back(new_guard);

        std::cout << "  New guard: " << new_guard << std::endl;
      }

      bool already_contained = false;
      for (auto& s : set_of_stmts) {
        switch (s->type) {
        case alphabet::stmt_t::ASSERTION:
          {
            alphabet::assertion_t* s2 = (alphabet::assertion_t*)s;
            alphabet::assertion_t* new_s2 = (alphabet::assertion_t*)new_stmt;

            if (*s2 == *new_s2) {
              already_contained = true;
            }

            break;
          }
        case alphabet::stmt_t::ASSUMPTION:
          {
            alphabet::assumption_t* s2 = (alphabet::assumption_t*)s;
            alphabet::assumption_t* new_s2 = (alphabet::assumption_t*)new_stmt;

            if (*s2 == *new_s2) {
              already_contained = true;
            }

            break;
          }
        case alphabet::stmt_t::LOCAL_ASSIGNMENT:
          {
            alphabet::local_assignment_t* s2 = (alphabet::local_assignment_t*)s;
            alphabet::local_assignment_t* new_s2 = (alphabet::local_assignment_t*)new_stmt;

            if (*s2 == *new_s2) {
              already_contained = true;
            }

            break;
          }
        case alphabet::stmt_t::GLOBAL_ASSIGNMENT:
          {
            alphabet::global_assignment_t* s2 = (alphabet::global_assignment_t*)s;
            alphabet::global_assignment_t* new_s2 = (alphabet::global_assignment_t*)new_stmt;

            if (*s2 == *new_s2) {
              already_contained = true;
            }

            break;
          }
        case alphabet::stmt_t::PI_ASSIGNMENT:
          {
            alphabet::pi_assignment_t* s2 = (alphabet::pi_assignment_t*)s;
            alphabet::pi_assignment_t* new_s2 = (alphabet::pi_assignment_t*)new_stmt;

            if (*s2 == *new_s2) {
              already_contained = true;
            }

            break;
          }
        default:
          break;
        }

        if (already_contained) {
          break;
        }

#if 0
        if (*s == *new_stmt) { // TODO make this possible
          std::cout << "Generated an equivalent statement!" << std::endl;
        }
#endif
      }

      if (!already_contained) {
        set_of_stmts.insert(new_stmt);
      }
      else {
        std::cout << "Generated an equivalent statement!" << std::endl;
      }
    }

    std::cout << "set_of_stmts.size() = " << set_of_stmts.size() << std::endl << std::endl;

    // TODO insert statement into unified_stmts
    assert(!set_of_stmts.empty());

    // TODO Resolve nondeterminism!
    // TODO Resolve pi assignments!
    unified_stmts.push_back(*set_of_stmts.begin());
  }

  return unified_stmts;
}

std::pair< alternative::projected_executions_t< size_t >, std::vector< alphabet::stmt_t* > >
unify(
  alternative::projected_executions_t<size_t>& pexes,
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts,
  const std::set<int>& shared_variables
) {

  alternative::projected_executions_t< size_t > unified_pes;

  // substitution map for global variables
  id_partitioned_substitution_maps_t sharedvar_substmap = extract_sharedvar_substmap(pexes, set_of_merged_stmts);
  // substitution map for local variables
  id_partitioned_substitution_maps_t localvar_substmap = extract_localvar_substmap(pexes, set_of_merged_stmts);

  auto v_unified = unify_statements(pexes, set_of_merged_stmts, sharedvar_substmap, localvar_substmap);

  // TODO update unified_pes
  return { unified_pes, v_unified };
}

int main(int argc, char* argv[]) {
  exe::execution_t s_destination = read_execution("example.xml");
  std::cout << s_destination << std::endl << "******************************************" << std::endl;

  projected_execution_t p(s_destination, 0);
  std::cout << p << std::endl << "******************************************" << std::endl;

  exe::execution_t e_dummy = read_execution("example_dummy.xml");
  projected_execution_t p_dummy(e_dummy, 1);

  exe::execution_t e_dummy2 = read_execution("example_dummy2.xml");
  projected_execution_t p_dummy2(e_dummy2, 2);

  using label_type2 = size_t;
  std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > > set_of_merged_stmts;

  alternative::projected_executions_t< label_type2 > p_alt2;
  auto is_mergable = [&] (const label_type2& v, const alphabet::stmt_t& s) {
    const alphabet::stmt_t& s_destination = *(set_of_merged_stmts[v].front().element());

    if (s_destination.program_location == s.program_location) {
      // can we assume that we have the same type of statement at the same program location?
      assert(s_destination.type == s.type);

      // check guards
      if (s_destination.guards.size() != s.guards.size()) {
        return false;
      }

      for (size_t i = 0; i < s.guards.size(); i++) {
        if (s_destination.guards[i] != s.guards[i]) {
          return false;
        }
      }

      // do further equality checks
      switch (s.type) {
        case alphabet::stmt_t::PI_ASSIGNMENT:
          {
            const alphabet::pi_assignment_t& ls = (const alphabet::pi_assignment_t&)s_destination;
            const alphabet::pi_assignment_t& ss = (const alphabet::pi_assignment_t&)s;

            return (ls.local_variable == ss.local_variable);
          }
        case alphabet::stmt_t::LOCAL_ASSIGNMENT:
          {
            const alphabet::local_assignment_t& ls = (const alphabet::local_assignment_t&)s_destination;
            const alphabet::local_assignment_t& ss = (const alphabet::local_assignment_t&)s;

            return (ls.local_variable == ss.local_variable);
          }
        case alphabet::stmt_t::GLOBAL_ASSIGNMENT:
          {
            const alphabet::global_assignment_t& ls = (const alphabet::global_assignment_t&)s_destination;
            const alphabet::global_assignment_t& ss = (const alphabet::global_assignment_t&)s;

            return (ls.shared_variable == ss.shared_variable);
          }
        default:
          // TODO implement other equality checks
          break;
      }

      return true;
    }

    return false;
  };

  auto do_merge = [&] (label_type2& l, const alphabet::stmt_t& s_source, const projected_execution_t& pexe) {
    auto& v = set_of_merged_stmts[l];
    v.emplace(v.end(), &s_source, pexe.unique_id);
  };

  auto create_label = [&] (const alphabet::stmt_t& s, const projected_execution_t& pexe) {
    auto it = set_of_merged_stmts.emplace(set_of_merged_stmts.end());
    it->emplace(it->end(), &s, pexe.unique_id);
    return set_of_merged_stmts.size() - 1;
  };

  p_alt2.merge(p, is_mergable, do_merge, create_label);
  std::cout << "***************************" << std::endl;
  p_alt2.merge(p_dummy, is_mergable, do_merge, create_label);
  std::cout << "***************************" << std::endl;
  p_alt2.merge(p_dummy2, is_mergable, do_merge, create_label);
  std::cout << "***************************" << std::endl;
  std::cout << p_alt2 << std::endl;

  //for (auto& v : set_of_merged_stmts) {
  for (size_t i = 0; i < set_of_merged_stmts.size(); ++i) {
    std::cout << i << ": "; // << set_of_merged_stmts[i].size() << std::endl;
    for (auto& t : set_of_merged_stmts[i]) {
      std::cout << "(" << *(t.element()) << ")@" << t.execution_id() << ", ";
    }
    std::cout << std::endl;
  }

  unify(p_alt2, set_of_merged_stmts, s_destination.shared_variables());

  return EXIT_SUCCESS;
}
