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
    variable_to_be_updated = a.shared_variable.variable_id;
    do_update = true;
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
  size_t node, /*const*/ graph_t< size_t > g, 
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

alternative::projected_executions_t< size_t > unify(
  alternative::projected_executions_t<size_t>& pexes, 
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts, 
  const std::set<int>& shared_variables
) {

  alternative::projected_executions_t< size_t > unified_pes;

  for (auto& it : pexes.projections) {
    graph_t< size_t >& g = it.second;
    // for each thread we have to generate a unified graph
    std::cout << "thread " << it.first << std::endl;
    
    graph_t< size_t >& g_new = unified_pes.projections[it.first];
    std::vector< graph_t< size_t >::edge_t >& es = unified_pes.edges[it.first]; // actually we do not need that since we do not merge with the unified executions anymore -> refactor
    
    auto order = g.dag_topological_sort(0);
    assert(order.size() > 0);
    //graph_t< size_t > g_new;
    g_new.create_nodes(order.size()); // we assume that all numbers from 0 ... n - 1 are used
    std::vector< alphabet::stmt_t* > unified_stmts;

    std::map<size_t /* i.e., node*/, ssa_map_t> node2map;
    ssa_map_t empty_map;
    node2map.insert({ 0, empty_map });

    std::map<const graph_t<size_t>::edge_t, ssa_map_t> edge2map;

    update_edge2map_map(0, g, set_of_merged_stmts, node2map, edge2map);

    for (size_t i = 1; i < order.size(); ++i) {
      size_t node = order[i];

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

      // create incoming edges to node
      for (const auto& e : g.incoming_edges(node)) {
        size_t index = unified_stmts.size();
        es.push_back(g_new.add_edge(e.source, index, e.target));
        alphabet::stmt_t* unified_stmt = unify_statements(set_of_merged_stmts[e.label]);
        unified_stmts.push_back(unified_stmt);
      }

      update_edge2map_map(node, g, set_of_merged_stmts, node2map, edge2map);
    }

    std::map< size_t, id_partitioned_substitution_maps_t > node2substmap;
    std::map< const graph_t<size_t>::edge_t, id_partitioned_substitution_maps_t > edge2substmap;

    for (size_t node : order) {
      auto& substmap = node2substmap[node];

      // TODO for each outgoing edge compute an update for substmap (put them into edge2substmap)

      // TODO unify the substmaps of all incoming edges (put the result into node2substmap)

    }
    
    std::cout << g_new << std::endl;
    for (alphabet::stmt_t* s : unified_stmts) {
      std::cout << s << std::endl;
    }
  }
  
  // TODO we also have to return the newly created statements
  return unified_pes;
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
  auto is_mergable_alt2 = [&] (const label_type2& v, const alphabet::stmt_t& s) {
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

  auto do_merge_alt2 = [&] (label_type2& l, const alphabet::stmt_t& s_source, const projected_execution_t& pexe) {
    auto& v = set_of_merged_stmts[l];
    v.emplace(v.end(), &s_source, pexe.unique_id);
  };

  auto create_label2 = [&] (const alphabet::stmt_t& s, const projected_execution_t& pexe) {
    auto it = set_of_merged_stmts.emplace(set_of_merged_stmts.end());
    it->emplace(it->end(), &s, pexe.unique_id);
    return set_of_merged_stmts.size() - 1;
  };

  p_alt2.merge(p, is_mergable_alt2, do_merge_alt2, create_label2);
  std::cout << "***************************" << std::endl;
  p_alt2.merge(p_dummy, is_mergable_alt2, do_merge_alt2, create_label2);
  std::cout << "***************************" << std::endl;
  p_alt2.merge(p_dummy2, is_mergable_alt2, do_merge_alt2, create_label2);
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
