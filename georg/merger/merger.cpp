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

void update_edge2map_map(size_t node, /*const*/ graph_t< size_t > g, const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts,const std::map<size_t /* i.e., node*/, ssa_map_t>& node2map, std::map<const graph_t<size_t>::edge_t, ssa_map_t>& edge2map) {
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

    std::cout << new_ssa_map << std::endl;

    edge2map.insert({ edge, new_ssa_map });
  }
}

void unify(alternative::projected_executions_t<size_t>& pexes, const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts) {
  std::cout << "unify!" << std::endl;

  // TODO create a new projected_executions_t instance

  for (auto& it : pexes.projections) {
    graph_t< size_t >& g = it.second;
    // for each thread we have to generate a unified graph
    std::cout << "thread " << it.first << std::endl;
    auto order = g.dag_topological_sort(0);
    assert(order.size() > 0);
    graph_t< size_t > g_new;
    //std::cout << "topological order:";
    std::cout << "g_new.size() = " << g_new.size();
    g_new.create_nodes(order.size()); // we assume that all numbers from 0 ... n - 1 are used
    std::cout << " ---> " << g_new.size() << " (order.size() = " << order.size() << ")" << std::endl;

    std::map<size_t /* i.e., node*/, ssa_map_t> node2map;
    ssa_map_t empty_map;
    node2map.insert({ 0, empty_map });

    std::cout << empty_map << std::endl;

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
      // TODO implement

      update_edge2map_map(node, g, set_of_merged_stmts, node2map, edge2map);
    }
  }
}

int main(int argc, char* argv[]) {
  exe::execution_t s_destination = read_execution("example.xml");
  std::cout << s_destination << std::endl << "******************************************" << std::endl;

  projected_execution_t p(s_destination, 0);
  std::cout << p << std::endl << "******************************************" << std::endl;

//  projected_executions_t ps(p);
  //std::cout << ps << std::endl << "******************************************" << std::endl;

  exe::execution_t e_dummy = read_execution("example_dummy.xml");
  projected_execution_t p_dummy(e_dummy, 1);

  exe::execution_t e_dummy2 = read_execution("example_dummy2.xml");
  projected_execution_t p_dummy2(e_dummy2, 2);

#if 0
  auto is_mergable = [] (const alphabet::stmt_t& s_destination, const alphabet::stmt_t& s) {
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

  auto do_merge = [] (alphabet::stmt_t& s_destination, const alphabet::stmt_t& s_source) {
    switch (s_source.type) {
      case alphabet::stmt_t::PI_ASSIGNMENT:
      {
        alphabet::pi_assignment_t& ls = (alphabet::pi_assignment_t&)s_destination;
        const alphabet::pi_assignment_t& ss = (const alphabet::pi_assignment_t&)s_source;

        ls.shared_variables.insert(ls.shared_variables.end(), ss.shared_variables.begin(), ss.shared_variables.end());

        break;
      }
      case alphabet::stmt_t::LOCAL_ASSIGNMENT:
      {
        alphabet::local_assignment_t& ls = (alphabet::local_assignment_t&)s_destination;
        const alphabet::local_assignment_t& ss = (const alphabet::local_assignment_t&)s_source;

        ls.rhs.insert(ls.rhs.end(), ss.rhs.begin(), ss.rhs.end());

        break;
      }
      case alphabet::stmt_t::GLOBAL_ASSIGNMENT:
      {
        alphabet::global_assignment_t& ls = (alphabet::global_assignment_t&)s_destination;
        const alphabet::global_assignment_t& ss = (const alphabet::global_assignment_t&)s_source;

        ls.rhs.insert(ls.rhs.end(), ss.rhs.begin(), ss.rhs.end());

        break;
      }
      default:
        // do nothing
        break;
    }
  };

  ps.merge(p_dummy, is_mergable, do_merge);
  std::cout << ps << std::endl;

  ps.merge(p_dummy2, is_mergable, do_merge);
  std::cout << ps << std::endl;

  execution_tag_t<int> t(43, 0);
  execution_tag_t<int> t2(132, 0);
  execution_tag_t<int> t3(43, 1);
  std::cout << t << " " << t2 << " " << t3 << std::endl;
  std::cout << (t == t) << std::endl;
  std::cout << (t != t) << std::endl;
  std::cout << (t == t2) << std::endl;
  std::cout << (t == t3) << std::endl;



  using label_type = alphabet::stmt_t*;

  auto is_mergable_alt = [] (const label_type& s_dest, const alphabet::stmt_t& s) {
    const alphabet::stmt_t& s_destination = *s_dest;

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

  auto do_merge_alt = [] (alphabet::stmt_t*& s_dest, const alphabet::stmt_t& s_source) {
    alphabet::stmt_t& s_destination = *s_dest;

    switch (s_source.type) {
      case alphabet::stmt_t::PI_ASSIGNMENT:
      {
        alphabet::pi_assignment_t& ls = (alphabet::pi_assignment_t&)s_destination;
        const alphabet::pi_assignment_t& ss = (const alphabet::pi_assignment_t&)s_source;

        ls.shared_variables.insert(ls.shared_variables.end(), ss.shared_variables.begin(), ss.shared_variables.end());

        break;
      }
      case alphabet::stmt_t::LOCAL_ASSIGNMENT:
      {
        alphabet::local_assignment_t& ls = (alphabet::local_assignment_t&)s_destination;
        const alphabet::local_assignment_t& ss = (const alphabet::local_assignment_t&)s_source;

        ls.rhs.insert(ls.rhs.end(), ss.rhs.begin(), ss.rhs.end());

        break;
      }
      case alphabet::stmt_t::GLOBAL_ASSIGNMENT:
      {
        alphabet::global_assignment_t& ls = (alphabet::global_assignment_t&)s_destination;
        const alphabet::global_assignment_t& ss = (const alphabet::global_assignment_t&)s_source;

        ls.rhs.insert(ls.rhs.end(), ss.rhs.begin(), ss.rhs.end());

        break;
      }
      default:
        // do nothing
        break;
    }
  };

  alternative::projected_executions_t< alphabet::stmt_t* > p_alt;
  p_alt.merge(p, is_mergable_alt, do_merge_alt);
  std::cout << "***************************" << std::endl;
  p_alt.merge(p_dummy, is_mergable_alt, do_merge_alt);
  std::cout << "***************************" << std::endl;
  p_alt.merge(p_dummy2, is_mergable_alt, do_merge_alt);
  std::cout << "***************************" << std::endl;
  std::cout << p_alt << std::endl;
  std::cout << "***************************" << std::endl;
#endif

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

  unify(p_alt2, set_of_merged_stmts);

  ssa_map_t ssa_map;
  std::cout << ssa_map[0] << std::endl;
  ssa_map.inc(0);
  std::cout << ssa_map[0] << std::endl;

  return EXIT_SUCCESS;
}
