#ifndef PROJECTED_EXECUTIONS_H_INCLUDED
#define PROJECTED_EXECUTIONS_H_INCLUDED

#include "alphabet.h"
#include "graph.h"
#include "tag.h"

#include <functional>
#include <iostream>
#include <ostream>
#include <map>
#include <vector>

namespace alternative {

template <class LabelType>
struct projected_executions_t {

  /*
    We assume that every symbol in the alphabet appears at most once in a word,
    that there is a total order over the symbols in the alphabet, and that in
    each word the symbols respect this order.
  */
  void merge(
    const projected_execution_t& pexe,
    std::function<bool (const LabelType&, const alphabet::stmt_t&)> is_mergable,
    std::function<void (LabelType&, const alphabet::stmt_t&, const projected_execution_t&)> do_merge,
    std::function<LabelType (alphabet::stmt_t&, const projected_execution_t&)> create_label
  ) {
    std::map< alphabet::stmt_t* , edge_t& > merge_map;
    std::map< int, std::vector< edge_t >> new_edges;

    // determine merging points
    for (auto& p : pexe.projections) {
      for (edge_t& e : edges[p.first]) {
        for (auto& s : p.second) {
          if (is_mergable(e.label, *s)) {
            // store for later merging
            // TODO shall we add an assertion that checks that merge_map[s] does not already contain another edge?
            merge_map.insert({ s, e });
            break;
          }
        }
      }
    }

    // merge
    for (auto& p : pexe.projections) {
      graph_t<LabelType>& g = projections[p.first];
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
          std::cout << "no merge(" << s << "): " << s->type << std::endl;

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

          new_edges[p.first].push_back(g.add_edge(source, create_label(*s, pexe), target));

          source = target;
        }
        else {
          // merge
          std::cout << "merge" << std::endl;
          do_merge(it->second.label, *s, pexe);

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
      out << "  statements:" << std::endl;
      auto it = ps.edges.find(p.first);

      if (it != ps.edges.end()) {
        for (const edge_t& e : it->second) {
          out << "    " << e.label << std::endl;
        }
      }
    }
    out << "}" << std::endl;

    return out;
  }

  void unify() {
    std::cout << "unify!" << std::endl;

    for (auto& it : projections) {
      std::cout << "thread " << it.first << std::endl;
      auto order = it.second.dag_topological_sort(0);
      std::cout << "topological order:";
      for (size_t node : order) {
        std::cout << " " << node;
      }
      std::cout << std::endl;
    }
  }

private:
  using edge_t = typename graph_t<LabelType>::edge_t;
  std::map<int, graph_t< LabelType >> projections;
  std::map<int, std::vector< edge_t >> edges;

};

}

#endif // PROJECTED_EXECUTIONS_H_INCLUDED
