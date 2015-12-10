#include "execution2alphabet.h"

#include <ostream>

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

projected_executions_t::projected_executions_t(const projected_execution_t& pexe) {
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

  /*
    We assume that every symbol in the alphabet appears at most once in a word,
    that there is a total order over the symbols in the alphabet, and that in
    each word the symbols respect this order.
  */
  void projected_executions_t::merge(
    const projected_execution_t& pexe,
    std::function<bool (const graph_t<int>::edge_t&, const alphabet::stmt_t&)> is_mergable,
    std::function<void (const graph_t<int>::edge_t&, const alphabet::stmt_t&)> do_merge
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

  std::ostream& operator<<(std::ostream& out, const projected_executions_t ps) {
    out << "{" << std::endl;
    for (auto& p : ps.projections) {
      out << "thread " << p.first << ":" << std::endl;
      out << p.second << std::endl;
    }
    out << "}" << std::endl;

    return out;
  }
