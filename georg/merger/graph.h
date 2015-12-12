#ifndef GRAPH_H_INCLUDED
#define GRAPH_H_INCLUDED

#include <map>
#include <ostream>
#include <vector>

template <class LabelType>
class graph_t {

public:
  struct edge_t {

    edge_t(size_t src, LabelType lbl, size_t tgt) : source(src), label(lbl), target(tgt) {}

    size_t source;
    LabelType label;
    size_t target;

    friend std::ostream& operator<<(std::ostream& out, const edge_t& e) {
      out << e.source << " -[" << e.label << "]-> " << e.target << ", ";
      return out;
    }
  };

private:
  std::map<size_t, std::vector<edge_t>> adjacency_lists;
  size_t nr_of_nodes;

public:

  graph_t() : nr_of_nodes(0) {}

  size_t create_node() {
    size_t id = nr_of_nodes;
    nr_of_nodes++;
    return id;
  }

  edge_t& add_edge(size_t source, LabelType label, size_t target) {
    // TODO How defensive do we want to progam?
    auto& v = adjacency_lists[source];
    v.emplace(v.end(), source, label, target);
    return v.back();
  }

  inline
  size_t size() const {
    return nr_of_nodes;
  }

  inline
  bool empty() const {
    return (nr_of_nodes == 0);
  }

  friend std::ostream& operator<<(std::ostream& out, const graph_t& g) {
    out << "graph {" << std::endl;
    for (size_t n = 0; n < g.nr_of_nodes; n++) {
      out << "  " << n << ": ";
      typename std::map<size_t, std::vector<edge_t>>::const_iterator it = g.adjacency_lists.find(n);
      if (it == g.adjacency_lists.end()) {
        out << "empty" << std::endl;
      }
      else {
        for (const edge_t& e : it->second) {
          out << e << ", ";
        }
        out << std::endl;
      }
    }
    out << "}";

    return out;
  }

};

#endif // GRAPH_H_INCLUDED
