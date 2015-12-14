#ifndef GRAPH_H_INCLUDED
#define GRAPH_H_INCLUDED

#include <cassert>
#include <map>
#include <ostream>
#include <stack>
#include <vector>

template <class LabelType>
class graph_t {

public:
  struct edge_t {

    edge_t(size_t src, LabelType lbl, size_t tgt) : source(src), label(lbl), target(tgt) {}

    size_t source;
    LabelType label;
    size_t target;

    bool operator<(const edge_t& other) const {
      if (source < other.source) {
        return true;
      }

      if (source == other.source) {
        if (target < other.target) {
          return true;
        }

        if (target == other.target) {
          return (label < other.label);
        }
      }

      return false;
    }

    friend std::ostream& operator<<(std::ostream& out, const edge_t& e) {
      out << e.source << " -[" << e.label << "]-> " << e.target;
      return out;
    }
  };

private:
  std::map<size_t, std::vector<edge_t>> adjacency_lists;
  std::map<size_t, std::vector<edge_t>> incoming_adjacency_lists;
  size_t nr_of_nodes;

public:

  graph_t() : nr_of_nodes(0) {}

  size_t create_node() {
    size_t id = nr_of_nodes;
    nr_of_nodes++;
    return id;
  }

  size_t create_nodes(size_t n) { // n = number of nodes
    assert(n > 0);

    size_t start = create_node();
    for (size_t i = 1; i < n; i++) {
      create_node();
    }

    return start;
  }

  edge_t& add_edge(size_t source, LabelType label, size_t target) {
    // TODO How defensive do we want to progam?
    auto& v = adjacency_lists[source];
    v.emplace(v.end(), source, label, target);

    auto& edge = v.back();
    auto& incoming_v = incoming_adjacency_lists[target];
    incoming_v.push_back(edge);

    return edge;
  }

  const std::vector<edge_t>& outgoing_edges(size_t node) {
    return adjacency_lists[node];
  }

  const std::vector<edge_t>& incoming_edges(size_t node) {
    return incoming_adjacency_lists[node];
  }

  inline
  size_t size() const {
    return nr_of_nodes;
  }

  inline
  bool empty() const {
    return (nr_of_nodes == 0);
  }

  std::vector<size_t> dag_topological_sort(size_t root) {
    // TODO assert that root is a valid node in the graph

    std::stack<size_t> topological_order;

    std::stack<std::pair<size_t, int>> workset;

    workset.push({ root, -1 });

    bool* visited = new bool[size()];
    visited[0] = true;
    for (int i = 1; i < size(); i++) {
      visited[i] = false;
    }

    while (!workset.empty()) {
      auto it = workset.top();
      workset.pop();

      int i = it.second + 1;

      if (i < adjacency_lists[it.first].size()) {
        workset.push({ it.first, i });

        if (!visited[adjacency_lists[it.first][i].target]) {
          workset.push({ adjacency_lists[it.first][i].target, -1 });
          visited[adjacency_lists[it.first][i].target] = true;
        }
      }
      else {
        // map node to time and increment time
        topological_order.push(it.first);
      }
    }

    delete[] visited;

    std::vector<size_t> order;
    while (!topological_order.empty()) {
      size_t node = topological_order.top();
      topological_order.pop();
      order.push_back(node);
    }

    return order;
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
