#ifndef ALPHABET_H_INCLUDED
#define ALPHABET_H_INCLUDED

#include "program_location.h"
#include "graph.h"

#include <functional>

namespace alphabet {

struct ssa_variable_t {

  //int unique_id;
  int variable_id;

  /* type, currently: INT */

  struct ssa_index_t {
    int thread_id;
    int thread_local_index;
  } ssa_index;

  friend std::ostream& operator<<(std::ostream& out, const ssa_variable_t& v) {
    out << "var(" << v.variable_id << ")_{T" << v.ssa_index.thread_id << "," << v.ssa_index.thread_local_index << "}";
    return out;
  }

};

struct pi_assignment_t;
struct local_assignment_t;
struct global_assignment_t;
struct phi_assignment_t;
struct assertion_t;
struct assumption_t;
struct local_execution_t;

struct stmt_visitor_t {

  virtual void visit_pi_assignment(pi_assignment_t& a) = 0;
  virtual void visit_local_assignment(local_assignment_t& a) = 0;
  virtual void visit_global_assignment(global_assignment_t& a) = 0;
  virtual void visit_phi_assignment(phi_assignment_t& a) = 0;
  virtual void visit_assertion(assertion_t& a) = 0;
  virtual void visit_assumption(assumption_t& a) = 0;

};

struct stmt_t {

  virtual ~stmt_t() {}

  std::vector<expr::expr_t<ssa_variable_t>> guards;
  thread_local_position_t program_location; // program location

  virtual void accept(stmt_visitor_t& visitor) = 0;

  void print_guards(std::ostream& out) const {
    out << "guard(";

    if (guards.empty()) {
      out << "true";
    }
    else if (guards.size() == 1) {
      out << guards[0];
    }
    else {
      out << "(" << guards[0] << ")";

      for (size_t i = 1; i < guards.size(); i++) {
        out << " && (" << guards[i] << ")";
      }
    }

    out << ") -> ";
  }

  virtual void print(std::ostream& out) const = 0;

  friend std::ostream& operator<<(std::ostream& out, const stmt_t& s) {
    out << s.program_location << ": ";
    s.print_guards(out);
    s.print(out);
    return out;
  }

};

struct local_assignment_t : public stmt_t {
  ssa_variable_t local_variable; // lhs
  expr::term_t<ssa_variable_t> rhs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_local_assignment(*this);
  }

  void print(std::ostream& out) const override {
    out << local_variable << " := " << rhs;
  }

};

struct pi_assignment_t : public stmt_t {
  ssa_variable_t local_variable; // lhs
  ssa_variable_t shared_variable; // rhs

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_pi_assignment(*this);
  }

  void print(std::ostream& out) const override {
    out << local_variable << " := pi(" << shared_variable << ")";
  }

};

struct global_assignment_t : public stmt_t {
  ssa_variable_t shared_variable; // lhs
  expr::term_t<ssa_variable_t> rhs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_global_assignment(*this);
  }

  void print(std::ostream& out) const override {
    out << shared_variable << " := " << rhs;
  }

};

struct phi_assignment_t : public stmt_t {
  ssa_variable_t variable; // lhs
  /* ... */

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_phi_assignment(*this);
  }

  void print(std::ostream& out) const override {
    out << "phi(...)";
  }

};

struct assertion_t : public stmt_t {

  std::vector<expr::expr_t<ssa_variable_t>> exprs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_assertion(*this);
  }

  void print(std::ostream& out) const override {
    out << "assert(";
    switch (exprs.size()) {
      case 0:
        out << "true";
        break;
      case 1:
        out << exprs[0];
        break;
      default:
        out << "(" << exprs[0] << ")";
        for (size_t i = 1; i < exprs.size(); i++) {
          out << " && (" << exprs[i] << ")";
        }
        break;
    }
    out << ")";
  }

};

struct assumption_t : public stmt_t {

  std::vector<expr::expr_t<ssa_variable_t>> exprs;

  void accept(stmt_visitor_t& visitor) override {
    visitor.visit_assumption(*this);
  }

  void print(std::ostream& out) const override {
    out << "assume(";
    switch (exprs.size()) {
      case 0:
        out << "true";
        break;
      case 1:
        out << exprs[0];
        break;
      default:
        out << "(" << exprs[0] << ")";
        for (size_t i = 1; i < exprs.size(); i++) {
          out << " && (" << exprs[i] << ")";
        }
        break;
    }
    out << ")";
  }

};

struct projected_execution_t {

  std::map<int, std::vector<stmt_t*>> projections;

  ~projected_execution_t() {
    for (auto& p : projections) {
      for (auto& s : p.second) {
        delete s;
      }
    }
  }

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

  /*
    We assume that every symbol in the alphabet appears at most once in a word,
    that there is a total order over the symbols in the alphabet, and that in
    each word the symbols respect this order.
  */
  void merge(
    const projected_execution_t& pexe,
    std::function<bool (const graph_t<int>::edge_t&, const stmt_t&)> is_mergable,
    std::function<void (const graph_t<int>::edge_t&, const stmt_t&)> do_merge,
    int execution_id // TODO this has to be used in \pi nodes!
  ) {
    std::map< alphabet::stmt_t* , graph_t<int>::edge_t > merge_map;
    std::map< int, std::vector< graph_t<int>::edge_t >> new_edges;

    // determine merging points
    for (auto& p : pexe.projections) {
      size_t last_match = -1;
      for (auto& e : edges[p.first]) {
        for (size_t i = last_match + 1; i < p.second.size(); i++) {
          stmt_t* s = p.second[i];
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
        stmt_t* s = p.second[i];
        auto it = merge_map.find(s);

        if (it == merge_map.end()) {
          // no merge
          std::cout << "no merge" << std::endl;

          bool target_set = false;
          size_t target;

          // check whether successor is getting merged
          if (i < p.second.size() - 1) {
            stmt_t* next_s = p.second[i + 1];

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

}

#endif // ALPHABET_H_INCLUDED
