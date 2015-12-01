#include <cstdlib>
#include <iostream>

#include <map>
#include <set>
#include <vector>

#include "error.h"
#include "trace.h"
#include "xml.h"

#include "alphabet.h"

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

std::set<int> extract_variables(const exe::expression_t& e) {
  std::set<int> variable_ids;

  for (const exe::linear_product_t& p : e.term.products) {
    variable_ids.insert(p.variable_id);
  }

  return variable_ids;
}

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
    int pos = thread_local_counters[s.thread];
    v.push_back({ s.thread, pos });
    thread_local_counters[s.thread] = pos + 1;

    // track variable definition
    if (s.type == exe::ASSIGNMENT) {
      variable_definitions[s.variable_id] = s.position;
      std::cout << "Variable " << s.variable_id << " is defined at " << v[variable_definitions[s.variable_id]] << std::endl;
    }

    // track variable usage
    // a) guards
    std::set<int> variable_ids;
    for (auto const& e : s.guard.exprs) {
      auto var_ids = extract_variables(e);
      variable_ids.insert(var_ids.begin(), var_ids.end());
    }

    // b) variables in other expressions
    switch (s.type) {
      case exe::ASSIGNMENT:
        for (auto const& p : s.rhs.products) {
          if (e.variable_declarations[p.variable_id].thread < 0) { // global variable
            std::cout << "G" << p.variable_id;
          }
          variable_ids.insert(p.variable_id);
        }
        break;
      case exe::ASSERTION:
      case exe::ASSUMPTION:
        for (auto const& e : s.exprs) {
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

int main(int argc, char* argv[]) {
  exe::execution_t e = read_execution("example.xml");

  std::cout << e << std::endl;

  auto pos = extract_thread_local_positions(e);

  for (auto const& p : pos) {
    std::cout << p << std::endl;
  }

  return EXIT_SUCCESS;
}

