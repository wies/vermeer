#ifndef SSA_MAP_H_INCLUDED
#define SSA_MAP_H_INCLUDED

#include <map>
#include <ostream>

struct ssa_map_t {

  ssa_map_t() {}
  ssa_map_t(const ssa_map_t& other) : ssa_indices(other.ssa_indices) {}

  int inc(int variable_id) {
    int ssa_index = ssa_indices[variable_id];
    ssa_index++;
    ssa_indices[variable_id] = ssa_index;
    return ssa_index;
  }

  // TODO can we do something less arbitrary?
  void set_value(int variable_id, int value) {
    ssa_indices.insert({ variable_id, value });
  }

  const int operator[](int variable_id) const {
    auto it = ssa_indices.find(variable_id);

    if (it != ssa_indices.end()) {
      return it->second;
    }

    return 0;
  }

  std::set<int> variables() const {
    std::set<int> vars;

    for (auto& i : ssa_indices) {
      vars.insert(i.first);
    }

    return vars;
  }

  friend std::ostream& operator<<(std::ostream& out, ssa_map_t& m) {
    out << "{" << std::endl;

    for (const auto& p : m.ssa_indices) {
      out << "  var(" << p.first << ") = " << p.second << std::endl;
    }

    out << "}";

    return out;
  }

private:
  // map from variable id to thread-local ssa index
  std::map<int, int> ssa_indices;

};

#endif // SSA_MAP_H_INCLUDED
