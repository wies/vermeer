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

  friend std::ostream& operator<<(std::ostream& out, const ssa_map_t& m) {
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

struct id_partitioned_substitution_maps_t {

  id_partitioned_substitution_maps_t() {}
  id_partitioned_substitution_maps_t(const id_partitioned_substitution_maps_t& other) : id_partitioned_substitution_maps(other.id_partitioned_substitution_maps) {}

  typedef std::map< alphabet::ssa_variable_t, alphabet::ssa_variable_t > substitution_map_t;
  std::map< int /* i.e., the id */, substitution_map_t > id_partitioned_substitution_maps;

  void map_to(int id, alphabet::ssa_variable_t domain_variable, alphabet::ssa_variable_t image_variable) {
    substitution_map_t& m = id_partitioned_substitution_maps[id];
    m[domain_variable] = image_variable;
  }

  friend std::ostream& operator<<(std::ostream& out, const id_partitioned_substitution_maps_t& maps) {
    out << "{" << std::endl;

    for (auto& p : maps.id_partitioned_substitution_maps) {
      out << "  " << p.first << " -> {" << std::endl;
      for (auto& p2 : p.second) {
        out << "    " << p2.first << " -> " << p2.second << std::endl;
      }
      out << "  }" << std::endl;
    }

    out << "}";

    return out;
  }

};

#endif // SSA_MAP_H_INCLUDED
