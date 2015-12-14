#ifndef SSA_MAP_H_INCLUDED
#define SSA_MAP_H_INCLUDED

#include <map>

struct ssa_map_t {

  int inc(int variable_id) {
    int ssa_index = ssa_indices[variable_id];
    ssa_index++;
    ssa_indices[variable_id] = ssa_index;
    return ssa_index;
  }

  const int operator[](int variable_id) {
    int ssa_index = ssa_indices[variable_id];
    return ssa_index;
  }

private:
  // map from variable id to thread-local ssa index
  std::map<int, int> ssa_indices;

};

#endif // SSA_MAP_H_INCLUDED
