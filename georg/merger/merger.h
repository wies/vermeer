#ifndef MERGER_H_INCLUDED
#define MERGER_H_INCLUDED

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

void update_edge2map_map2(
  int thread_id,
  size_t node,
  /*const*/ graph_t< size_t > g,
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts,
  const std::map<size_t /* i.e., node*/, ssa_map_t>& node2map,
  std::map<const graph_t<size_t>::edge_t, ssa_map_t>& edge2map,
  id_partitioned_substitution_maps_t& local_subst_map
);

id_partitioned_substitution_maps_t extract_sharedvar_substmap(
  alternative::projected_executions_t<size_t>& pexes,
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts
);

id_partitioned_substitution_maps_t extract_localvar_substmap(
  alternative::projected_executions_t<size_t>& pexes,
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts
);

std::vector< alphabet::stmt_t* > unify_statements(
  alternative::projected_executions_t<size_t>& pexes,
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts,
  const id_partitioned_substitution_maps_t& sharedvar_substmap,
  const id_partitioned_substitution_maps_t& localvar_substmap
);

std::pair< alternative::projected_executions_t< size_t >, std::vector< alphabet::stmt_t* > >
unify(
  alternative::projected_executions_t<size_t>& pexes,
  const std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > >& set_of_merged_stmts,
  const std::set<int>& shared_variables
);

#endif // MERGER_H_INCLUDED
