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

#include "merger.h"

int main(int argc, char* argv[]) {
  exe::execution_t s_destination = read_execution("example.xml");
  std::cout << s_destination << std::endl << "******************************************" << std::endl;

  projected_execution_t p(s_destination, 0);
  std::cout << p << std::endl << "******************************************" << std::endl;

  exe::execution_t e_dummy = read_execution("example_dummy.xml");
  projected_execution_t p_dummy(e_dummy, 1);

  exe::execution_t e_dummy2 = read_execution("example_dummy2.xml");
  projected_execution_t p_dummy2(e_dummy2, 2);

  using label_type2 = size_t;
  std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > > set_of_merged_stmts;

  alternative::projected_executions_t< label_type2 > p_alt2;
  auto is_mergable = [&] (const label_type2& v, const alphabet::stmt_t& s) {
    const alphabet::stmt_t& s_destination = *(set_of_merged_stmts[v].front().element());

    if (s_destination.program_location == s.program_location) {
      // can we assume that we have the same type of statement at the same program location?
      assert(s_destination.type == s.type);

      // check guards
      if (s_destination.guards.size() != s.guards.size()) {
        return false;
      }

      for (size_t i = 0; i < s.guards.size(); i++) {
        if (s_destination.guards[i] != s.guards[i]) {
          return false;
        }
      }

      // do further equality checks
      switch (s.type) {
        case alphabet::stmt_t::PI_ASSIGNMENT:
          {
            const alphabet::pi_assignment_t& ls = (const alphabet::pi_assignment_t&)s_destination;
            const alphabet::pi_assignment_t& ss = (const alphabet::pi_assignment_t&)s;

            return (ls.local_variable == ss.local_variable);
          }
        case alphabet::stmt_t::LOCAL_ASSIGNMENT:
          {
            const alphabet::local_assignment_t& ls = (const alphabet::local_assignment_t&)s_destination;
            const alphabet::local_assignment_t& ss = (const alphabet::local_assignment_t&)s;

            return (ls.local_variable == ss.local_variable);
          }
        case alphabet::stmt_t::GLOBAL_ASSIGNMENT:
          {
            const alphabet::global_assignment_t& ls = (const alphabet::global_assignment_t&)s_destination;
            const alphabet::global_assignment_t& ss = (const alphabet::global_assignment_t&)s;

            return (ls.shared_variable == ss.shared_variable);
          }
        default:
          // TODO implement other equality checks
          break;
      }

      return true;
    }

    return false;
  };

  auto do_merge = [&] (label_type2& l, const alphabet::stmt_t& s_source, const projected_execution_t& pexe) {
    auto& v = set_of_merged_stmts[l];
    v.emplace(v.end(), &s_source, pexe.unique_id);
  };

  auto create_label = [&] (const alphabet::stmt_t& s, const projected_execution_t& pexe) {
    auto it = set_of_merged_stmts.emplace(set_of_merged_stmts.end());
    it->emplace(it->end(), &s, pexe.unique_id);
    return set_of_merged_stmts.size() - 1;
  };

  p_alt2.merge(p, is_mergable, do_merge, create_label);
  std::cout << "***************************" << std::endl;
  p_alt2.merge(p_dummy, is_mergable, do_merge, create_label);
  std::cout << "***************************" << std::endl;
  p_alt2.merge(p_dummy2, is_mergable, do_merge, create_label);
  std::cout << "***************************" << std::endl;
  std::cout << p_alt2 << std::endl;

  //for (auto& v : set_of_merged_stmts) {
  for (size_t i = 0; i < set_of_merged_stmts.size(); ++i) {
    std::cout << i << ": "; // << set_of_merged_stmts[i].size() << std::endl;
    for (auto& t : set_of_merged_stmts[i]) {
      std::cout << "(" << *(t.element()) << ")@" << t.execution_id() << ", ";
    }
    std::cout << std::endl;
  }

  unify(p_alt2, set_of_merged_stmts, s_destination.shared_variables());

  return EXIT_SUCCESS;
}
