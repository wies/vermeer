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

int main(int argc, char* argv[]) {
  exe::execution_t s_destination = read_execution("example.xml");
  std::cout << s_destination << std::endl << "******************************************" << std::endl;

  projected_execution_t p(s_destination, 0);
  std::cout << p << std::endl << "******************************************" << std::endl;

//  projected_executions_t ps(p);
  //std::cout << ps << std::endl << "******************************************" << std::endl;

  exe::execution_t e_dummy = read_execution("example_dummy.xml");
  projected_execution_t p_dummy(e_dummy, 1);

  exe::execution_t e_dummy2 = read_execution("example_dummy2.xml");
  projected_execution_t p_dummy2(e_dummy2, 2);

#if 0
  auto is_mergable = [] (const alphabet::stmt_t& s_destination, const alphabet::stmt_t& s) {
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

  auto do_merge = [] (alphabet::stmt_t& s_destination, const alphabet::stmt_t& s_source) {
    switch (s_source.type) {
      case alphabet::stmt_t::PI_ASSIGNMENT:
      {
        alphabet::pi_assignment_t& ls = (alphabet::pi_assignment_t&)s_destination;
        const alphabet::pi_assignment_t& ss = (const alphabet::pi_assignment_t&)s_source;

        ls.shared_variables.insert(ls.shared_variables.end(), ss.shared_variables.begin(), ss.shared_variables.end());

        break;
      }
      case alphabet::stmt_t::LOCAL_ASSIGNMENT:
      {
        alphabet::local_assignment_t& ls = (alphabet::local_assignment_t&)s_destination;
        const alphabet::local_assignment_t& ss = (const alphabet::local_assignment_t&)s_source;

        ls.rhs.insert(ls.rhs.end(), ss.rhs.begin(), ss.rhs.end());

        break;
      }
      case alphabet::stmt_t::GLOBAL_ASSIGNMENT:
      {
        alphabet::global_assignment_t& ls = (alphabet::global_assignment_t&)s_destination;
        const alphabet::global_assignment_t& ss = (const alphabet::global_assignment_t&)s_source;

        ls.rhs.insert(ls.rhs.end(), ss.rhs.begin(), ss.rhs.end());

        break;
      }
      default:
        // do nothing
        break;
    }
  };

  ps.merge(p_dummy, is_mergable, do_merge);
  std::cout << ps << std::endl;

  ps.merge(p_dummy2, is_mergable, do_merge);
  std::cout << ps << std::endl;

  execution_tag_t<int> t(43, 0);
  execution_tag_t<int> t2(132, 0);
  execution_tag_t<int> t3(43, 1);
  std::cout << t << " " << t2 << " " << t3 << std::endl;
  std::cout << (t == t) << std::endl;
  std::cout << (t != t) << std::endl;
  std::cout << (t == t2) << std::endl;
  std::cout << (t == t3) << std::endl;



  using label_type = alphabet::stmt_t*;

  auto is_mergable_alt = [] (const label_type& s_dest, const alphabet::stmt_t& s) {
    const alphabet::stmt_t& s_destination = *s_dest;

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

  auto do_merge_alt = [] (alphabet::stmt_t*& s_dest, const alphabet::stmt_t& s_source) {
    alphabet::stmt_t& s_destination = *s_dest;

    switch (s_source.type) {
      case alphabet::stmt_t::PI_ASSIGNMENT:
      {
        alphabet::pi_assignment_t& ls = (alphabet::pi_assignment_t&)s_destination;
        const alphabet::pi_assignment_t& ss = (const alphabet::pi_assignment_t&)s_source;

        ls.shared_variables.insert(ls.shared_variables.end(), ss.shared_variables.begin(), ss.shared_variables.end());

        break;
      }
      case alphabet::stmt_t::LOCAL_ASSIGNMENT:
      {
        alphabet::local_assignment_t& ls = (alphabet::local_assignment_t&)s_destination;
        const alphabet::local_assignment_t& ss = (const alphabet::local_assignment_t&)s_source;

        ls.rhs.insert(ls.rhs.end(), ss.rhs.begin(), ss.rhs.end());

        break;
      }
      case alphabet::stmt_t::GLOBAL_ASSIGNMENT:
      {
        alphabet::global_assignment_t& ls = (alphabet::global_assignment_t&)s_destination;
        const alphabet::global_assignment_t& ss = (const alphabet::global_assignment_t&)s_source;

        ls.rhs.insert(ls.rhs.end(), ss.rhs.begin(), ss.rhs.end());

        break;
      }
      default:
        // do nothing
        break;
    }
  };

  alternative::projected_executions_t< alphabet::stmt_t* > p_alt;
  p_alt.merge(p, is_mergable_alt, do_merge_alt);
  std::cout << "***************************" << std::endl;
  p_alt.merge(p_dummy, is_mergable_alt, do_merge_alt);
  std::cout << "***************************" << std::endl;
  p_alt.merge(p_dummy2, is_mergable_alt, do_merge_alt);
  std::cout << "***************************" << std::endl;
  std::cout << p_alt << std::endl;
  std::cout << "***************************" << std::endl;
#endif

  using label_type2 = size_t;
  std::vector< std::vector< execution_tag_t< const alphabet::stmt_t* > > > set_of_merged_stmts;

  alternative::projected_executions_t< label_type2 > p_alt2;
  auto is_mergable_alt2 = [&] (const label_type2& v, const alphabet::stmt_t& s) {
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

  auto do_merge_alt2 = [&] (label_type2& l, const alphabet::stmt_t& s_source, const projected_execution_t& pexe) {
    auto& v = set_of_merged_stmts[l];
    v.emplace(v.end(), &s_source, pexe.unique_id);
  };

  auto create_label2 = [&] (const alphabet::stmt_t& s, const projected_execution_t& pexe) {
    auto it = set_of_merged_stmts.emplace(set_of_merged_stmts.end());
    it->emplace(it->end(), &s, pexe.unique_id);
    return set_of_merged_stmts.size() - 1;
  };

  p_alt2.merge(p, is_mergable_alt2, do_merge_alt2, create_label2);
  std::cout << "***************************" << std::endl;
  p_alt2.merge(p_dummy, is_mergable_alt2, do_merge_alt2, create_label2);
  std::cout << "***************************" << std::endl;
  p_alt2.merge(p_dummy2, is_mergable_alt2, do_merge_alt2, create_label2);
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

  return EXIT_SUCCESS;
}
