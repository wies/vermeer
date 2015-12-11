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

int main(int argc, char* argv[]) {
  exe::execution_t e = read_execution("example.xml");
  std::cout << e << std::endl << "******************************************" << std::endl;

  projected_execution_t p(e, 0);
  std::cout << p << std::endl << "******************************************" << std::endl;

  projected_executions_t ps(p);
  std::cout << ps << std::endl << "******************************************" << std::endl;

  exe::execution_t e_dummy = read_execution("example_dummy.xml");
  projected_execution_t p_dummy(e_dummy, 1);

  exe::execution_t e_dummy2 = read_execution("example_dummy2.xml");
  projected_execution_t p_dummy2(e_dummy2, 2);


  auto is_mergable = [] (const graph_t<alphabet::stmt_t*>::edge_t e, const alphabet::stmt_t& s) {
    if (e.label->program_location == s.program_location) {
      // can we assume that we have the same type of statement at the same program location?
      assert(e.label->type == s.type);

      // check guards
      if (e.label->guards.size() != s.guards.size()) {
        return false;
      }

      for (size_t i = 0; i < s.guards.size(); i++) {
        if (e.label->guards[i] != s.guards[i]) {
          return false;
        }
      }

      // do further equality checks
      switch (s.type) {
        case alphabet::stmt_t::PI_ASSIGNMENT:
          {
            alphabet::pi_assignment_t* ls = (alphabet::pi_assignment_t*)e.label;
            alphabet::pi_assignment_t* ss = (alphabet::pi_assignment_t*)&s;

            if (ls->local_variable != ss->local_variable) {
              return false;
            }

            break;
          }
        case alphabet::stmt_t::LOCAL_ASSIGNMENT:
          {
            alphabet::local_assignment_t* ls = (alphabet::local_assignment_t*)e.label;
            alphabet::local_assignment_t* ss = (alphabet::local_assignment_t*)&s;

            if (ls->local_variable != ss->local_variable) {
              return false;
            }

            break;
          }
        case alphabet::stmt_t::GLOBAL_ASSIGNMENT:
          {
            alphabet::global_assignment_t* ls = (alphabet::global_assignment_t*)e.label;
            alphabet::global_assignment_t* ss = (alphabet::global_assignment_t*)&s;

            if (ls->shared_variable != ss->shared_variable) {
              return false;
            }

            break;
          }
        default:
          // TODO implement other equality checks
          break;
      }

      return true;
    }

    return false;
  };

  auto do_merge = [] (const graph_t<alphabet::stmt_t*>::edge_t e, const alphabet::stmt_t& s) {
    switch (s.type) {
      case alphabet::stmt_t::PI_ASSIGNMENT:
      {
        alphabet::pi_assignment_t* ls = (alphabet::pi_assignment_t*)e.label;
        alphabet::pi_assignment_t* ss = (alphabet::pi_assignment_t*)&s;

        ls->shared_variables.insert(ls->shared_variables.end(), ss->shared_variables.begin(), ss->shared_variables.end());

        break;
      }
      case alphabet::stmt_t::LOCAL_ASSIGNMENT:
      {
        alphabet::local_assignment_t* ls = (alphabet::local_assignment_t*)e.label;
        alphabet::local_assignment_t* ss = (alphabet::local_assignment_t*)&s;

        ls->rhs.insert(ls->rhs.end(), ss->rhs.begin(), ss->rhs.end());

        break;
      }
      case alphabet::stmt_t::GLOBAL_ASSIGNMENT:
      {
        alphabet::global_assignment_t* ls = (alphabet::global_assignment_t*)e.label;
        alphabet::global_assignment_t* ss = (alphabet::global_assignment_t*)&s;

        ls->rhs.insert(ls->rhs.end(), ss->rhs.begin(), ss->rhs.end());

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

  alphabet::execution_tag_t<int> t(43, 0);
  alphabet::execution_tag_t<int> t2(132, 0);
  alphabet::execution_tag_t<int> t3(43, 1);
  std::cout << t << " " << t2 << " " << t3 << std::endl;
  std::cout << (t == t) << std::endl;
  std::cout << (t != t) << std::endl;
  std::cout << (t == t2) << std::endl;
  std::cout << (t == t3) << std::endl;

  return EXIT_SUCCESS;
}

