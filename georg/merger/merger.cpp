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

  auto is_mergable = [] (const graph_t<alphabet::stmt_t*>::edge_t e, const alphabet::stmt_t& s) {
    if (e.label->program_location == s.program_location) {
      // can we assume that we have the same type of statement at the same program location?
      assert(e.label->type == s.type);

      return true;
    }

    return false;
  };
  auto do_merge = [] (const graph_t<alphabet::stmt_t*>::edge_t e, const alphabet::stmt_t& s) { };

  ps.merge(p_dummy, is_mergable, do_merge);
  std::cout << ps << std::endl;

  return EXIT_SUCCESS;
}

