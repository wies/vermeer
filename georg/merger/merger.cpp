#include <cstdlib>
#include <iostream>

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

  std::cout << e << std::endl;
  std::cout << "******************************************" << std::endl;

  projected_execution_t p(e);
  std::cout << p << std::endl;
  std::cout << "******************************************" << std::endl;

  projected_executions_t ps(p, 0);
  std::cout << ps << std::endl;
  std::cout << "******************************************" << std::endl;

  exe::execution_t e_dummy = read_execution("example_dummy.xml");
  projected_execution_t p_dummy(e_dummy);

  auto is_mergable = [] (const graph_t<int>::edge_t e, const alphabet::stmt_t& s) { return (e.label == s.program_location.position); };
  auto do_merge = [] (const graph_t<int>::edge_t e, const alphabet::stmt_t& s) {  };

  ps.merge(p_dummy, is_mergable, do_merge, 1);
  std::cout << ps << std::endl;

  return EXIT_SUCCESS;
}

