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

  alphabet::projected_execution_t p;
  local_execution_extractor_t lee(p);
  lee.variable_declarations.insert(lee.variable_declarations.end(), e.variable_declarations.begin(), e.variable_declarations.end()); // TODO replace
  e.accept(lee);
  std::cout << p << std::endl;
  std::cout << "******************************************" << std::endl;

  alphabet::projected_executions_t ps(p);
  std::cout << ps << std::endl;
  std::cout << "******************************************" << std::endl;
  //ps.merge(p);
  //std::cout << ps << std::endl;

  exe::execution_t e_dummy = read_execution("example_dummy.xml");
  alphabet::projected_execution_t p_dummy;
  local_execution_extractor_t lee_dummy(p_dummy);
  // TODO this should be done in the accept visit method of the execution! Make sure that the lee-variable-declarations are empty!
  lee_dummy.variable_declarations.insert(lee_dummy.variable_declarations.end(), e.variable_declarations.begin(), e.variable_declarations.end());
  e_dummy.accept(lee_dummy);
  //std::cout << p_dummy << std::endl;

  auto is_mergable = [] (const graph_t<int>::edge_t e, const alphabet::stmt_t& s) { return (e.label == s.program_location.position); };
  auto do_merge = [] (const graph_t<int>::edge_t e, const alphabet::stmt_t& s) {  };

  ps.merge(p_dummy, is_mergable, do_merge);
  std::cout << ps << std::endl;

  return EXIT_SUCCESS;
}

