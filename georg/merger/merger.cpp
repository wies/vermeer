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
  ps.merge(p);
  std::cout << ps << std::endl;

  return EXIT_SUCCESS;
}

