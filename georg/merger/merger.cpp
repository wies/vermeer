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

  local_execution_extractor_t lee;
  lee.variable_declarations.insert(lee.variable_declarations.end(), e.variable_declarations.begin(), e.variable_declarations.end()); // TODO replace
  e.accept(lee);

  for (auto& p : lee.local_executions) {
    std::cout << "Thread " << p.first << ": " << p.second.size() << std::endl;
    for (auto& s : p.second) {
      std::cout << *s << std::endl;
    }
    std::cout << std::endl;
  }

  return EXIT_SUCCESS;
}

