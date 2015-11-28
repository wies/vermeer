#include <cstdlib>
#include <iostream>

#include "error.h"
#include "trace.h"
#include "xml.h"

int main(int argc, char* argv[]) {
  execution_t e = read_execution("example.xml");

  std::cout << e << std::endl;

  return EXIT_SUCCESS;
}

