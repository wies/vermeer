#include <cstdlib>
#include <iostream>

#include "error.h"
#include "trace.h"
#include "xml.h"

int main(int argc, char* argv[]) {
  trace_t t = read_trace("example.xml");

  std::cout << t << std::endl;

  return EXIT_SUCCESS;
}

