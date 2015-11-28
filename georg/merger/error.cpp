#include "error.h"

#include <iostream>
#include <cstdlib>

void merge_error(const char* file, int line, const char* text) {
  std::cerr << std::endl << "*** ERROR at line " << line << " in file \"" << file << "\": " << text << std::endl;
  exit(EXIT_FAILURE);
}
