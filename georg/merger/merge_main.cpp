#include "merger.h"

#include <cstdlib>
#include <iostream>
#include <set>
#include <string>

int main(int argc, char* argv[]) {
  if (argc < 2) {
    std::cerr << "Usage: " << argv[0] << " file1.xml file2.xml ..." << std::endl;
    return EXIT_FAILURE;
  }

  std::set< std::string > files;
  for (int i = 1; i < argc; ++i) {
    files.insert(argv[i]);
  }

  merge(files);

  return EXIT_SUCCESS;
}
