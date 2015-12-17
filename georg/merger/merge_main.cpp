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
#include "tag.h"

#include "projected_executions.h"

#include "ssa_map.h"

#include "merger.h"

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
