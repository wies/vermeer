#include "execution.h"
#include "xml.h"

#include <cstdlib>
#include <iostream>

void ir2c(std::ostream& out, const exe::execution_t& e) {
  out << "#ifdef COMPILE_FOR_TEST" << ::std::endl;
  out << "#include <assert.h>" << ::std::endl;
  out << "#define assume(cond) assert(cond)" << ::std::endl;
  out << "#endif" << ::std::endl << ::std::endl;
  out << "void main(int argc, char* argv[]) {" << ::std::endl;
  //MakeVarDecls(out);
  out << ::std::endl;
  //MakeGuardedAssignments(out);
  out << "}" << ::std::endl;
}

int main(int argc, char* argv[]) {
  if (argc != 2) {
    std::cerr << "Usage: " << argv[0] << " file1.xml" << std::endl;
    return EXIT_FAILURE;
  }

  exe::execution_t* e = read_execution(argv[1]);

  ir2c(std::cout, *e);

  delete e;

  return EXIT_SUCCESS;
}
