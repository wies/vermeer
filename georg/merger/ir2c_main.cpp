#include "execution.h"
#include "xml.h"

#include <cstdlib>
#include <iostream>

void ir2c(std::ostream& out, const exe::execution_t& e) {
  out << "#ifdef COMPILE_FOR_TEST" << std::endl;
  out << "#include <assert.h>" << std::endl;
  out << "#define assume(cond) assert(cond)" << std::endl;
  out << "#endif" << std::endl << std::endl;
  out << "void main(int argc, char* argv[]) {" << std::endl;

  // TODO variable names are missing in the intermediate representation
  for (const auto& vd : e.variable_declarations) {
    out << "  int x_" << vd.variable << "_" << vd.ssa_index << ";//" << std::endl;
  }

  out << std::endl;

  for (const auto& s : e.statements) {
    out << "  T_" << s->program_location.thread << "_" << s->position_in_execution << "_" << s->program_location.thread << ": ";
    out << std::endl;
  }

  out << "}" << std::endl;
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
