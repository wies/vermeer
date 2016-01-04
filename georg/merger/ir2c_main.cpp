#include "execution.h"
#include "xml.h"

#include <cstdlib>
#include <iostream>

struct ir2c_visitor_t : public exe::stmt_visitor_t {

private:
  std::ostream& out;

public:
  ir2c_visitor_t(std::ostream& out_) : out(out_) {}

  virtual ~ir2c_visitor_t() {}

  virtual void visit_execution(exe::execution_t& e) override {
  }

  virtual void visit_assignment(exe::assignment_t& a) override {
    // TODO implement guard
    // TODO implement C statement
    out << "assignment";
  }

  virtual void visit_assertion(exe::assertion_t& a) override {
    // TODO implement guard
    // TODO implement C statement
    out << "assertion";
  }

  virtual void visit_assumption(exe::assumption_t& a) override {
    // TODO implement guard
    // TODO implement C statement
    out << "assumption";
  }

};

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

  ir2c_visitor_t v(std::cout);
  for (const auto& s : e.statements) {
    out << "  T_" << s->program_location.thread << "_" << s->position_in_execution << "_" << s->program_location.thread << ": ";
    s->accept(v);
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
