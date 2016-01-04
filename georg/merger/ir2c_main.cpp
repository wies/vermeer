#include "execution.h"
#include "xml.h"

#include <cstdlib>
#include <iostream>
#include <sstream>

std::string get_variable_name(const exe::variable_declaration_t& vd) {
  std::stringstream sstr;
  sstr << "x_" << vd.variable << "_" << vd.ssa_index;
  return sstr.str();
}

std::string translate_term(const expr::term_t<int> t, const std::vector<exe::variable_declaration_t>& vds) {
  std::stringstream out;

  if (t.products.empty()) {
    out << t.constant;
  }
  else {
    bool first = true;
    for (const auto& lp : t.products) {
      if (first) {
        first = false;
      } else {
        out << " + ";
      }
      if (lp.factor != 1) {
        out << lp.factor << " * ";
      }
      out << get_variable_name(vds[lp.variable]);
    }

    if (t.constant > 0) {
      out << " + " << t.constant;
    } else if (t.constant < 0) {
      out << " " << t.constant;
    }
  }

  return out.str();
}

std::string translate_expression(const expr::expr_t<int> e, const std::vector<exe::variable_declaration_t>& vds) {
  std::stringstream out;
  out << "0 " << ops2strC(e.op) << " " << translate_term(e.term, vds);
  return out.str();
}

std::string translate_expressions(const std::vector<expr::expr_t<int>> exprs, const std::vector<exe::variable_declaration_t>& vds) {
  std::stringstream out;

  if (exprs.size() > 1) {
    out << "(";
  }

  bool first = true;
  for (const auto& expr : exprs) {
    if (first) {
      first = false;
    } else {
      out << ") && (";
    }
    out << translate_expression(expr, vds);
  }

  if (exprs.size() > 1) {
    out << ")";
  }

  return out.str();
}

struct ir2c_visitor_t : public exe::stmt_visitor_t {

private:
  std::ostream& out;
  const exe::execution_t& e;

public:
  ir2c_visitor_t(std::ostream& out_, const exe::execution_t& e_) : out(out_), e(e_) {}

  virtual ~ir2c_visitor_t() {}

  virtual void visit_execution(exe::execution_t& e) override {
  }

  virtual void visit_assignment(exe::assignment_t& a) override {
    // TODO implement guards
    out << get_variable_name(e.variable_declarations[a.variable_id]) << " = " << translate_term(a.rhs, e.variable_declarations);
  }

  virtual void visit_assertion(exe::assertion_t& a) override {
    // TODO implement guards
    out << "assert(" << translate_expressions(a.exprs, e.variable_declarations) << ")";
  }

  virtual void visit_assumption(exe::assumption_t& a) override {
    // TODO implement guards
    out << "assume(" << translate_expressions(a.exprs, e.variable_declarations) << ")";
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
    out << "  int " << get_variable_name(vd) << ";//" << std::endl;
  }

  out << std::endl;

  ir2c_visitor_t v(std::cout, e);
  for (const auto& s : e.statements) {
    out << "  T_" << s->program_location.thread << "_" << s->position_in_execution << "_" << s->program_location.thread << ": ";
    s->accept(v);
    out << ";" << std::endl;
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
