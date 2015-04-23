#include "causality.hpp"
#include "cbmc.h"

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <queue>

namespace causality {

variablet::variablet(::std::string var_name) : var_name(var_name) {

}

variablet::~variablet() {

}

const ::std::string& variablet::get_name() const {
  return var_name;
}


int_variablet::int_variablet(::std::string var_name) : variablet(var_name) {

}

int_variablet::~int_variablet() {

}

void int_variablet::accept(variable_visitort& visitor) const {
  visitor.visit(*this);
}

void int_variablet::accept(int_term_visitort& visitor) const {
  visitor.visit(*this);
}


boolean_variablet::boolean_variablet(::std::string var_name) : variablet(var_name) {

}

boolean_variablet::~boolean_variablet() {

}

void boolean_variablet::accept(variable_visitort& visitor) const {
  visitor.visit(*this);
}

void boolean_variablet::accept(boolean_term_visitort& visitor) const {
  visitor.visit(*this);
}



boolean_andt::boolean_andt(boolean_termt& t1, boolean_termt& t2) : t1(t1), t2(t2) {

}

boolean_andt::~boolean_andt() {

}

const boolean_termt& boolean_andt::get_subterm1() const {
  return t1;
}

const boolean_termt& boolean_andt::get_subterm2() const {
  return t2;
}

void boolean_andt::accept(boolean_term_visitort& visitor) const {
  visitor.visit(*this);
}


boolean_nott::boolean_nott(boolean_termt& t) : t(t) {

}

boolean_nott::~boolean_nott() {

}

const boolean_termt& boolean_nott::get_subterm() const {
  return t;
}

void boolean_nott::accept(boolean_term_visitort& visitor) const {
  visitor.visit(*this);
}


boolean_constt::boolean_constt(bool value) : value(value) {

}

boolean_constt::~boolean_constt() {

}

bool boolean_constt::get_value() const {
  return value;
}

void boolean_constt::accept(boolean_term_visitort& visitor) const {
  visitor.visit(*this);
}


int_constt::int_constt(int value) : value(value) {

}

int_constt::~int_constt() {

}

int int_constt::get_value() const {
  return value;
}

void int_constt::accept(int_term_visitort& visitor) const {
  visitor.visit(*this);
}


relationt::relationt(relational_operatort op, int_termt& t1, int_termt& t2) : op(op), t1(t1), t2(t2) {

}

relationt::~relationt() {

}

const relational_operatort relationt::get_operator() const {
  return op;
}

const int_termt& relationt::get_subterm1() const {
  return t1;
}

const int_termt& relationt::get_subterm2() const {
  return t2;
}

void relationt::accept(boolean_term_visitort& visitor) const {
  visitor.visit(*this);
}


itet::itet(boolean_termt& condition, int_termt& then_term, int_termt& else_term) : condition(condition), then_term(then_term), else_term(else_term) {

}

itet::~itet() {

}

const boolean_termt& itet::get_condition() const {
  return condition;
}

const int_termt& itet::get_then_term() const {
  return then_term;
}

const int_termt& itet::get_else_term() const {
  return else_term;
}

void itet::accept(int_term_visitort& visitor) const {
  visitor.visit(*this);
}


equationt::~equationt() {

}


empty_equationt::~empty_equationt() {

}

void empty_equationt::accept(equation_visitort& visitor) const {
  visitor.visit(*this);
}


boolean_equationt::boolean_equationt(const boolean_variablet& variable, const boolean_termt& term, const equationt& subequation) : variable(variable), term(term), subequation(subequation) {

}

boolean_equationt::~boolean_equationt() {

}

void boolean_equationt::accept(equation_visitort& visitor) const {
  visitor.visit(*this);
}

const boolean_variablet& boolean_equationt::get_variable() const {
  return variable;
}

const boolean_termt& boolean_equationt::get_term() const {
  return term;
}

const equationt& boolean_equationt::get_subequation() const {
  return subequation;
}


int_equationt::int_equationt(const int_variablet& variable, const int_termt& term, const equationt& subequation) : variable(variable), term(term), subequation(subequation) {

}

int_equationt::~int_equationt() {

}

void int_equationt::accept(equation_visitort& visitor) const {
  visitor.visit(*this);
}

const int_variablet& int_equationt::get_variable() const {
  return variable;
}

const int_termt& int_equationt::get_term() const {
  return term;
}

const equationt& int_equationt::get_subequation() const {
  return subequation;
}



causal_modelt::causal_modelt(const ::std::set< variablet* > exogenous_variables, const ::std::set< variablet* > endogenous_variables, const equationt& equations) : exogenous_variables(exogenous_variables), endogenous_variables(endogenous_variables), equations(equations) {

}

causal_modelt::~causal_modelt() {

}

const ::std::set< variablet* > causal_modelt::get_exogenous_variables() const {
  return exogenous_variables;
}

const ::std::set< variablet* > causal_modelt::get_endogenous_variables() const {
  return endogenous_variables;
}

const equationt& causal_modelt::get_equations() const {
  return equations;
}



causal_logic_formulat::~causal_logic_formulat() {

}


TRUE_causal_logic_formulat::~TRUE_causal_logic_formulat() {

}

void TRUE_causal_logic_formulat::accept(causal_logic_formula_visitort& visitor) {
  visitor.visit(*this);
}


FALSE_causal_logic_formulat::~FALSE_causal_logic_formulat() {

}

void FALSE_causal_logic_formulat::accept(causal_logic_formula_visitort& visitor) {
  visitor.visit(*this);
}


NOT_causal_logic_formulat::NOT_causal_logic_formulat(const causal_logic_formulat& f) : f(f) {

}

NOT_causal_logic_formulat::~NOT_causal_logic_formulat() {

}

void NOT_causal_logic_formulat::accept(causal_logic_formula_visitort& visitor) const {
  visitor.visit(*this);
}

const causal_logic_formulat& NOT_causal_logic_formulat::get_subformula() const {
  return f;
}


AND_causal_logic_formulat::AND_causal_logic_formulat(const causal_logic_formulat& f1, const causal_logic_formulat& f2) : f1(f1), f2(f2) {

}

AND_causal_logic_formulat::~AND_causal_logic_formulat() {

}

void AND_causal_logic_formulat::accept(causal_logic_formula_visitort& visitor) const {
  visitor.visit(*this);
}

const causal_logic_formulat& AND_causal_logic_formulat::get_first_subformula() const {
  return f1;
}

const causal_logic_formulat& AND_causal_logic_formulat::get_second_subformula() const {
  return f2;
}


BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat::BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat(const boolean_variablet& variable, const boolean_constt& value) : variable(variable), value(value) {

}

BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat::~BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat() {

}

void BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat::accept(causal_logic_formula_visitort& visitor) const {
  visitor.visit(*this);
}

const boolean_variablet& BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat::get_variable() const {
  return variable;
}

const boolean_constt& BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat::get_value() const {
  return value;
}


INTEGER_PRIMITIVE_EVENT_causal_logic_formulat::INTEGER_PRIMITIVE_EVENT_causal_logic_formulat(const int_variablet& variable, const int_constt& value) : variable(variable), value(value) {

}

INTEGER_PRIMITIVE_EVENT_causal_logic_formulat::~INTEGER_PRIMITIVE_EVENT_causal_logic_formulat() {

}

void INTEGER_PRIMITIVE_EVENT_causal_logic_formulat::accept(causal_logic_formula_visitort& visitor) const {
  visitor.visit(*this);
}

const int_variablet& INTEGER_PRIMITIVE_EVENT_causal_logic_formulat::get_variable() const {
  return variable;
}

const int_constt& INTEGER_PRIMITIVE_EVENT_causal_logic_formulat::get_value() const {
  return value;
}


BOOLEAN_COUNTERFACTUAL_causal_logic_formulat::BOOLEAN_COUNTERFACTUAL_causal_logic_formulat(const boolean_variablet& variable, const boolean_constt& value, const causal_logic_formulat& subformula) : variable(variable), value(value), subformula(subformula) {

}

BOOLEAN_COUNTERFACTUAL_causal_logic_formulat::~BOOLEAN_COUNTERFACTUAL_causal_logic_formulat() {

}

void BOOLEAN_COUNTERFACTUAL_causal_logic_formulat::accept(causal_logic_formula_visitort& visitor) const {
  visitor.visit(*this);
}

const boolean_variablet& BOOLEAN_COUNTERFACTUAL_causal_logic_formulat::get_variable() const {
  return variable;
}

const boolean_constt& BOOLEAN_COUNTERFACTUAL_causal_logic_formulat::get_value() const {
  return value;
}

const causal_logic_formulat& BOOLEAN_COUNTERFACTUAL_causal_logic_formulat::get_subformula() const {
  return subformula;
}


INTEGER_COUNTERFACTUAL_causal_logic_formulat::INTEGER_COUNTERFACTUAL_causal_logic_formulat(const int_variablet& variable, const int_constt& value, const causal_logic_formulat& subformula) : variable(variable), value(value), subformula(subformula) {

}

INTEGER_COUNTERFACTUAL_causal_logic_formulat::~INTEGER_COUNTERFACTUAL_causal_logic_formulat() {

}

void INTEGER_COUNTERFACTUAL_causal_logic_formulat::accept(causal_logic_formula_visitort& visitor) const {
  visitor.visit(*this);
}

const int_variablet& INTEGER_COUNTERFACTUAL_causal_logic_formulat::get_variable() const {
  return variable;
}

const int_constt& INTEGER_COUNTERFACTUAL_causal_logic_formulat::get_value() const {
  return value;
}

const causal_logic_formulat& INTEGER_COUNTERFACTUAL_causal_logic_formulat::get_subformula() const {
  return subformula;
}



/* context classes */

contextt::~contextt() {

}

empty_contextt::~empty_contextt() {

}

void empty_contextt::accept(context_visitort& visitor) const {

}

boolean_contextt::boolean_contextt(const boolean_variablet& variable, const boolean_constt& value, const contextt& subcontext) : variable(variable), value(value), subcontext(subcontext) {

}

boolean_contextt::~boolean_contextt() {

}

void boolean_contextt::accept(context_visitort& visitor) const {
  visitor.visit(*this);
}

const boolean_variablet& boolean_contextt::get_variable() const {
  return variable;
}

const boolean_constt& boolean_contextt::get_value() const {
  return value;
}

const contextt& boolean_contextt::get_subcontext() const {
  return subcontext;
}

int_contextt::int_contextt(const int_variablet& variable, const int_constt& value, const contextt& subcontext) : variable(variable), value(value), subcontext(subcontext) {

}

int_contextt::~int_contextt() {

}

void int_contextt::accept(context_visitort& visitor) const {
  visitor.visit(*this);
}

const int_variablet& int_contextt::get_variable() const {
  return variable;
}

const int_constt& int_contextt::get_value() const {
  return value;
}

const contextt& int_contextt::get_subcontext() const {
  return subcontext;
}

/* causal logic solver */

causal_logic_solvert::~causal_logic_solvert() {

}

context_visitort::~context_visitort() {

}

class C_context_visitort : public context_visitort {
public:
  C_context_visitort(incremental_cbmct& cbmc) : cbmc(cbmc) {}
  virtual ~C_context_visitort() {}

  virtual void visit(const empty_contextt& context) {
    // do nothing
  }

  virtual void visit(const boolean_contextt& context) {
    ::std::stringstream strstr;
    strstr << "c::foo::1::" << context.get_variable().get_name() << "!0@1#1";
    cbmc.assume_value(strstr.str(), context.get_value().get_value()?1:0);
    context.get_subcontext().accept(*this);
  }

  virtual void visit(const int_contextt& context) {
    ::std::stringstream strstr;
    strstr << "c::foo::1::" << context.get_variable().get_name() << "!0@1#1";
    cbmc.assume_value(strstr.str(), context.get_value().get_value());
    context.get_subcontext().accept(*this);
  }

protected:
  incremental_cbmct& cbmc;

};

class ExtractValue_variable_visitort : public variable_visitort {
public:
  ExtractValue_variable_visitort(incremental_cbmct& cbmc, const contextt& subcontext) : cbmc(cbmc), subcontext(subcontext) {}
  virtual ~ExtractValue_variable_visitort() {}

  void visit(const int_variablet& var) {
    ::std::stringstream strstr;
    strstr << "c::foo::1::" << var.get_name() << "!0@1#2";

    // TODO we have to free the memory
    int_constt* c = new int_constt((int)cbmc.query_value(strstr.str()));
    context = new int_contextt(var, *c, subcontext);
  }

  void visit(const boolean_variablet& var) {
    ::std::stringstream strstr;
    strstr << "c::foo::1::" << var.get_name() << "!0@1#2";

    // TODO we have to free the memory
    boolean_constt* c = new boolean_constt((bool)cbmc.query_value(strstr.str()));
    context = new boolean_contextt(var, *c, subcontext);
  }

  contextt* get_context() {
    return context;
  }

protected:
  incremental_cbmct& cbmc;
  const contextt& subcontext;
  contextt* context;

};

bool causal_logic_solvert::solve(const causal_modelt& model, const contextt& context, const causal_logic_formulat& formula, contextt*& ctxt) {
  ::std::ofstream tmp_c("causality_tmp.c");

  translate_to_C_program(model, context, formula, tmp_c);

  tmp_c.close();

  // TODO make cbmc directory configurable
  incremental_cbmct inc_cbmc("/home/andi/mpc-synthesis/cbmc-4.9-src/cbmc-4.9-incremental/src/cbmc/cbmc", 10);

  inc_cbmc.start("causality_tmp.c", "causality_tmp.out");

  //inc_cbmc.list_variable_names();

  C_context_visitort context_visitor(inc_cbmc);
  context.accept(context_visitor);

  bool result = inc_cbmc.check();

  ctxt = new empty_contextt;

  if (result) {
    // Since the equations are deterministic and the context determines all free variables, if there is a solution it is unique.
    ::std::cout << "SAT" << ::std::endl;

    for (auto variable : model.get_endogenous_variables()) {
      ExtractValue_variable_visitort evvv(inc_cbmc, *ctxt);
      variable->accept(evvv);
      ctxt = evvv.get_context();
    }
  } 
  else {
    ::std::cout << "UNSAT" << ::std::endl;
  }

  inc_cbmc.stop();

  return result; // TODO shall we flip this? Think about validity in the causality context!
}

/*
contextt causal_logic_solvert::existsContext(const causal_modelt& model, const contextt& partial_context, const causal_logic_formulat& formula) {
  return empty_contextt.get_instance();
}
*/

class variable_declaration_visitort : public variable_visitort {
public:
  variable_declaration_visitort(::std::ostream& out) : out(out) {}
  virtual ~variable_declaration_visitort() {}

  virtual void visit(const int_variablet& variable) {
    out << "  unsigned char " << variable.get_name() << ";" << ::std::endl;
  }

  virtual void visit(const boolean_variablet& variable) { 
    out << "  unsigned char " << variable.get_name() << ";" << ::std::endl; // TODO fix
  }

protected:
  ::std::ostream& out;

};

class C_boolean_term_visitort;

class C_int_term_visitort : public int_term_visitort {
public:
  C_int_term_visitort(::std::ostream& out);
  virtual ~C_int_term_visitort();

  virtual void visit(const int_variablet& v) {
    out << v.get_name();
  }

  virtual void visit(const int_constt& c) {
    out << c.get_value();
  }

  virtual void visit(const itet& i); 

protected:
  ::std::ostream& out;

};

class C_boolean_term_visitort : public boolean_term_visitort {
public:
  C_boolean_term_visitort(::std::ostream& out) : out(out), ivis(out) {}
  virtual ~C_boolean_term_visitort() {}

  virtual void visit(const boolean_variablet& v) {
    out << v.get_name();
  }

  virtual void visit(const boolean_andt& a) {
    out << "(";
    a.get_subterm1().accept(*this);
    out << " && ";
    a.get_subterm2().accept(*this);
    out << ")";
  }

  virtual void visit(const boolean_nott& n) {
    out << "(!";
    n.get_subterm().accept(*this);
    out << ")";
  }

  virtual void visit(const boolean_constt& c) {
    out << c.get_value();
  }

  virtual void visit(const relationt& r) {
    out << "(";
    r.get_subterm1().accept(ivis);
    switch(r.get_operator()) {
    case EQ:
      out << " == ";
      break;
    case NEQ:
      out << " != ";
      break;
    case GT:
      out << " > ";
      break;
    case LT:
      out << " < ";
      break;
    }
    r.get_subterm2().accept(ivis);
    out << ")";
  }

protected:
  ::std::ostream& out;
  C_int_term_visitort ivis;

};

C_int_term_visitort::C_int_term_visitort(::std::ostream& out) : out(out) {

}

C_int_term_visitort::~C_int_term_visitort() {

}

void C_int_term_visitort::visit(const itet& i) {
  C_boolean_term_visitort bvis(out);

  out << "(";
  i.get_condition().accept(bvis);
  out << ") ? (";
  i.get_then_term().accept(*this);
  out << ") : (";
  i.get_else_term().accept(*this);
  out << ")";
}


class C_equation_visitort : public equation_visitort {
public:
  C_equation_visitort(::std::ostream& out) : out(out), ivis(out), bvis(out) {}
  virtual ~C_equation_visitort() {}

  virtual void visit(const empty_equationt& equation) {
    // do nothing
  }

  virtual void visit(const boolean_equationt& equation) {
    out << "  ";
    out << equation.get_variable().get_name() << " = ";
    equation.get_term().accept(bvis);
    out << ";" << ::std::endl;
    equation.get_subequation().accept(*this);
  }

  virtual void visit(const int_equationt& equation) {
    out << "  ";
    out << equation.get_variable().get_name() << " = ";
    equation.get_term().accept(ivis);
    out << ";" << ::std::endl;
    equation.get_subequation().accept(*this);
  }

protected:
  ::std::ostream& out;
  C_int_term_visitort ivis;
  C_boolean_term_visitort bvis;

};

class C_causal_logic_formula_visitort : public causal_logic_formula_visitort {
public:
  C_causal_logic_formula_visitort(::std::ostream& out) : out(out), bvis(out), ivis(out) {}
  virtual ~C_causal_logic_formula_visitort() {}

  virtual void visit(const TRUE_causal_logic_formulat& True) {
    out << "1";
  }

  virtual void visit(const FALSE_causal_logic_formulat& False) {
    out << "0";
  }

  virtual void visit(const NOT_causal_logic_formulat& Not) {
    out << "(!";
    Not.get_subformula().accept(*this);
    out << ")";
  }

  virtual void visit(const AND_causal_logic_formulat& And) {
    out << "(";
    And.get_first_subformula().accept(*this);
    out << " && ";
    And.get_second_subformula().accept(*this);
    out << ")";
  }

  virtual void visit(const BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat& primitive_event) {
    out << "(";
    primitive_event.get_variable().accept(bvis);
    out << " == ";
    primitive_event.get_value().accept(bvis);
    out << ")";
  }

  virtual void visit(const INTEGER_PRIMITIVE_EVENT_causal_logic_formulat& primitive_event) {
    out << "(";
    primitive_event.get_variable().accept(ivis);
    out << " == ";
    primitive_event.get_value().accept(ivis);
    out << ")";
  }

  virtual void visit(const BOOLEAN_COUNTERFACTUAL_causal_logic_formulat& counterfactual) {
    out << "TODO";
  }

  virtual void visit(const INTEGER_COUNTERFACTUAL_causal_logic_formulat& counterfactual) {
    out << "TODO";
  }

protected:
  ::std::ostream& out;
  C_boolean_term_visitort bvis;
  C_int_term_visitort ivis;

};

void causal_logic_solvert::translate_to_C_program(const causal_modelt& model, const contextt& context, const causal_logic_formulat& formula, ::std::ostream& out) {
  out << "void foo() {" << ::std::endl;

  variable_declaration_visitort decl_visitor(out);

  out << "  // declarations of exogenous variables" << ::std::endl;
  for (variablet* var : model.get_exogenous_variables()) {
    var->accept(decl_visitor);
  } 
  out << ::std::endl;

  out << "  // declarations of endogenous variables" << ::std::endl;
  for (variablet* var : model.get_endogenous_variables()) {
    var->accept(decl_visitor);
  } 
  out << ::std::endl;

  out << "  // structural equations" << ::std::endl;
  C_equation_visitort equ_visitor(out);
  model.get_equations().accept(equ_visitor);
  out << ::std::endl;

  out << "  // formula" << ::std::endl;
  out << "  assert(!(";
  
  C_causal_logic_formula_visitort logic_visitor(out);
  formula.accept(logic_visitor);

  out << "));" << ::std::endl;
  out << "}" << ::std::endl;
}

class context_printert : public context_visitort {
public:
  context_printert(::std::ostream& out) : out(out) {}
  virtual ~context_printert() {}
  
  virtual void visit(const empty_contextt& c) {
    // do nothing
  }

  virtual void visit(const int_contextt& c) {
    out << c.get_variable().get_name() << " = " << c.get_value().get_value() << ::std::endl;
    c.get_subcontext().accept(*this);
  }

  virtual void visit(const boolean_contextt& c) {
    out << c.get_variable().get_name() << " = " << (c.get_value().get_value()?"true":"false") << ::std::endl;
    c.get_subcontext().accept(*this);
  }

protected:
  ::std::ostream& out;

};


class filter_equation_visitort : public equation_visitort {
public:
  filter_equation_visitort(::std::set< variablet * >& variables_that_should_not_appear_in_the_equations_anymore) : variables(variables_that_should_not_appear_in_the_equations_anymore) {}
  virtual ~filter_equation_visitort() {}

  virtual void visit(const empty_equationt& equation) {
    // TODO we store this first in our new set of equations
    last_equation = new empty_equationt; // TODO we have to free that again!
  }

  virtual void visit(const boolean_equationt& equation) {
    // we want to preserve the order of the equations, therefore we process post-order
    equation.get_subequation().accept(*this);

    if (variables.find((variablet*)&(equation.get_variable())) == variables.end()) {
      // keep equation, i.e., create a copy
      equationt* tmp = new boolean_equationt(equation.get_variable(), equation.get_term(), *last_equation);
      last_equation = tmp;
    }
  }

  virtual void visit(const int_equationt& equation) {
    // we want to preserve the order of the equations, therefore we process post-order
    equation.get_subequation().accept(*this);

    if (variables.find((variablet*)&(equation.get_variable())) == variables.end()) {
      // keep equation, i.e., create a copy
      equationt* tmp = new int_equationt(equation.get_variable(), equation.get_term(), *last_equation);
      last_equation = tmp;
    }
  }

  virtual equationt* get_filtered_equation() {
    return last_equation;
  }

protected:
  ::std::set< variablet * >& variables;
  equationt* last_equation;
};


bool causal_logic_solvert::check_AC2a_and_AC2b(const causal_modelt& model, const contextt& context, const causal_logic_formulat& explanandum, const contextt& solution, const ::std::vector< variablet* >& endogenous_variables, const ::std::vector< bool >& candidate, const ::std::vector< bool >& partition) {
  ::std::set< variablet* > new_exogenous_variables(model.get_exogenous_variables());
  ::std::set< variablet* > new_endogenous_variables;

  ::std::set< variablet* > gamma_and_W;

  for (unsigned i = 0; i < candidate.size(); i++) {
    if (candidate[i] || !partition[i]) { // if partition[i] is set to false, then it is a variable in W
      gamma_and_W.insert(endogenous_variables[i]);
      new_exogenous_variables.insert(endogenous_variables[i]);
    }
    else {
      new_endogenous_variables.insert(endogenous_variables[i]);
    }
  }

  filter_equation_visitort filter(gamma_and_W);
  model.get_equations().accept(filter);
  equationt* filtered_equations = filter.get_filtered_equation();

  causal_modelt new_model(new_exogenous_variables, new_endogenous_variables, *filtered_equations);

  contextt* new_solution = NULL;
  NOT_causal_logic_formulat negated_explanandum(explanandum);
  if (solve(new_model, context, negated_explanandum, new_solution)) {
    // this has to become a synthesis loop

  }

  exit(-1);

  return false;
}

bool causal_logic_solvert::is_actual_cause(const causal_modelt& model, const contextt& context, const causal_logic_formulat& explanandum, const contextt& solution, const ::std::vector< variablet* >& endogenous_variables, const ::std::vector< bool >& candidate) {

  // We have to consider all partitions

  // 1) determine how many 1s are set in candidate
  unsigned nr_of_ones = 0;
  for (auto b : candidate) {
    if (b) {
      nr_of_ones++;
    }
  }

  // 2) create new bit vector
  ::std::vector< bool > bits;
  for (unsigned i = 0; i < candidate.size() - nr_of_ones; i++) {
    bits.push_back(false);
  }

  ::std::queue< ::std::vector< bool > > q;
  q.push(bits);

  while (!q.empty()) {
    auto b = q.front();
    q.pop();

    // create partition
    ::std::vector< bool > partition(candidate);
    for (unsigned i = 0, j = 0; i < partition.size(); i++) {
      if (!partition[i]) {
        partition[i] = partition[i] || b[j];
        j++;
      }
    }

    // do checks
    if (check_AC2a_and_AC2b(model, context, explanandum, solution, endogenous_variables, candidate, partition)) {
      return true;
    }

    unsigned last_set = -1;
    for (unsigned j = 0; j < b.size(); j++) {
      unsigned i = b.size() - 1 - j;

      if (b[i]) {
        last_set = i;
        break;
      }
    }

    for (unsigned i = last_set + 1; i < b.size(); i++) {
      if (!b[i]) {
        b[i] = true;
        q.push(b);
        b[i] = false;
      }
    }
  }

  return false;
}

void causal_logic_solvert::compute_actual_causes(const causal_modelt& model, const contextt& context, const causal_logic_formulat& explanandum) {
  // 1) solve the situation (model, context) 
  ::causality::contextt* solution = NULL;
  solve(model, context, explanandum, solution);

  // 2) extract all primitive events (they are the basic blocks for actual causes)
  context_printert printer(::std::cout);
  solution->accept(printer);

  // Note that AC3 is already satisfied by our enumeration strategy

  // 3) AC2 ...
  ::std::vector< bool > bits;
  ::std::vector< variablet* > vars;
  // initialize
  for (auto var : model.get_endogenous_variables()) {
    bits.push_back(false);
    vars.push_back(var);

    // TODO remove
    //if (bits.size() >= 3) break;
  }

  ::std::queue< ::std::vector< bool > > q;
  for (unsigned i = 0; i < vars.size(); i++) {
    bits[i] = true;

    q.push(bits);

    bits[i] = false;
  }

  ::std::set< ::std::vector< bool > > actual_causes;

  while (!q.empty()) {
    auto b = q.front();
    q.pop();

    // check whether b is an actual cause
    if (is_actual_cause(model, context, explanandum, *solution, vars, b)) {
      actual_causes.insert(b);

      exit(-1); // just for now TODO: remove

      continue;
    }

    // if b is not an actual cause then produce all successors
    unsigned last_set = 0;
    for (unsigned i = b.size() - 1; i >= 0; i--) {
      if (b[i]) {
        last_set = i;
        break;
      }
    }

    for (unsigned i = last_set + 1; i < b.size(); i++) {
      if (!b[i]) {
        b[i] = true;
        q.push(b);
        b[i] = false;
      }
    }
  }

  // TODO return actual_causes?

}

}

