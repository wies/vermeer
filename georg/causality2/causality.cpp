#include "causality.hpp"

#include <iostream>

namespace causality {

variablet::variablet(::std::string var_name) : var_name(var_name) {

}

variablet::~variablet() {

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

bool causal_logic_solvert::solve(const causal_modelt& model, const contextt& context, const causal_logic_formulat& formula) {
  translate_to_C_program(model, context, formula, ::std::cout);

  return true; // TODO fix
}

/*
contextt causal_logic_solvert::existsContext(const causal_modelt& model, const contextt& partial_context, const causal_logic_formulat& formula) {
  return empty_contextt.get_instance();
}
*/

void causal_logic_solvert::translate_to_C_program(const causal_modelt& model, const contextt& context, const causal_logic_formulat& formula, ::std::ostream& out) {
  out << "void foo() {" << ::std::endl;
  out << "}" << ::std::endl;
}

}

