#include "causality.hpp"

namespace causality {

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



/* causal logic solver */

causal_logic_solvert::~causal_logic_solvert() {

}

void causal_logic_solvert::solve(causal_modelt& model, contextt& context, causal_logic_formulat& formula) {

}

}

