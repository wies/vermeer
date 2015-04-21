#ifndef CAUSALITY_HPP
#define CAUSALITY_HPP

#include <string>
#include <set>
#include <iostream>

namespace causality {

class int_term_visitort;

class int_termt {
public:
  virtual ~int_termt() {};

  virtual void accept(int_term_visitort& visitor) const = 0;

};

class boolean_term_visitort;

class boolean_termt {
public:
  virtual ~boolean_termt() {};

  virtual void accept(boolean_term_visitort& visitor) const = 0;

};

class variable_visitort;

class variablet {
public:
  variablet(::std::string var_name);
  virtual ~variablet();

  virtual void accept(variable_visitort& visitor) const = 0;
 
  virtual const ::std::string& get_name() const;

protected:
  ::std::string var_name;

};

class int_variablet : public int_termt, public variablet {
public:
  int_variablet(::std::string var_name);
  virtual ~int_variablet();

  virtual void accept(variable_visitort& visitor) const;
  virtual void accept(int_term_visitort& visitor) const;

};

class boolean_variablet : public boolean_termt, public variablet {
public:
  boolean_variablet(::std::string var_name);
  virtual ~boolean_variablet();

  virtual void accept(variable_visitort& visitor) const;
  virtual void accept(boolean_term_visitort& visitor) const;

};

class variable_visitort {
public:
  virtual ~variable_visitort() {}

  virtual void visit(const int_variablet& variable) = 0;
  virtual void visit(const boolean_variablet& variable) = 0;

};

class boolean_andt : public boolean_termt {
public:
  boolean_andt(boolean_termt& t1, boolean_termt& t2);
  virtual ~boolean_andt();

  virtual const boolean_termt& get_subterm1() const;
  virtual const boolean_termt& get_subterm2() const;

  virtual void accept(boolean_term_visitort& visitor) const;

protected:
  const boolean_termt& t1;
  const boolean_termt& t2;
};

class boolean_nott : public boolean_termt {
public:
  boolean_nott(boolean_termt& t);
  virtual ~boolean_nott();

  virtual const boolean_termt& get_subterm() const;

  virtual void accept(boolean_term_visitort& visitor) const;

protected:
  boolean_termt& t;
};

class boolean_constt : public boolean_termt {
public:
  boolean_constt(bool value);
  virtual ~boolean_constt();

  virtual bool get_value() const;

  virtual void accept(boolean_term_visitort& visitor) const;

protected:
  bool value;

};

enum relational_operatort {
  EQ, NEQ, GT, LT
};

class relationt : public boolean_termt {
public:
  relationt(relational_operatort op, int_termt& t1, int_termt& t2);
  virtual ~relationt();

  virtual const relational_operatort get_operator() const;

  virtual const int_termt& get_subterm1() const;
  virtual const int_termt& get_subterm2() const;

  virtual void accept(boolean_term_visitort& visitor) const;

protected:
  const relational_operatort op;
  const int_termt& t1;
  const int_termt& t2;
};

class boolean_term_visitort {
public:
  virtual ~boolean_term_visitort() {}

  virtual void visit(const boolean_variablet& v) = 0;
  virtual void visit(const boolean_andt& a) = 0;
  virtual void visit(const boolean_nott& n) = 0;
  virtual void visit(const boolean_constt& c) = 0;
  virtual void visit(const relationt& r) = 0;

};

class int_constt : public int_termt {
public:
  int_constt(int value);
  virtual ~int_constt();

  virtual int get_value() const;

  virtual void accept(int_term_visitort& visitor) const;

protected:
  int value;
};

class itet : public int_termt {
public:
  itet(boolean_termt& condition, int_termt& then_term, int_termt& else_term);
  virtual ~itet();

  virtual const boolean_termt& get_condition() const;

  virtual const int_termt& get_then_term() const;
  virtual const int_termt& get_else_term() const;

  virtual void accept(int_term_visitort& visitor) const;

protected:
  const boolean_termt& condition;
  const int_termt& then_term;
  const int_termt& else_term;
};

class int_term_visitort {
public:
  virtual ~int_term_visitort() {}

  virtual void visit(const int_variablet& v) = 0;
  virtual void visit(const int_constt& c) = 0;
  virtual void visit(const itet& i) = 0;

};

class equation_visitort;

class equationt {
public:
  virtual ~equationt();

  virtual void accept(equation_visitort& visitor) const = 0;

};

class empty_equationt : public equationt {
public:
  virtual ~empty_equationt();

  virtual void accept(equation_visitort& visitor) const;

};

class boolean_equationt : public equationt {
public:
  boolean_equationt(const boolean_variablet& variable, const boolean_termt& term, const equationt& subequation);
  virtual ~boolean_equationt();

  virtual void accept(equation_visitort& visitor) const;

  virtual const boolean_variablet& get_variable() const;
  virtual const boolean_termt& get_term() const;
  virtual const equationt& get_subequation() const;

protected:
  const boolean_variablet& variable;
  const boolean_termt& term;
  const equationt& subequation;

};

class int_equationt : public equationt {
public:
  int_equationt(const int_variablet& variable, const int_termt& term, const equationt& subequation);
  virtual ~int_equationt();

  virtual void accept(equation_visitort& visitor) const;

  virtual const int_variablet& get_variable() const;
  virtual const int_termt& get_term() const;
  virtual const equationt& get_subequation() const;

protected:
  const int_variablet& variable;
  const int_termt& term;
  const equationt& subequation;

};

class equation_visitort {
public:
  virtual ~equation_visitort() {}

  virtual void visit(const empty_equationt& equation) = 0;
  virtual void visit(const boolean_equationt& equation) = 0;
  virtual void visit(const int_equationt& equation) = 0;

};

class causal_modelt {
public:
  causal_modelt(const ::std::set< variablet* > exogenous_variables, const ::std::set< variablet* > endogenous_variables, const equationt& equations);
  virtual ~causal_modelt();

  const ::std::set< variablet* > get_exogenous_variables() const;
  const ::std::set< variablet* > get_endogenous_variables() const;
  const equationt& get_equations() const;

protected:
  const ::std::set< variablet* > exogenous_variables;
  const ::std::set< variablet* > endogenous_variables;
  const equationt& equations;

};


// TODO create namespace causal_logic

class causal_logic_formula_visitort;

class causal_logic_formulat {
public:
  virtual ~causal_logic_formulat();

  /* TODO can we make return value generic? */
  virtual void accept(causal_logic_formula_visitort& visitor) const = 0;

};

class TRUE_causal_logic_formulat : public causal_logic_formulat {
public:
  virtual ~TRUE_causal_logic_formulat();

  virtual void accept(causal_logic_formula_visitort& visitor);

};

class FALSE_causal_logic_formulat : public causal_logic_formulat {
public:
  virtual ~FALSE_causal_logic_formulat();

  virtual void accept(causal_logic_formula_visitort& visitor);

};

class NOT_causal_logic_formulat : public causal_logic_formulat {
public:
  NOT_causal_logic_formulat(const causal_logic_formulat& f);
  virtual ~NOT_causal_logic_formulat();

  virtual void accept(causal_logic_formula_visitort& visitor) const;

  virtual const causal_logic_formulat& get_subformula() const;

protected:
  const causal_logic_formulat& f;

};

class AND_causal_logic_formulat : public causal_logic_formulat {
public:
  AND_causal_logic_formulat(const causal_logic_formulat& f1, const causal_logic_formulat& f2);
  virtual ~AND_causal_logic_formulat();

  virtual void accept(causal_logic_formula_visitort& visitor) const;

  virtual const causal_logic_formulat& get_first_subformula() const;
  virtual const causal_logic_formulat& get_second_subformula() const;

protected:
  const causal_logic_formulat& f1;
  const causal_logic_formulat& f2;

};

// TODO should be a boolean primitive object either a variable or its negation?
class BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat : public causal_logic_formulat {
public:
  BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat(const boolean_variablet& variable, const boolean_constt& value);
  virtual ~BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat();

  virtual void accept(causal_logic_formula_visitort& visitor) const;

  virtual const boolean_variablet& get_variable() const;
  virtual const boolean_constt& get_value() const;

protected:
  const boolean_variablet& variable;
  const boolean_constt& value;

};

class INTEGER_PRIMITIVE_EVENT_causal_logic_formulat : public causal_logic_formulat {
public:
  INTEGER_PRIMITIVE_EVENT_causal_logic_formulat(const int_variablet& variable, const int_constt& value);
  virtual ~INTEGER_PRIMITIVE_EVENT_causal_logic_formulat();

  virtual void accept(causal_logic_formula_visitort& visitor) const;

  virtual const int_variablet& get_variable() const;
  virtual const int_constt& get_value() const;

protected:
  const int_variablet& variable;
  const int_constt& value;

};

class BOOLEAN_COUNTERFACTUAL_causal_logic_formulat : public causal_logic_formulat {
public:
  BOOLEAN_COUNTERFACTUAL_causal_logic_formulat(const boolean_variablet& variable, const boolean_constt& value, const causal_logic_formulat& subformula);
  virtual ~BOOLEAN_COUNTERFACTUAL_causal_logic_formulat();

  virtual void accept(causal_logic_formula_visitort& visitor) const;

  virtual const boolean_variablet& get_variable() const;
  virtual const boolean_constt& get_value() const;
  virtual const causal_logic_formulat& get_subformula() const;

protected:
  const boolean_variablet& variable;
  const boolean_constt& value;
  const causal_logic_formulat& subformula;

};

class INTEGER_COUNTERFACTUAL_causal_logic_formulat : public causal_logic_formulat {
public:
  INTEGER_COUNTERFACTUAL_causal_logic_formulat(const int_variablet& variable, const int_constt& value, const causal_logic_formulat& subformula);
  virtual ~INTEGER_COUNTERFACTUAL_causal_logic_formulat();

  virtual void accept(causal_logic_formula_visitort& visitor) const;

  virtual const int_variablet& get_variable() const;
  virtual const int_constt& get_value() const;
  virtual const causal_logic_formulat& get_subformula() const;

protected:
  const int_variablet& variable;
  const int_constt& value;
  const causal_logic_formulat& subformula;

};

class causal_logic_formula_visitort {
public:
  virtual ~causal_logic_formula_visitort() {};

  virtual void visit(const TRUE_causal_logic_formulat& True) = 0;
  virtual void visit(const FALSE_causal_logic_formulat& False) = 0;
  virtual void visit(const NOT_causal_logic_formulat& Not) = 0;
  virtual void visit(const AND_causal_logic_formulat& And) = 0;
  virtual void visit(const BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat& primitive_event) = 0;
  virtual void visit(const INTEGER_PRIMITIVE_EVENT_causal_logic_formulat& primitive_event) = 0;
  virtual void visit(const BOOLEAN_COUNTERFACTUAL_causal_logic_formulat& counterfactual) = 0;
  virtual void visit(const INTEGER_COUNTERFACTUAL_causal_logic_formulat& counterfactual) = 0;

};

class context_visitort;

class contextt {
public:
  virtual ~contextt();

  virtual void accept(context_visitort& visitor) const = 0;

};


// TODO create static instance
class empty_contextt : public contextt {
public:
  virtual ~empty_contextt();

  virtual void accept(context_visitort& visitor) const;

};

class boolean_contextt : public contextt {
public:
  boolean_contextt(const boolean_variablet& variable, const boolean_constt& value, const contextt& subcontext);
  virtual ~boolean_contextt();

  virtual void accept(context_visitort& visitor) const;

  virtual const boolean_variablet& get_variable() const;
  virtual const boolean_constt& get_value() const;
  virtual const contextt& get_subcontext() const;

protected:
  const boolean_variablet& variable;
  const boolean_constt& value;
  const contextt& subcontext;

};

class int_contextt : public contextt {
public:
  int_contextt(const int_variablet& variable, const int_constt& value, const contextt& subcontext);
  virtual ~int_contextt();

  virtual void accept(context_visitort& visitor) const;

  virtual const int_variablet& get_variable() const;
  virtual const int_constt& get_value() const;
  virtual const contextt& get_subcontext() const;

protected:
  const int_variablet& variable;
  const int_constt& value;
  const contextt& subcontext;

};

class context_visitort {
public:
  virtual ~context_visitort();

  virtual void visit(const empty_contextt& context) = 0;
  virtual void visit(const boolean_contextt& context) = 0;
  virtual void visit(const int_contextt& context) = 0;

};

class causal_logic_solvert {
public:
  virtual ~causal_logic_solvert();

  virtual void compute_actual_causes(const causal_modelt& model, const contextt& context, const causal_logic_formulat& explanandum);
  virtual bool solve(const causal_modelt& model, const contextt& context, const causal_logic_formulat& formula, contextt*& ctxt);
  //contextt existsContext(const causal_modelt& model, const contextt& partial_context, const causal_logic_formulat& formula);

protected:

  virtual void translate_to_C_program(const causal_modelt& model, const contextt& context, const causal_logic_formulat& formula, ::std::ostream& out);

};

}

#endif // CAUSALITY_HPP

