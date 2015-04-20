#ifndef CAUSALITY_HPP
#define CAUSALITY_HPP

#include <string>

namespace causality {

class int_termt {
};

class boolean_termt {
};

class variablet {
public:
  variablet(::std::string var_name) : var_name(var_name) {}
  virtual ~variablet() {}

protected:
  ::std::string var_name;
};

class int_variablet : public int_termt, public variablet {
public:
  int_variablet(::std::string var_name) : variablet(var_name) {}
  virtual ~int_variablet() {}
};

class boolean_variablet : public boolean_termt, public variablet {
public:
  boolean_variablet(::std::string var_name) : variablet(var_name) {}
  virtual ~boolean_variablet() {}
};

class boolean_andt : public boolean_termt {
public:
  boolean_andt(boolean_termt& t1, boolean_termt& t2) : t1(t1), t2(t2) {}
  virtual ~boolean_andt() {}

protected:
  boolean_termt& t1;
  boolean_termt& t2;
};

class boolean_nott : public boolean_termt {
public:
  boolean_nott(boolean_termt& t) : t(t) {}
  virtual ~boolean_nott() {}

protected:
  boolean_termt& t;
};

class boolean_constt : public boolean_termt {
public:
  boolean_constt(bool value) : value(value) {}
  virtual ~boolean_constt() {}

protected:
  bool value;
};

class int_constt : public int_termt {
public:
  int_constt(int value) : value(value) {}
  virtual ~int_constt() {}

protected:
  int value;
};

enum relational_operatort {
  EQ, NEQ, GT, LT
};

template< class T >
class relationt : public T {
public:
  relationt(relational_operatort op, T& t1, T& t2) : t1(t1), t2(t2) {}
  virtual ~relationt() {}

protected:
  relational_operatort op;
  T& t1;
  T& t2;
};

template< class T >
class itet : public T {
public:
  itet(boolean_termt& condition, T& then_term, T& else_term) : condition(condition), then_term(then_term), else_term(else_term) {}
  virtual ~itet() {}

protected:
  boolean_termt& condition;
  T& then_term;
  T& else_term;
};

class functiont {
public:
  virtual ~functiont() {}

};

template< class T >
class function_termt : public functiont {
public:
  function_termt(T& t) : t(t) {}
  virtual ~function_termt() {}

protected:
  T& t;
};

class causal_modelt {
public:
  virtual ~causal_modelt() {}
};

// context???

// TODO do we need that?
/*
class situationt {
public:
  virtual ~situationt() {}
};
*/

// TODO create namespace causal_logic

class causal_logic_formula_visitort;

class causal_logic_formulat {
public:
  virtual ~causal_logic_formulat();

  /* TODO can we make return value generic? */
  virtual void accept(causal_logic_formula_visitort& visitor) = 0;

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

class COUNTERFACTUAL_causal_logic_formulat : public causal_logic_formulat {
public:
  COUNTERFACTUAL_causal_logic_formulat();
  virtual ~COUNTERFACTUAL_causal_logic_formulat();

  // TODO finish
};

class causal_logic_formula_visitort {
public:
  virtual ~causal_logic_formula_visitort();

  virtual void visit(const TRUE_causal_logic_formulat& True) = 0;
  virtual void visit(const FALSE_causal_logic_formulat& False) = 0;
  virtual void visit(const NOT_causal_logic_formulat& Not) = 0;
  virtual void visit(const AND_causal_logic_formulat& And) = 0;
  virtual void visit(const BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat& primitive_event) = 0;
  virtual void visit(const INTEGER_PRIMITIVE_EVENT_causal_logic_formulat& primitive_event) = 0;

};

/*
class causal_logic_solvert {
public:
  virtual ~causal_logic_solvert();

  void solve(causal_modelt& model, contextt& context, causal_logic_formulat& formula);

};
*/

}

#endif // CAUSALITY_HPP

