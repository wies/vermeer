#ifndef CAUSALITY_HPP
#define CAUSALITY_HPP

#include <string>

namespace causality {

class int_termt {
};

class boolean_termt {
};

class int_variablet : public int_termt {
public:
  int_variablet(::std::string var_name) : var_name(var_name) {}
  virtual ~int_variablet() {}

protected:
  ::std::string var_name;
};

class boolean_variablet : public boolean_termt {
public:
  boolean_variablet(::std::string var_name) : var_name(var_name) {}
  virtual ~boolean_variablet() {}

protected:
  ::std::string var_name;
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

}

#endif // CAUSALITY_HPP

