#ifndef EXPR_H_INCLUDED
#define EXPR_H_INCLUDED

#include <map>

namespace expr {

template <class VariableType>
struct linear_product_t {
  int factor;
  VariableType variable;

  friend std::ostream& operator<<(std::ostream& out, linear_product_t<VariableType> p) {
    out << p.factor << "*" << p.variable;

    return out;
  }

  template <class VisitorType, class ReturnType>
  ReturnType accept(VisitorType& v) {
    return v.visit_linear_product(*this);
  }

  template <class VisitorType>
  void accept(VisitorType& v) {
    v.visit_linear_product(*this);
  }

};

template <class VariableType>
struct term_t {
  std::vector<linear_product_t<VariableType>> products;
  int constant;

  friend std::ostream& operator<<(std::ostream& out, term_t<VariableType> t) {
    out << t.constant;

    for (auto& p : t.products) {
      out << " + " << p;
    }

    return out;
  }

  template <class VisitorType, class ReturnType = void>
  ReturnType accept(VisitorType& v) {
    return v.visit_term(*this);
  }

};

template <class VariableType>
struct expr_t {
  enum ops {
    EQ, NEQ, LT, LEQ, GT, GEQ
  } op;

  term_t<VariableType> term;

  friend std::ostream& operator<<(std::ostream& out, expr_t<VariableType> e) {
    out << 0;

    switch (e.op) {
      case EQ:
        out << " = ";
        break;
      case NEQ:
        out << " != ";
        break;
      case LT:
        out << " < ";
        break;
      case LEQ:
        out << " <= ";
        break;
      case GT:
        out << " > ";
        break;
      case GEQ:
        out << " >= ";
        break;
    }

    out << e.term;

    return out;
  }

  template <class VisitorType, class ReturnType = void>
  ReturnType accept(VisitorType& v) {
    return v.visit_expr(*this);
  }

};

template <class VariableType1, class VariableType2>
struct variable_substitution_t {

  std::map<VariableType1, VariableType2> substitution_map;

  expr_t<VariableType2> visit_expr(expr_t<VariableType1>& e) {
    expr_t<VariableType2> e_new;

    e_new.op = e.op;
    //e_new.term = e.term.accept(*this);
    e_new.term.constant = e.term.constant;
    for (auto& p : e.term.products) {
      e_new.term.products.push_back(visit_linear_product(p));
    }

    return e_new;
  }

  term_t<VariableType2> visit_term(term_t<VariableType1>& t) {
    term_t<VariableType2> t_new;

    t_new.constant = t.constant;

    for (auto& p : t.products) {
      t_new.products.push_back(visit_linear_product(p));
    }

    return t_new;
  }

  linear_product_t<VariableType2> visit_linear_product(linear_product_t<VariableType1> p) {
    auto it = substitution_map.find(p.variable);

    if (it == substitution_map.end()) {
      ERROR("Unmatched variable!");
    }

    // perform replacement
    linear_product_t<VariableType2> p_new;
    p_new.factor = p.factor;
    p_new.variable = it->second;

    return p_new;
  }

};

}

#endif // EXPR_H_INCLUDED
