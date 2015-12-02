#ifndef EXPR_H_INCLUDED
#define EXPR_H_INCLUDED

namespace expr {

template <class VariableType>
struct linear_product_t {
  int factor;
  VariableType variable;

  friend std::ostream& operator<<(std::ostream& out, linear_product_t<VariableType> p) {
    out << p.factor << "*" << p.variable;

    return out;
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
};



}

#endif // EXPR_H_INCLUDED
