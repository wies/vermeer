#ifndef EXPR_H_INCLUDED
#define EXPR_H_INCLUDED

namespace expr {

template <class VariableType>
struct linear_product_t {
  int factor;
  VariableType variable;
};

template <class VariableType>
struct term_t {
  std::vector<linear_product_t<VariableType>> products;
  int constant;
};

template <class VariableType>
struct expr_t {
  enum ops {
    EQ, NEQ, LT, LEQ, GT, GEQ
  } op;

  term_t<VariableType> term;
};

}

#endif // EXPR_H_INCLUDED
