//#include "cbmc.h"

#include "causality.hpp"

#include <cstdlib>
#include <cstring>
#include <libgen.h>

#include <iostream>
#include <sstream>
#include <fstream>

int main(int argc, char* argv[]) {
  //incremental_cbmct inc_cbmc("/home/andi/mpc-synthesis/cbmc-4.9-src/cbmc-4.9-incremental/src/cbmc/cbmc", 21);
  //incremental_cbmct minisat2_cbmc("/home/andi/mpc-synthesis/cbmc-4.9-src/cbmc-4.9-incremental/src/cbmc/cbmc", 20);

  // exogenous variables
  ::std::set< ::causality::variablet* > exogenous_variables;
  ::causality::int_variablet i0("i0");
  exogenous_variables.insert(&i0);
  ::causality::int_variablet i1("i1");
  exogenous_variables.insert(&i1);

  // endogenous variables
  ::std::set< ::causality::variablet* > endogenous_variables;
  ::causality::int_variablet x0("x0");
  endogenous_variables.insert(&x0);
  ::causality::int_variablet y0("y0");
  endogenous_variables.insert(&y0);
  ::causality::int_variablet z0("z0");
  endogenous_variables.insert(&z0);
  ::causality::int_variablet z1("z1");
  endogenous_variables.insert(&z1);
  ::causality::int_variablet z2("z2");
  endogenous_variables.insert(&z2);
  ::causality::int_variablet z3("z3");
  endogenous_variables.insert(&z3);
  ::causality::int_variablet z4("z4");
  endogenous_variables.insert(&z4);
  ::causality::int_variablet z5("z5");
  endogenous_variables.insert(&z5);
  ::causality::int_variablet z6("z6");
  endogenous_variables.insert(&z6);
  ::causality::int_variablet z7("z7");
  endogenous_variables.insert(&z7);
  ::causality::int_variablet z8("z8");
  endogenous_variables.insert(&z8);
  ::causality::int_variablet l0("l0");
  endogenous_variables.insert(&l0);
  ::causality::int_variablet l1("l1");
  endogenous_variables.insert(&l1);
  ::causality::int_variablet l2("l2");
  endogenous_variables.insert(&l2);
  ::causality::int_variablet l3("l3");
  endogenous_variables.insert(&l3);
  ::causality::int_variablet l4("l4");
  endogenous_variables.insert(&l4);
  ::causality::boolean_variablet c0("c0");
  endogenous_variables.insert(&c0);
  ::causality::boolean_variablet c0p("c0p");
  endogenous_variables.insert(&c0p);
  ::causality::boolean_variablet c1("c1");
  endogenous_variables.insert(&c1);
  ::causality::boolean_variablet c1p("c1p");
  endogenous_variables.insert(&c1p);
  ::causality::boolean_variablet c2("c2");
  endogenous_variables.insert(&c2);
  ::causality::boolean_variablet c3("c3");
  endogenous_variables.insert(&c3);
  
  ::causality::int_constt zero(0);
  ::causality::int_constt one(1);
  ::causality::int_constt two(2);
  ::causality::int_constt three(3);

  ::causality::empty_equationt empty_equation; // TODO make static

  ::causality::relationt r_F_c3(::causality::EQ, l4, zero);
  ::causality::boolean_equationt F_c3(c3, r_F_c3, empty_equation);
  ::causality::boolean_nott not_c0p(c0p);

  ::causality::itet ite_F_l4(not_c0p, l3, l1);
  ::causality::int_equationt F_l4(l4, ite_F_l4, F_c3);

  ::causality::itet ite_F_l3(c2, l2, l0);
  ::causality::int_equationt F_l3(l3, ite_F_l3, F_l4);

  ::causality::itet ite_F_z8(c0p, z7, z5);
  ::causality::int_equationt F_z8(z8, ite_F_z8, F_l3);

  ::causality::itet ite_F_z7(c2, z6, z4);
  ::causality::int_equationt F_z7(z7, ite_F_z7, F_z8);

  ::causality::relationt r_F_c2(::causality::GT, z4, one /*zero*/ /* modification to omit -1 as a value */);
  ::causality::boolean_equationt F_c2(c2, r_F_c2, F_z7);

  ::causality::itet ite_F_z4(c1p, z3, z2);
  ::causality::int_equationt F_z4(z4, ite_F_z4, F_c2);

  ::causality::boolean_andt and_c0_c1(c0, c1);
  ::causality::itet ite_F_z2(and_c0_c1, z1, z0);
  ::causality::int_equationt F_z2(z2, ite_F_z2, F_z4);

  ::causality::relationt rel_c0(::causality::EQ, x0, zero);
  ::causality::boolean_equationt F_c0(c0, rel_c0, F_z2);

  ::causality::relationt rel_c0p(::causality::NEQ, x0, zero);
  ::causality::boolean_equationt F_c0p(c0p, rel_c0p, F_c0);

  ::causality::relationt rel_c1(::causality::EQ, y0, zero);
  ::causality::boolean_equationt F_c1(c1, rel_c1, F_c0p);

  ::causality::relationt rel_c1p(::causality::NEQ, y0, zero);
  ::causality::boolean_equationt F_c1p(c1p, rel_c1p, F_c1);

  ::causality::int_equationt F_z3(z3, y0, F_c1p);
  ::causality::int_equationt F_z0(z0, zero, F_z3);
  ::causality::int_equationt F_z1(z1, one, F_z0);
  ::causality::int_equationt F_z5(z5, two, F_z1);
  ::causality::int_equationt F_z6(z6, three, F_z5);
  ::causality::int_equationt F_l0(l0, one, F_z6);
  ::causality::int_equationt F_l1(l1, zero, F_l0);
  ::causality::int_equationt F_l2(l2, zero, F_l1);
  ::causality::int_equationt F_x0(x0, i0, F_l2);
  ::causality::int_equationt F_y0(y0, i1, F_x0);

  ::causality::causal_modelt model(exogenous_variables, endogenous_variables, F_y0);

  ::causality::causal_logic_solvert solver();

  // values for exogenous variables
  ::causality::int_contextt ctxt_i0(i0, zero, ::causality::empty_contextt());
  ::causality::int_contextt ctxt_i1(i1, one, ctxt_i0);

  // formula for which causes have to be determined
  //::causality::BOOLEAN_PRIMITIVE_EVENT_causal_logic_formulat formula(c3, ::causality::boolean_constt(false));

  //solver.solve(model, ctxt_i1, formula);
}


