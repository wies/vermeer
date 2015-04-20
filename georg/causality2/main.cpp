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
  ::causality::int_variablet i0("i0");
  ::causality::int_variablet i1("i1");

  // endogenous variables
  ::causality::int_variablet x0("x0");
  ::causality::int_variablet y0("y0");
  ::causality::int_variablet z0("z0");
  ::causality::int_variablet z1("z1");
  ::causality::int_variablet z2("z2");
  ::causality::int_variablet z3("z3");
  ::causality::int_variablet z4("z4");
  ::causality::int_variablet z5("z5");
  ::causality::int_variablet z6("z6");
  ::causality::int_variablet z7("z7");
  ::causality::int_variablet z8("z8");
  ::causality::int_variablet l0("l0");
  ::causality::int_variablet l1("l1");
  ::causality::int_variablet l2("l2");
  ::causality::int_variablet l3("l3");
  ::causality::int_variablet l4("l4");
  ::causality::boolean_variablet c0("c0");
  ::causality::boolean_variablet c0p("c0p");
  ::causality::boolean_variablet c1("c1");
  ::causality::boolean_variablet c1p("c1p");
  ::causality::boolean_variablet c2("c2");
  ::causality::boolean_variablet c3("c3");

//  ::causality::relationt< ::causality::boolean_termt > r(::causality::EQ, c0, c1);
//  ::causality::itet< ::causality::int_termt > ite0(r, x0, y0);
}


