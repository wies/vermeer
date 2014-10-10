#include <stdio.h>
#include <math.h>
#include <stdlib.h>

#include "extern_debug_funs.h"

int main(int argc, char** argv){
  int x = 3;
  int y = 2;
  double r = pow(x,y);
  char buf[90];
  printf("Result \t is %f\n", r);
  pow(x,r);

  struct MY_RET z = some_extern_fun();
  int *p = return_a_pointer();
  no_return();
  sprintf(buf, "pow(x,y) = %f", r);
  printf(buf);

  return 0;
}
