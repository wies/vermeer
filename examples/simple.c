#include <stdio.h>
#include <math.h>

int main(int argc, char** argv)
{
  int a = 100;
  int b = 2;
  while(a > 0){
    a = abs(-1 * (a-1));
    b++;
  }
					       
  dsn_assert(b < 4);
  return 0;
}
