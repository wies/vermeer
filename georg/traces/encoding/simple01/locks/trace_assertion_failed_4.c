#ifdef COMPILE_FOR_TEST
#include <assert.h>
#define assume(cond) assert(cond)
#endif

void main(int argc, char* argv[]) {
int x_0_0;//x 
int x_0_1;//x 

T_0_0_0: x_0_0 = 0;
T_2_1_2: x_0_1 = 2;
T_3_2_3: assert(x_0_1 == 0);
}
