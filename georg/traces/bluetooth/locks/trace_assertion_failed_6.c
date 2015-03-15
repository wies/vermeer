#ifdef COMPILE_FOR_TEST
#include <assert.h>
#define assume(cond) assert(cond)
#endif

void main(int argc, char* argv[]) {
int x_0_0;//stoppingEvent 
int x_0_1;//stoppingEvent 
int x_1_0;//stopped 
int x_1_1;//stopped 
int x_2_0;//stoppingFlag 
int x_2_1;//stoppingFlag 
int x_3_0;//pendingIO 
int x_3_1;//pendingIO 
int x_3_2;//pendingIO 
int x_4_0;//status1 
int x_4_1;//status1 
int x_5_0;//status2 
int x_6_0;//input1 T0
int x_6_1;//input1 T0
int x_7_0;//input2 T0
int x_7_1;//input2 T0
int x_8_0;//in T1
int x_8_1;//in T1
int x_9_0;//in T2
int x_9_1;//in T2

T_0_0_0: x_6_0 = 0;
T_0_1_0: x_6_1 = 1;
T_0_2_0: x_7_0 = 0;
T_0_3_0: x_7_1 = 0;
T_0_4_0: x_0_0 = 0;
T_0_5_0: x_1_0 = 0;
T_0_6_0: x_2_0 = 0;
T_0_7_0: x_3_0 = 1;
T_0_8_0: x_4_0 = 0;
T_0_9_0: x_5_0 = 0;
T_1_10_1: x_8_0 = 0;
T_1_11_1: x_8_1 = x_6_1;
T_2_12_2: x_9_0 = 0;
T_2_13_2: x_9_1 = x_7_1;
T_2_14_2: if (x_9_1 != 1)  x_2_1 = 1;
T_2_15_2: if (x_9_1 != 1)  x_3_1 = -1 + x_3_0;
T_1_16_1: if (x_8_1 == 1 && x_2_0 != 1)  x_3_2 = 1 + x_3_0;
T_2_17_2: if (x_9_1 != 1 && x_3_1 == 0)  x_0_1 = 1;
T_2_18_2: if (x_9_1 != 1)  x_1_1 = 1;
T_1_19_1: if (x_8_1 == 1 && x_2_0 != 1)  x_4_1 = 0;
T_1_20_1: if (x_8_1 == 1 && x_4_1 == 0)  assert(x_1_1 != 1);
}
