#ifdef COMPILE_FOR_TEST
#include <assert.h>
#define assume(cond) assert(cond)
#endif

void main(int argc, char* argv[]) {
int x_0_0;//global::lock_a 
int x_0_1;//global::lock_a 
int x_0_2;//global::lock_a 
int x_1_0;//global::lock_b 
int x_1_1;//global::lock_b 
int x_1_2;//global::lock_b 
int x_2_0;//global::lock_a_w 
int x_2_1;//global::lock_a_w 
int x_2_2;//global::lock_a_w 
int x_2_3;//global::lock_a_w 
int x_3_0;//global::lock_b_w 
int x_3_1;//global::lock_b_w 
int x_3_2;//global::lock_b_w 
int x_3_3;//global::lock_b_w 
int x_4_0;//global::t1_id 
int x_4_1;//global::t1_id 
int x_4_2;//global::t1_id 
int x_5_0;//global::t2_id 
int x_5_1;//global::t2_id 
int x_5_2;//global::t2_id 

T_0_0_0: x_0_0 = 0;
T_0_1_0: x_1_0 = 0;
T_0_2_0: x_2_0 = 0;
T_0_3_0: x_3_0 = 0;
T_0_4_0: x_4_0 = 0;
T_0_5_0: x_5_0 = 0;
T_0_6_0: x_3_1 = -1;
T_0_7_0: x_2_1 = x_3_1;
T_0_8_0: x_1_1 = x_2_1;
T_0_9_0: x_0_1 = x_1_1;
T_0_10_0: x_5_1 = -2;
T_0_11_0: x_4_1 = x_5_1;
T_1_12_1: x_4_2 = 1;
T_2_13_2: x_5_2 = 2;
T_2_14_2: if (x_1_1 + 1 == 0)  x_1_2 = x_5_2;
T_2_15_2: if (x_1_1 + 1 == 0)  x_3_2 = -1;
T_1_16_1: if (x_0_1 + 1 == 0)  x_0_2 = x_4_2;
T_1_17_1: if (x_0_1 + 1 == 0)  x_2_2 = -1;
T_2_18_2: if (x_0_2 + 1 != 0)  x_2_3 = x_5_2;
T_1_19_1: if (x_1_2 + 1 != 0)  x_3_3 = x_4_2;
T_1_20_1: if (x_1_2 + 1 != 0)  assert(x_2_3 != x_5_2);
}
