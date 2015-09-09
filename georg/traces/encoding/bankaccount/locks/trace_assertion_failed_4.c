#ifdef COMPILE_FOR_TEST
#include <assert.h>
#define assume(cond) assert(cond)
#endif

void main(int argc, char* argv[]) {
int x_0_0;//global::bal 
int x_0_1;//global::bal 
int x_0_2;//global::bal 
int x_0_3;//global::bal 
int x_0_4;//global::bal 
int x_1_0;//global::thread1_ended 
int x_1_1;//global::thread1_ended 
int x_1_2;//global::thread1_ended 
int x_2_0;//global::thread2_ended 
int x_2_1;//global::thread2_ended 
int x_2_2;//global::thread2_ended 
int x_3_0;//thread1::b T1
int x_3_1;//thread1::b T1
int x_3_2;//thread1::b T1
int x_3_3;//thread1::b T1
int x_3_4;//thread1::b T1
int x_4_0;//thread2::c T2
int x_4_1;//thread2::c T2
int x_4_2;//thread2::c T2

T_0_0_0: x_0_0 = 0;
T_0_1_0: x_1_0 = 0;
T_0_2_0: x_2_0 = 0;
T_0_3_0: x_0_1 = 50;
T_0_4_0: x_1_1 = 0;
T_0_5_0: x_2_1 = 0;
T_1_6_1: x_3_0 = 11021;
T_2_7_2: x_4_0 = 0;
T_1_8_1: x_3_1 = x_0_1;
T_1_9_1: x_3_2 = 10 + x_3_1;
T_1_10_1: x_0_2 = x_3_2;
T_1_11_1: x_3_3 = x_0_2;
T_1_12_1: x_3_4 = 5 + x_3_3;
T_1_13_1: x_0_3 = x_3_4;
T_2_14_2: x_4_1 = x_0_1;
T_2_15_2: x_4_2 = -5 + x_4_1;
T_2_16_2: x_0_4 = x_4_2;
T_1_17_1: x_1_2 = 1;
T_2_18_2: x_2_2 = 1;
T_0_19_0: if (x_1_2 != 0 && x_2_2 != 0)  assert(x_0_4 == 60);
}
