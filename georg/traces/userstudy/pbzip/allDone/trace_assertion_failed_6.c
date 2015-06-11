#ifdef COMPILE_FOR_TEST
#include <assert.h>
#define assume(cond) assert(cond)
#endif

void main(int argc, char* argv[]) {
int x_0_0;//output_done 
int x_0_1;//output_done 
int x_0_2;//output_done 
int x_1_0;//fifo.empty 
int x_1_1;//fifo.empty 
int x_1_2;//fifo.empty 
int x_1_3;//fifo.empty 
int x_2_0;//fifo.ready 
int x_2_1;//fifo.ready 
int x_2_2;//fifo.ready 
int x_3_0;//fifo.full 
int x_3_1;//fifo.full 
int x_3_2;//fifo.full 
int x_3_3;//fifo.full 
int x_4_0;//fifo.isFreed 
int x_4_1;//fifo.isFreed 
int x_4_2;//fifo.isFreed 
int x_5_0;//CREST_scheduler::lock_0 
int x_5_1;//CREST_scheduler::lock_0 
int x_5_2;//CREST_scheduler::lock_0 
int x_5_3;//CREST_scheduler::lock_0 
int x_5_4;//CREST_scheduler::lock_0 
int x_5_5;//CREST_scheduler::lock_0 
int x_5_6;//CREST_scheduler::lock_0 
int x_6_0;//allDone 
int x_6_1;//allDone 
int x_7_0;//consumer::i T1
int x_7_1;//consumer::i T1
int x_7_2;//consumer::i T1
int x_8_0;//consumer::cond T1
int x_8_1;//consumer::cond T1
int x_9_0;//output::ready T2
int x_9_1;//output::ready T2

T_0_0_0: x_0_0 = 0;
T_0_1_0: x_0_1 = 0;
T_0_2_0: x_1_0 = 0;
T_0_3_0: x_2_0 = 0;
T_0_4_0: x_3_0 = 0;
T_0_5_0: x_4_0 = 0;
T_0_6_0: x_1_1 = 1;
T_0_7_0: x_2_1 = 0;
T_0_8_0: x_3_1 = 0;
T_0_9_0: x_4_1 = 0;
T_0_10_0: x_5_0 = -1;
T_0_11_0: x_6_0 = 0;
T_0_12_0: if (0 == x_5_0 + 1)  x_5_1 = 0;
T_0_13_0: if (x_1_1 != 0 && 0 == x_5_1)  x_3_2 = 1;
T_0_14_0: if (x_1_1 != 0 && 0 == x_5_1)  x_1_2 = 0;
T_0_15_0: if (0 == x_5_1)  x_5_2 = -1;
T_1_16_1: x_7_0 = 0;
T_1_17_1: x_7_1 = 0;
T_1_18_1: if (x_7_1 < 3)  assert(x_4_1 == 0);
T_1_19_1: if (x_7_1 < 3 && 0 == x_5_2 + 1)  x_5_3 = 1;
T_1_20_1: if (x_7_1 < 3 && 1 == x_5_3)  x_8_0 = 270624512;
T_1_21_1: if (x_7_1 < 3 && 1 == x_5_3)  x_8_1 = x_1_2 + x_6_0;
T_1_22_1: if (x_7_1 < 3 && x_8_1 != 2 && x_3_2 != 0 && 1 == x_5_3)  x_1_3 = 1;
T_1_23_1: if (x_7_1 < 3 && x_8_1 != 2 && x_3_2 != 0 && 1 == x_5_3)  x_3_3 = 0;
T_1_24_1: if (x_7_1 < 3 && x_8_1 != 2 && x_3_2 != 0 && 1 == x_5_3)  x_2_2 = 1;
T_1_25_1: if (x_7_1 < 3 && 1 == x_5_3)  x_5_4 = -1;
T_2_26_2: if (0 == x_5_4 + 1)  x_5_5 = 2;
T_2_27_2: if (2 == x_5_5)  x_9_0 = 0;
T_2_28_2: if (2 == x_5_5)  x_9_1 = x_2_2;
T_2_29_2: if (x_9_1 != 0 && 2 == x_5_5)  x_6_1 = 1;
T_2_30_2: if (2 == x_5_5)  x_5_6 = -1;
T_2_31_2: x_0_2 = x_6_1;
T_0_32_0: if (x_0_2 != 0)  x_4_2 = 1;
T_1_33_1: x_7_2 = 1 + x_7_1;
T_1_34_1: if (x_7_2 < 3)  assert(x_4_2 == 0);
}
