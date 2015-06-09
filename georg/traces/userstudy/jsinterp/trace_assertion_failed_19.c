#ifdef COMPILE_FOR_TEST
#include <assert.h>
#define assume(cond) assert(cond)
#endif

void main(int argc, char* argv[]) {
int x_0_0;//CREST_scheduler::lock_0 
int x_0_1;//CREST_scheduler::lock_0 
int x_0_2;//CREST_scheduler::lock_0 
int x_0_3;//CREST_scheduler::lock_0 
int x_0_4;//CREST_scheduler::lock_0 
int x_0_5;//CREST_scheduler::lock_0 
int x_0_6;//CREST_scheduler::lock_0 
int x_0_7;//CREST_scheduler::lock_0 
int x_0_8;//CREST_scheduler::lock_0 
int x_0_9;//CREST_scheduler::lock_0 
int x_0_10;//CREST_scheduler::lock_0 
int x_0_11;//CREST_scheduler::lock_0 
int x_1_0;//cache_global.table[0] 
int x_1_1;//cache_global.table[0] 
int x_1_2;//cache_global.table[0] 
int x_1_3;//cache_global.table[0] 
int x_2_0;//cache_global.table[1] 
int x_2_1;//cache_global.table[1] 
int x_2_2;//cache_global.table[1] 
int x_2_3;//cache_global.table[1] 
int x_3_0;//cache_global.table[2] 
int x_3_1;//cache_global.table[2] 
int x_3_2;//cache_global.table[2] 
int x_4_0;//cache_global.table[3] 
int x_4_1;//cache_global.table[3] 
int x_4_2;//cache_global.table[3] 
int x_5_0;//cache_global.empty 
int x_5_1;//cache_global.empty 
int x_5_2;//cache_global.empty 
int x_5_3;//cache_global.empty 
int x_6_0;//cache_global.fills 
int x_6_1;//cache_global.fills 
int x_6_2;//cache_global.fills 
int x_7_0;//cache_global.recycles 
int x_7_1;//cache_global.recycles 
int x_8_0;//cache_global.tests 
int x_8_1;//cache_global.tests 
int x_9_0;//cache_global.misses 
int x_9_1;//cache_global.misses 
int x_10_0;//cache_global.flushes 
int x_10_1;//cache_global.flushes 
int x_10_2;//cache_global.flushes 
int x_11_0;//functioncall::param T1
int x_11_1;//functioncall::param T1
int x_11_2;//functioncall::param T1
int x_12_0;//js_PropertyCacheFill::found T1
int x_12_1;//js_PropertyCacheFill::found T1
int x_12_2;//js_PropertyCacheFill::found T1
int x_12_3;//js_PropertyCacheFill::found T1
int x_12_4;//js_PropertyCacheFill::found T1
int x_13_0;//js_PropertyCacheFill::found T1
int x_13_1;//js_PropertyCacheFill::found T1
int x_13_2;//js_PropertyCacheFill::found T1
int x_13_3;//js_PropertyCacheFill::found T1
int x_13_4;//js_PropertyCacheFill::found T1

T_0_0_0: x_0_0 = -1;
T_0_1_0: x_1_0 = 0;
T_0_2_0: x_1_1 = 0;
T_0_3_0: x_2_0 = 0;
T_0_4_0: x_2_1 = 0;
T_0_5_0: x_3_0 = 0;
T_0_6_0: x_3_1 = 0;
T_0_7_0: x_4_0 = 0;
T_0_8_0: x_4_1 = 0;
T_0_9_0: x_5_0 = 0;
T_0_10_0: x_6_0 = 0;
T_0_11_0: x_7_0 = 0;
T_0_12_0: x_8_0 = 0;
T_0_13_0: x_9_0 = 0;
T_0_14_0: x_10_0 = 0;
T_0_15_0: x_5_1 = 1;
T_0_16_0: x_6_1 = 0;
T_0_17_0: x_7_1 = 0;
T_0_18_0: x_8_1 = 0;
T_0_19_0: x_9_1 = 0;
T_0_20_0: x_10_1 = 0;
T_2_21_2: if (0 == x_0_0 + 1)  x_0_1 = 2;
T_2_22_2: if (2 == x_0_1)  x_0_2 = -1;
T_1_23_1: x_11_0 = 512942321;
T_1_24_1: x_11_1 = 0;
T_1_25_1: if (0 == x_0_2 + 1)  x_0_3 = 1;
T_1_26_1: if (x_11_1 == 0 && 1 == x_0_3)  x_1_2 = 1;
T_1_27_1: if (1 == x_0_3)  x_0_4 = -1;
T_1_28_1: if (0 == x_0_4 + 1)  x_0_5 = 1;
T_1_29_1: if (1 == x_0_5)  x_12_0 = 11029;
T_1_30_1: if (1 == x_0_5)  x_12_1 = x_1_2;
T_1_31_1: if (1 == x_0_5)  x_12_2 = x_2_1 + x_12_1;
T_1_32_1: if (1 == x_0_5)  x_12_3 = x_3_1 + x_12_2;
T_1_33_1: if (1 == x_0_5)  x_12_4 = x_4_1 + x_12_3;
T_1_34_1: if (1 == x_0_5)  assert(x_12_4 != 0);
T_1_35_1: if (1 == x_0_5)  x_5_2 = 0;
T_1_36_1: if (1 == x_0_5)  x_0_6 = -1;
T_1_37_1: x_6_2 = 1 + x_6_1;
T_1_38_1: x_11_2 = 1;
T_1_39_1: if (0 == x_0_6 + 1)  x_0_7 = 1;
T_1_40_1: if (x_11_2 != 0 && x_11_2 == 1 && 1 == x_0_7)  x_2_2 = 1;
T_1_41_1: if (1 == x_0_7)  x_0_8 = -1;
T_2_42_2: if (0 == x_0_8 + 1)  x_0_9 = 2;
T_2_43_2: if (x_5_2 == 0 && 2 == x_0_9)  x_1_3 = 0;
T_2_44_2: if (x_5_2 == 0 && 2 == x_0_9)  x_2_3 = 0;
T_2_45_2: if (x_5_2 == 0 && 2 == x_0_9)  x_3_2 = 0;
T_2_46_2: if (x_5_2 == 0 && 2 == x_0_9)  x_4_2 = 0;
T_2_47_2: if (x_5_2 == 0 && 2 == x_0_9)  x_5_3 = 1;
T_2_48_2: if (x_5_2 == 0 && 2 == x_0_9)  x_10_2 = 1 + x_10_1;
T_2_49_2: if (2 == x_0_9)  x_0_10 = -1;
T_1_50_1: if (0 == x_0_10 + 1)  x_0_11 = 1;
T_1_51_1: if (1 == x_0_11)  x_13_0 = 0;
T_1_52_1: if (1 == x_0_11)  x_13_1 = x_1_3;
T_1_53_1: if (1 == x_0_11)  x_13_2 = x_2_3 + x_13_1;
T_1_54_1: if (1 == x_0_11)  x_13_3 = x_3_2 + x_13_2;
T_1_55_1: if (1 == x_0_11)  x_13_4 = x_4_2 + x_13_3;
T_1_56_1: if (1 == x_0_11)  assert(x_13_4 != 0);
}
