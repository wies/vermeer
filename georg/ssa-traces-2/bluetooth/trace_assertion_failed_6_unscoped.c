main() {
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
int x_7_0;//input2 T0
int x_8_0;//in T1
int x_8_1;//in T1
int x_9_0;//in T2
int x_9_1;//in T2

T0_0: x_6_0 = 1;
T0_1: x_7_0 = 0;
T0_2: x_0_0 = 0;
T0_3: x_1_0 = 0;
T0_4: x_2_0 = 0;
T0_5: x_3_0 = 1;
T0_6: x_4_0 = 0;
T0_7: x_5_0 = 0;
T1_8: x_8_0 = 0;
T1_9: x_8_1 = x_6_0;
T1_10: assume(-1 + x_8_1 == 0);
T2_11: x_9_0 = 0;
T2_12: x_9_1 = x_7_0;
T2_13: assume(-1 + x_9_1 != 0);
T2_14: x_2_1 = 1;
T1_15: assume(-1 + x_2_0 != 0);
T2_16: x_3_1 = -1 + x_3_0;
T1_17: x_3_2 = 1 + x_3_0;
T2_18: assume(0 + x_3_1 == 0);
T2_19: x_0_1 = 1;
T2_20: x_1_1 = 1;
T1_21: x_4_1 = 0;
T1_22: assume(0 + x_4_1 == 0);
T1_23: assert(-1 + x_1_1 != 0);
}
