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
int x_1_0;//global::balance 
int x_1_1;//global::balance 
int x_1_2;//global::balance 
int x_1_3;//global::balance 
int x_2_0;//global::sum_thread1 
int x_2_1;//global::sum_thread1 
int x_2_2;//global::sum_thread1 
int x_3_0;//global::sum_thread2 
int x_3_1;//global::sum_thread2 
int x_3_2;//global::sum_thread2 
int x_4_0;//global::join_t1 
int x_4_1;//global::join_t1 
int x_4_2;//global::join_t1 
int x_5_0;//global::join_t2 
int x_5_1;//global::join_t2 
int x_5_2;//global::join_t2 
int x_6_0;//global::trs 
int x_7_0;//global::trs->num 
int x_7_1;//global::trs->num 
int x_8_0;//global::trs->t_array[0].amount 
int x_8_1;//global::trs->t_array[0].amount 
int x_9_0;//global::trs->t_array[0].type 
int x_9_1;//global::trs->t_array[0].type 
int x_10_0;//global::trs->t_array[1].amount 
int x_10_1;//global::trs->t_array[1].amount 
int x_11_0;//global::trs->t_array[1].type 
int x_11_1;//global::trs->t_array[1].type 
int x_12_0;//main::orgBalance T0
int x_12_1;//main::orgBalance T0
int x_13_0;//functioncall::param T0
int x_13_1;//functioncall::param T0
int x_14_0;//new_transactions::i T0
int x_14_1;//new_transactions::i T0
int x_14_2;//new_transactions::i T0
int x_14_3;//new_transactions::i T0
int x_15_0;//new_transactions::amounts[0] T0
int x_15_1;//new_transactions::amounts[0] T0
int x_16_0;//new_transactions::amounts[1] T0
int x_16_1;//new_transactions::amounts[1] T0
int x_17_0;//new_transactions::types[0] T0
int x_17_1;//new_transactions::types[0] T0
int x_18_0;//new_transactions::types[1] T0
int x_18_1;//new_transactions::types[1] T0
int x_19_0;//main::expBalance T0
int x_19_1;//main::expBalance T0
int x_19_2;//main::expBalance T0
int x_19_3;//main::expBalance T0
int x_20_0;//thread1::upper_bound T1
int x_20_1;//thread1::upper_bound T1
int x_21_0;//thread1::i T1
int x_21_1;//thread1::i T1
int x_21_2;//thread1::i T1
int x_22_0;//thread1::tmp_type T1
int x_22_1;//thread1::tmp_type T1
int x_23_0;//thread1::tmp_amount T1
int x_23_1;//thread1::tmp_amount T1
int x_24_0;//functioncall::param T1
int x_24_1;//functioncall::param T1
int x_25_0;//functioncall::param T1
int x_25_1;//functioncall::param T1
int x_26_0;//do_transaction::applied T1
int x_27_0;//do_transaction::tmp_type T1
int x_27_1;//do_transaction::tmp_type T1
int x_28_0;//functioncall::param T1
int x_28_1;//functioncall::param T1
int x_29_0;//deposit::tmpBalance T1
int x_29_1;//deposit::tmpBalance T1
int x_29_2;//deposit::tmpBalance T1
int x_30_0;//deposit::applied T1
int x_30_1;//deposit::applied T1
int x_31_0;//functioncall::param T1
int x_31_1;//functioncall::param T1
int x_32_0;//functioncall::param T1
int x_32_1;//functioncall::param T1
int x_33_0;//thread2::upper_bound T2
int x_33_1;//thread2::upper_bound T2
int x_34_0;//thread2::i T2
int x_34_1;//thread2::i T2
int x_34_2;//thread2::i T2
int x_35_0;//thread2::tmp_type T2
int x_35_1;//thread2::tmp_type T2
int x_36_0;//thread2::tmp_amount T2
int x_36_1;//thread2::tmp_amount T2
int x_37_0;//functioncall::param T2
int x_37_1;//functioncall::param T2
int x_38_0;//functioncall::param T2
int x_38_1;//functioncall::param T2
int x_39_0;//do_transaction::applied T2
int x_40_0;//do_transaction::tmp_type T2
int x_40_1;//do_transaction::tmp_type T2
int x_41_0;//functioncall::param T2
int x_41_1;//functioncall::param T2
int x_42_0;//withdraw::tmpBalance T2
int x_42_1;//withdraw::tmpBalance T2
int x_42_2;//withdraw::tmpBalance T2
int x_43_0;//withdraw::applied T2
int x_43_1;//withdraw::applied T2
int x_44_0;//functioncall::param T2
int x_44_1;//functioncall::param T2
int x_45_0;//functioncall::param T2
int x_45_1;//functioncall::param T2

T_0_0_0: x_0_0 = -1;
T_0_1_0: x_1_0 = 0;
T_0_2_0: x_1_1 = 40;
T_0_3_0: x_2_0 = 0;
T_0_4_0: x_2_1 = 0;
T_0_5_0: x_3_0 = 0;
T_0_6_0: x_3_1 = 0;
T_0_7_0: x_4_0 = 0;
T_0_8_0: x_4_1 = 0;
T_0_9_0: x_5_0 = 0;
T_0_10_0: x_5_1 = 0;
T_0_11_0: x_12_0 = 2129070432;
T_0_12_0: x_12_1 = x_1_1;
T_0_13_0: x_13_0 = 748266769;
T_0_14_0: x_13_1 = 2;
T_0_15_0: x_14_0 = 0;
T_0_16_0: x_6_0 = 0;
T_0_17_0: x_7_0 = 2139524024;
T_0_18_0: x_7_1 = x_13_1;
T_0_19_0: x_15_0 = 0;
T_0_20_0: x_16_0 = 0;
T_0_21_0: x_15_1 = 10;
T_0_22_0: x_16_1 = 20;
T_0_23_0: x_17_0 = 0;
T_0_24_0: x_18_0 = 0;
T_0_25_0: x_17_1 = 1;
T_0_26_0: x_18_1 = 0;
T_0_27_0: x_14_1 = 0;
T_0_28_0: if (x_14_1 < x_13_1)  x_8_0 = 0;
T_0_29_0: if (x_14_1 < x_13_1)  x_9_0 = 0;
T_0_30_0: if (x_14_1 < x_13_1)  x_8_1 = x_15_1;
T_0_31_0: if (x_14_1 < x_13_1)  x_9_1 = x_17_1;
T_0_32_0: x_14_2 = 1 + x_14_1;
T_0_33_0: if (x_14_2 < x_13_1)  x_10_0 = 0;
T_0_34_0: if (x_14_2 < x_13_1)  x_11_0 = 0;
T_0_35_0: if (x_14_2 < x_13_1)  x_10_1 = x_16_1;
T_0_36_0: if (x_14_2 < x_13_1)  x_11_1 = x_18_1;
T_0_37_0: x_14_3 = 1 + x_14_2;
T_1_38_1: x_20_0 = 2131240100;
T_2_39_2: x_33_0 = 0;
T_1_40_1: x_20_1 = 1;
T_1_41_1: x_21_0 = 10963;
T_1_42_1: x_21_1 = 0;
T_1_43_1: if (x_21_1 < x_20_1)  x_22_0 = 0;
T_2_44_2: x_33_1 = 1;
T_2_45_2: x_34_0 = 2131240100;
T_2_46_2: x_34_1 = x_33_1;
T_2_47_2: if (x_34_1 < x_7_1)  x_35_0 = 10963;
T_2_48_2: if (x_34_1 < x_7_1)  x_35_1 = x_11_1;
T_2_49_2: if (x_34_1 < x_7_1)  x_36_0 = 0;
T_2_50_2: if (x_34_1 < x_7_1)  x_36_1 = x_10_1;
T_2_51_2: if (x_34_1 < x_7_1)  x_37_0 = 556794905;
T_2_52_2: if (x_34_1 < x_7_1)  x_37_1 = x_36_1;
T_2_53_2: if (x_34_1 < x_7_1)  x_38_0 = 1805043704;
T_2_54_2: if (x_34_1 < x_7_1)  x_38_1 = x_35_1;
T_2_55_2: if (x_34_1 < x_7_1)  x_39_0 = 10963;
T_2_56_2: if (x_34_1 < x_7_1)  x_40_0 = -2115238144;
T_2_57_2: if (x_34_1 < x_7_1)  x_40_1 = x_38_1;
T_2_58_2: if (x_34_1 < x_7_1 && x_40_1 == 0)  x_41_0 = 691980359;
T_2_59_2: if (x_34_1 < x_7_1 && x_40_1 == 0)  x_41_1 = x_37_1;
T_2_60_2: if (x_34_1 < x_7_1 && x_40_1 == 0)  x_42_0 = 0;
T_2_61_2: if (x_34_1 < x_7_1 && x_40_1 == 0)  x_43_0 = 0;
T_2_62_2: if (x_34_1 < x_7_1 && x_40_1 == 0 && 0 == x_0_0 + 1)  x_0_1 = 2;
T_2_63_2: if (x_34_1 < x_7_1 && x_40_1 == 0 && 2 == x_0_1)  x_42_1 = x_1_1;
T_2_64_2: if (x_34_1 < x_7_1 && x_40_1 == 0 && 2 == x_0_1)  x_0_2 = -1;
T_1_65_1: if (x_21_1 < x_20_1)  x_22_1 = x_9_1;
T_1_66_1: if (x_21_1 < x_20_1)  x_23_0 = 0;
T_1_67_1: if (x_21_1 < x_20_1)  x_23_1 = x_8_1;
T_1_68_1: if (x_21_1 < x_20_1)  x_24_0 = 1613673012;
T_1_69_1: if (x_21_1 < x_20_1)  x_24_1 = x_23_1;
T_1_70_1: if (x_21_1 < x_20_1)  x_25_0 = 1343916093;
T_1_71_1: if (x_21_1 < x_20_1)  x_25_1 = x_22_1;
T_1_72_1: if (x_21_1 < x_20_1)  x_26_0 = 10963;
T_1_73_1: if (x_21_1 < x_20_1)  x_27_0 = -2117339392;
T_1_74_1: if (x_21_1 < x_20_1)  x_27_1 = x_25_1;
T_1_75_1: if (x_21_1 < x_20_1 && x_27_1 != 0)  x_28_0 = 1915995309;
T_1_76_1: if (x_21_1 < x_20_1 && x_27_1 != 0)  x_28_1 = x_24_1;
T_1_77_1: if (x_21_1 < x_20_1 && x_27_1 != 0)  x_29_0 = 0;
T_1_78_1: if (x_21_1 < x_20_1 && x_27_1 != 0)  x_30_0 = 0;
T_1_79_1: if (x_21_1 < x_20_1 && x_27_1 != 0 && 0 == x_0_2 + 1)  x_0_3 = 1;
T_1_80_1: if (x_21_1 < x_20_1 && x_27_1 != 0 && 1 == x_0_3)  x_29_1 = x_1_1;
T_1_81_1: if (x_21_1 < x_20_1 && x_27_1 != 0 && 1 == x_0_3)  x_0_4 = -1;
T_2_82_2: if (x_34_1 < x_7_1 && x_40_1 == 0 && x_42_1 >= x_41_1)  x_42_2 = -1*x_41_1 + x_42_1;
T_2_83_2: if (x_34_1 < x_7_1 && x_40_1 == 0 && x_42_1 >= x_41_1)  x_43_1 = 1;
T_2_84_2: if (x_34_1 < x_7_1 && x_40_1 == 0 && 0 == x_0_4 + 1)  x_0_5 = 2;
T_2_85_2: if (x_34_1 < x_7_1 && x_40_1 == 0 && 2 == x_0_5)  x_1_2 = x_42_2;
T_2_86_2: if (x_34_1 < x_7_1 && x_40_1 == 0 && 2 == x_0_5)  x_0_6 = -1;
T_2_87_2: if (x_34_1 < x_7_1 && x_40_1 == 0)  x_44_0 = 500297110;
T_2_88_2: if (x_34_1 < x_7_1 && x_40_1 == 0)  x_44_1 = x_43_1;
T_2_89_2: if (x_34_1 < x_7_1)  x_45_0 = 1496235047;
T_2_90_2: if (x_34_1 < x_7_1)  x_45_1 = x_44_1;
T_1_91_1: if (x_21_1 < x_20_1 && x_27_1 != 0 && x_28_1 + x_29_1 <= 100)  x_29_2 = x_28_1 + x_29_1;
T_1_92_1: if (x_21_1 < x_20_1 && x_27_1 != 0 && x_28_1 + x_29_1 <= 100)  x_30_1 = 1;
T_2_93_2: if (x_34_1 < x_7_1 && x_45_1 != 0 && x_35_1 == 0)  x_3_2 = x_3_1 + -1*x_36_1;
T_1_94_1: if (x_21_1 < x_20_1 && x_27_1 != 0 && 0 == x_0_6 + 1)  x_0_7 = 1;
T_1_95_1: if (x_21_1 < x_20_1 && x_27_1 != 0 && 1 == x_0_7)  x_1_3 = x_29_2;
T_2_96_2: x_34_2 = 1 + x_34_1;
T_1_97_1: if (x_21_1 < x_20_1 && x_27_1 != 0 && 1 == x_0_7)  x_0_8 = -1;
T_2_98_2: x_5_2 = 1;
T_1_99_1: if (x_21_1 < x_20_1 && x_27_1 != 0)  x_31_0 = 97132993;
T_1_100_1: if (x_21_1 < x_20_1 && x_27_1 != 0)  x_31_1 = x_30_1;
T_1_101_1: if (x_21_1 < x_20_1)  x_32_0 = 201942469;
T_1_102_1: if (x_21_1 < x_20_1)  x_32_1 = x_31_1;
T_1_103_1: if (x_21_1 < x_20_1 && x_32_1 != 0 && x_22_1 != 0)  x_2_2 = x_2_1 + x_23_1;
T_1_104_1: x_21_2 = 1 + x_21_1;
T_1_105_1: x_4_2 = 1;
T_0_106_0: if (x_4_2 != 0 && x_5_2 != 0)  x_19_0 = 10963;
T_0_107_0: if (x_4_2 != 0 && x_5_2 != 0)  x_19_1 = x_12_1;
T_0_108_0: if (x_4_2 != 0 && x_5_2 != 0)  x_19_2 = x_2_2 + x_19_1;
T_0_109_0: if (x_4_2 != 0 && x_5_2 != 0)  x_19_3 = x_3_2 + x_19_2;
T_0_110_0: if (x_4_2 != 0 && x_5_2 != 0)  assert(x_19_3 == x_1_3);
}
