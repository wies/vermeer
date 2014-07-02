#include "gzip_before_main.h"

//line 4634 "gzip.preprocessed.c"
int main(int  argc__1, char ** argv__1){
  int  file_count__1;
  int  proglen__1;
  int  optc__1;
  size_t  tmp__1;
  int  tmp___0__1;
  __sighandler_t  tmp___1__1;
  __sighandler_t  tmp___2__1;
  __sighandler_t  tmp___3__1;
  int  tmp___4__1;
  int  tmp___5__1;
  int  tmp___6__1;
  int  tmp___7__1;
  size_t  tmp___8__1;
  size_t  tmp___9__1;
  int  tmp___10__1;
  int  tmp___11__1;
  char *** __cil_tmp19__1;
  char ** __cil_tmp20__1;
  char ** __cil_tmp21__1;
  char * __cil_tmp22__1;
  char const   * __cil_tmp23__1;
  char * __cil_tmp24__1;
  char * __cil_tmp25__1;
  char const   * __cil_tmp26__1;
  int  __cil_tmp27__1;
  char * __cil_tmp28__1;
  char * __cil_tmp29__1;
  void * __cil_tmp30__1;
  unsigned long  __cil_tmp31__1;
  unsigned long  __cil_tmp32__1;
  char *** __cil_tmp33__1;
  void (* __cil_tmp34__1)(int );
  void (* __cil_tmp35__1)(int );
  unsigned long  __cil_tmp36__1;
  unsigned long  __cil_tmp37__1;
  void (* __cil_tmp38__1)(int );
  void (* __cil_tmp39__1)(int );
  void (* __cil_tmp40__1)(int );
  unsigned long  __cil_tmp41__1;
  unsigned long  __cil_tmp42__1;
  void (* __cil_tmp43__1)(int );
  void (* __cil_tmp44__1)(int );
  void (* __cil_tmp45__1)(int );
  unsigned long  __cil_tmp46__1;
  unsigned long  __cil_tmp47__1;
  void (* __cil_tmp48__1)(int );
  char const   * __cil_tmp49__1;
  size_t  __cil_tmp50__1;
  char const   * __cil_tmp51__1;
  size_t  __cil_tmp52__1;
  char * __cil_tmp53__1;
  char const   * __cil_tmp54__1;
  char const   * __cil_tmp55__1;
  unsigned long  __cil_tmp56__1;
  unsigned long  __cil_tmp57__1;
  char * __cil_tmp58__1;
  char * __restrict   __cil_tmp59__1;
  char const   * __restrict   __cil_tmp60__1;
  unsigned long  __cil_tmp61__1;
  unsigned long  __cil_tmp62__1;
  unsigned long  __cil_tmp63__1;
  char * __cil_tmp64__1;
  char const   * __cil_tmp65__1;
  int * __cil_tmp66__1;
  int  __cil_tmp67__1;
  char *** __cil_tmp68__1;
  char ** __cil_tmp69__1;
  char * const  * __cil_tmp70__1;
  unsigned long  __cil_tmp71__1;
  unsigned long  __cil_tmp72__1;
  struct option * __cil_tmp73__1;
  struct option  const  * __cil_tmp74__1;
  int * __cil_tmp75__1;
  char const   * __cil_tmp76__1;
  char const   * __cil_tmp77__1;
  unsigned long  __cil_tmp78__1;
  unsigned long  __cil_tmp79__1;
  char * __cil_tmp80__1;
  char * __restrict   __cil_tmp81__1;
  char const   * __restrict   __cil_tmp82__1;
  FILE * __restrict   __cil_tmp83__1;
  char const   * __restrict   __cil_tmp84__1;
  int * __cil_tmp85__1;
  int  __cil_tmp86__1;
  FILE * __restrict   __cil_tmp87__1;
  char const   * __restrict   __cil_tmp88__1;
  FILE * __restrict   __cil_tmp89__1;
  char const   * __restrict   __cil_tmp90__1;
  FILE * __restrict   __cil_tmp91__1;
  char const   * __restrict   __cil_tmp92__1;
  int * __cil_tmp93__1;
  int  __cil_tmp94__1;
  char *** __cil_tmp95__1;
  char ** __cil_tmp96__1;
  char ** __cil_tmp97__1;
  char * __cil_tmp98__1;
//line 4642 "gzip.preprocessed.c"
  __cil_tmp19__1 = &argv__1;
//line 4642 "gzip.preprocessed.c"
  __cil_tmp20__1 = *__cil_tmp19__1;
//line 4642 "gzip.preprocessed.c"
  __cil_tmp21__1 = (__cil_tmp20__1) + (0);
//line 4642 "gzip.preprocessed.c"
  __cil_tmp22__1 = *__cil_tmp21__1;
//line 4642 "gzip.preprocessed.c"
  //progname = basename(__cil_tmp22__1);
  {
//line 4642 "gzip.preprocessed.c"
    char * __arg_tmp_0__2  = __cil_tmp22__1;
//line 4642 "gzip.preprocessed.c"
    char *__return__2;
//line 4109 "gzip.preprocessed.c"
    //enter basename
    char * fname__2 = __arg_tmp_0__2 ;
    char * p__2;
    char const   * __cil_tmp3__2;
    void * __cil_tmp4__2;
    unsigned long  __cil_tmp5__2;
    unsigned long  __cil_tmp6__2;
//line 4113 "gzip.preprocessed.c"
    __cil_tmp3__2 = (char const   *)(fname__2);
//line 4113 "gzip.preprocessed.c"
    //p__2 = strrchr(__cil_tmp3__2, '/');
    {
//line 4113 "gzip.preprocessed.c"
      char const   * __arg_tmp_0__3  = __cil_tmp3__2;
//line 4113 "gzip.preprocessed.c"
      int  __arg_tmp_1__3  = '/';
//line 4113 "gzip.preprocessed.c"
      char *__return__3;
//line 4113 "gzip.preprocessed.c"
      p__2 = __return__3;
    }
//line 4113 "gzip.preprocessed.c"
    __cil_tmp4__2 = (void *)(0);
//line 4113 "gzip.preprocessed.c"
    __cil_tmp5__2 = (unsigned long )(__cil_tmp4__2);
//line 4113 "gzip.preprocessed.c"
    __cil_tmp6__2 = (unsigned long )(p__2);
//line 4113 "gzip.preprocessed.c"
    fname__2 = (p__2) + (1);
//line 4115 "gzip.preprocessed.c"
    //exiting basename
//line 4115 "gzip.preprocessed.c"
    __return__2 = fname__2;
//line 4642 "gzip.preprocessed.c"
    progname = __return__2;
  }
//line 4643 "gzip.preprocessed.c"
  __cil_tmp23__1 = (char const   *)(progname);
//line 4643 "gzip.preprocessed.c"
  //tmp__1 = strlen(__cil_tmp23__1);
  {
//line 4643 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp23__1;
//line 4643 "gzip.preprocessed.c"
    size_t __return__2;
//line 4643 "gzip.preprocessed.c"
    tmp__1 = __return__2;
  }
//line 4643 "gzip.preprocessed.c"
  proglen__1 = (int )(tmp__1);
//line 4644 "gzip.preprocessed.c"
  __cil_tmp24__1 = (progname) + (proglen__1);
//line 4644 "gzip.preprocessed.c"
  __cil_tmp25__1 = (__cil_tmp24__1) - (4);
//line 4644 "gzip.preprocessed.c"
  __cil_tmp26__1 = (char const   *)(__cil_tmp25__1);
//line 4644 "gzip.preprocessed.c"
  //tmp___0__1 = strcmp(__cil_tmp26__1, ".exe");
  {
//line 4644 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp26__1;
//line 4644 "gzip.preprocessed.c"
    char const   * __arg_tmp_1__2  = ".exe";
//line 4644 "gzip.preprocessed.c"
    int __return__2;
//line 4644 "gzip.preprocessed.c"
    tmp___0__1 = __return__2;
  }
//line 4647 "gzip.preprocessed.c"
  __cil_tmp29__1 = (char *)("GZIP");
//line 4647 "gzip.preprocessed.c"
  //env = add_envopt(&argc__1, &argv__1, __cil_tmp29__1);
  {
//line 4647 "gzip.preprocessed.c"
    int * __arg_tmp_0__2  = &argc__1;//DSN change
//line 4647 "gzip.preprocessed.c"
    char *** __arg_tmp_1__2  = &argv__1;//DSN change
//line 4647 "gzip.preprocessed.c"
    char * __arg_tmp_2__2  = __cil_tmp29__1;
//line 4647 "gzip.preprocessed.c"
    char *__return__2;
//line 4127 "gzip.preprocessed.c"
    //enter add_envopt
    int * argcp__2 = __arg_tmp_0__2 ;
    char *** argvp__2 = __arg_tmp_1__2 ;
    char * env__2 = __arg_tmp_2__2 ;
    char * p__2;
    char ** oargv__2;
    char ** nargv__2;
    int  oargc__2;
    int  nargc__2;
    char * tmp__2;
    size_t  tmp___0__2;
    voidp  tmp___1__2;
    size_t  tmp___2__2;
    size_t  tmp___3__2;
    char * tmp___4__2;
    void * tmp___5__2;
    int  tmp___6__2;
    char ** tmp___7__2;
    char ** tmp___8__2;
    size_t  tmp___9__2;
    char ** tmp___10__2;
    char * tmp___11__2;
    char ** tmp___12__2;
    char ** tmp___13__2;
    int  tmp___14__2;
    char const   * __cil_tmp25__2;
    void * __cil_tmp26__2;
    unsigned long  __cil_tmp27__2;
    unsigned long  __cil_tmp28__2;
    void * __cil_tmp29__2;
    char const   * __cil_tmp30__2;
    size_t  __cil_tmp31__2;
    unsigned int  __cil_tmp32__2;
    char * __restrict   __cil_tmp33__2;
    char const   * __restrict   __cil_tmp34__2;
    char const   * __cil_tmp35__2;
    char  __cil_tmp36__2;
    int  __cil_tmp37__2;
    char const   * __cil_tmp38__2;
    void * __cil_tmp39__2;
    void * __cil_tmp40__2;
    int  __cil_tmp41__2;
    int  __cil_tmp42__2;
    int  __cil_tmp43__2;
    size_t  __cil_tmp44__2;
    void * __cil_tmp45__2;
    unsigned long  __cil_tmp46__2;
    unsigned long  __cil_tmp47__2;
    char * __cil_tmp48__2;
    char * __cil_tmp49__2;
    char const   * __cil_tmp50__2;
    void * __cil_tmp51__2;
//line 4135 "gzip.preprocessed.c"
    oargc__2 = *argcp__2;
//line 4136 "gzip.preprocessed.c"
    nargc__2 = 0;
//line 4137 "gzip.preprocessed.c"
    __cil_tmp25__2 = (char const   *)(env__2);
//line 4137 "gzip.preprocessed.c"
    //tmp__2 = getenv(__cil_tmp25__2);
    {
//line 4137 "gzip.preprocessed.c"
      char const   * __arg_tmp_0__3  = __cil_tmp25__2;
//line 4137 "gzip.preprocessed.c"
      char *__return__3;
//line 4137 "gzip.preprocessed.c"
      tmp__2 = __return__3;
    }
//line 4137 "gzip.preprocessed.c"
    env__2 = tmp__2;
//line 4138 "gzip.preprocessed.c"
    __cil_tmp26__2 = (void *)(0);
//line 4138 "gzip.preprocessed.c"
    __cil_tmp27__2 = (unsigned long )(__cil_tmp26__2);
//line 4138 "gzip.preprocessed.c"
    __cil_tmp28__2 = (unsigned long )(env__2);
//line 4138 "gzip.preprocessed.c"
    __cil_tmp29__2 = (void *)(0);
//line 4138 "gzip.preprocessed.c"
    //exiting add_envopt
//line 4138 "gzip.preprocessed.c"
    __return__2 = (char *)(__cil_tmp29__2);
//line 4647 "gzip.preprocessed.c"
    env = __return__2;
  }
//line 4648 "gzip.preprocessed.c"
  __cil_tmp30__1 = (void *)(0);
//line 4648 "gzip.preprocessed.c"
  __cil_tmp31__1 = (unsigned long )(__cil_tmp30__1);
//line 4648 "gzip.preprocessed.c"
  __cil_tmp32__1 = (unsigned long )(env);
//line 4649 "gzip.preprocessed.c"
  __cil_tmp34__1 = (void (*)(int  ))(1);
//line 4649 "gzip.preprocessed.c"
  //tmp___1__1 = signal(2, __cil_tmp34__1);
  {
//line 4649 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 2;
//line 4649 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp34__1;
//line 4649 "gzip.preprocessed.c"
    __sighandler_t __return__2;
//line 4649 "gzip.preprocessed.c"
    tmp___1__1 = __return__2;
  }
//line 4649 "gzip.preprocessed.c"
  __cil_tmp35__1 = (void (*)(int  ))(1);
//line 4649 "gzip.preprocessed.c"
  __cil_tmp36__1 = (unsigned long )(__cil_tmp35__1);
//line 4649 "gzip.preprocessed.c"
  __cil_tmp37__1 = (unsigned long )(tmp___1__1);
//line 4649 "gzip.preprocessed.c"
  foreground = (__cil_tmp37__1) != (__cil_tmp36__1);
//line 4651 "gzip.preprocessed.c"
  __cil_tmp38__1 = (void (*)(int  ))(&abort_gzip);
//line 4651 "gzip.preprocessed.c"
  //signal(2, __cil_tmp38__1);
  {
//line 4651 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 2;
//line 4651 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp38__1;
  }
//line 4653 "gzip.preprocessed.c"
  __cil_tmp39__1 = (void (*)(int  ))(1);
//line 4653 "gzip.preprocessed.c"
  //tmp___2__1 = signal(15, __cil_tmp39__1);
  {
//line 4653 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 15;
//line 4653 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp39__1;
//line 4653 "gzip.preprocessed.c"
    __sighandler_t __return__2;
//line 4653 "gzip.preprocessed.c"
    tmp___2__1 = __return__2;
  }
//line 4653 "gzip.preprocessed.c"
  __cil_tmp40__1 = (void (*)(int  ))(1);
//line 4653 "gzip.preprocessed.c"
  __cil_tmp41__1 = (unsigned long )(__cil_tmp40__1);
//line 4653 "gzip.preprocessed.c"
  __cil_tmp42__1 = (unsigned long )(tmp___2__1);
//line 4654 "gzip.preprocessed.c"
  __cil_tmp43__1 = (void (*)(int  ))(&abort_gzip);
//line 4654 "gzip.preprocessed.c"
  //signal(15, __cil_tmp43__1);
  {
//line 4654 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 15;
//line 4654 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp43__1;
  }
//line 4656 "gzip.preprocessed.c"
  __cil_tmp44__1 = (void (*)(int  ))(1);
//line 4656 "gzip.preprocessed.c"
  //tmp___3__1 = signal(1, __cil_tmp44__1);
  {
//line 4656 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 1;
//line 4656 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp44__1;
//line 4656 "gzip.preprocessed.c"
    __sighandler_t __return__2;
//line 4656 "gzip.preprocessed.c"
    tmp___3__1 = __return__2;
  }
//line 4656 "gzip.preprocessed.c"
  __cil_tmp45__1 = (void (*)(int  ))(1);
//line 4656 "gzip.preprocessed.c"
  __cil_tmp46__1 = (unsigned long )(__cil_tmp45__1);
//line 4656 "gzip.preprocessed.c"
  __cil_tmp47__1 = (unsigned long )(tmp___3__1);
//line 4657 "gzip.preprocessed.c"
  __cil_tmp48__1 = (void (*)(int  ))(&abort_gzip);
//line 4657 "gzip.preprocessed.c"
  //signal(1, __cil_tmp48__1);
  {
//line 4657 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 1;
//line 4657 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp48__1;
  }
//line 4659 "gzip.preprocessed.c"
  __cil_tmp49__1 = (char const   *)(progname);
//line 4659 "gzip.preprocessed.c"
  __cil_tmp50__1 = (size_t )(2);
//line 4659 "gzip.preprocessed.c"
  //tmp___6__1 = strncmp(__cil_tmp49__1, "un", __cil_tmp50__1);
  {
//line 4659 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp49__1;
//line 4659 "gzip.preprocessed.c"
    char const   * __arg_tmp_1__2  = "un";
//line 4659 "gzip.preprocessed.c"
    size_t  __arg_tmp_2__2  = __cil_tmp50__1;
//line 4659 "gzip.preprocessed.c"
    int __return__2;
//line 4659 "gzip.preprocessed.c"
    tmp___6__1 = __return__2;
  }
//line 4659 "gzip.preprocessed.c"
  __cil_tmp51__1 = (char const   *)(progname);
//line 4659 "gzip.preprocessed.c"
  __cil_tmp52__1 = (size_t )(3);
//line 4659 "gzip.preprocessed.c"
  //tmp___7__1 = strncmp(__cil_tmp51__1, "gun", __cil_tmp52__1);
  {
//line 4659 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp51__1;
//line 4659 "gzip.preprocessed.c"
    char const   * __arg_tmp_1__2  = "gun";
//line 4659 "gzip.preprocessed.c"
    size_t  __arg_tmp_2__2  = __cil_tmp52__1;
//line 4659 "gzip.preprocessed.c"
    int __return__2;
//line 4659 "gzip.preprocessed.c"
    tmp___7__1 = __return__2;
  }
//line 4662 "gzip.preprocessed.c"
  __cil_tmp53__1 = (progname) + (1);
//line 4662 "gzip.preprocessed.c"
  __cil_tmp54__1 = (char const   *)(__cil_tmp53__1);
//line 4662 "gzip.preprocessed.c"
  //tmp___4__1 = strcmp(__cil_tmp54__1, "cat");
  {
//line 4662 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp54__1;
//line 4662 "gzip.preprocessed.c"
    char const   * __arg_tmp_1__2  = "cat";
//line 4662 "gzip.preprocessed.c"
    int __return__2;
//line 4662 "gzip.preprocessed.c"
    tmp___4__1 = __return__2;
  }
//line 4662 "gzip.preprocessed.c"
  __cil_tmp55__1 = (char const   *)(progname);
//line 4662 "gzip.preprocessed.c"
  //tmp___5__1 = strcmp(__cil_tmp55__1, "gzcat");
  {
//line 4662 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp55__1;
//line 4662 "gzip.preprocessed.c"
    char const   * __arg_tmp_1__2  = "gzcat";
//line 4662 "gzip.preprocessed.c"
    int __return__2;
//line 4662 "gzip.preprocessed.c"
    tmp___5__1 = __return__2;
  }
//line 4666 "gzip.preprocessed.c"
  __cil_tmp56__1 = (0) * (1UL);
//line 4666 "gzip.preprocessed.c"
  __cil_tmp57__1 = ((unsigned long )(z_suffix)) + (__cil_tmp56__1);
//line 4666 "gzip.preprocessed.c"
  __cil_tmp58__1 = (char *)(__cil_tmp57__1);
//line 4666 "gzip.preprocessed.c"
  __cil_tmp59__1 = (char * __restrict  )(__cil_tmp58__1);
//line 4666 "gzip.preprocessed.c"
  __cil_tmp60__1 = (char const   * __restrict  )(".gz");
//line 4666 "gzip.preprocessed.c"
  __cil_tmp61__1 = (31UL) - (1UL);
//line 4666 "gzip.preprocessed.c"
  //strncpy(__cil_tmp59__1, __cil_tmp60__1, __cil_tmp61__1);
  {
//line 4666 "gzip.preprocessed.c"
    char * __restrict   __arg_tmp_0__2  = __cil_tmp59__1;
//line 4666 "gzip.preprocessed.c"
    char const   * __restrict   __arg_tmp_1__2  = __cil_tmp60__1;
//line 4666 "gzip.preprocessed.c"
    unsigned long  __arg_tmp_2__2  = __cil_tmp61__1;
  }
//line 4667 "gzip.preprocessed.c"
  __cil_tmp62__1 = (0) * (1UL);
//line 4667 "gzip.preprocessed.c"
  __cil_tmp63__1 = ((unsigned long )(z_suffix)) + (__cil_tmp62__1);
//line 4667 "gzip.preprocessed.c"
  __cil_tmp64__1 = (char *)(__cil_tmp63__1);
//line 4667 "gzip.preprocessed.c"
  __cil_tmp65__1 = (char const   *)(__cil_tmp64__1);
//line 4667 "gzip.preprocessed.c"
  //tmp___8__1 = strlen(__cil_tmp65__1);
  {
//line 4667 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp65__1;
//line 4667 "gzip.preprocessed.c"
    size_t __return__2;
//line 4667 "gzip.preprocessed.c"
    tmp___8__1 = __return__2;
  }
//line 4667 "gzip.preprocessed.c"
  z_len = (int )(tmp___8__1);
//line 4668 "gzip.preprocessed.c"
  __cil_tmp66__1 = &argc__1;
//line 4668 "gzip.preprocessed.c"
  __cil_tmp67__1 = *__cil_tmp66__1;
//line 4668 "gzip.preprocessed.c"
  __cil_tmp68__1 = &argv__1;
//line 4668 "gzip.preprocessed.c"
  __cil_tmp69__1 = *__cil_tmp68__1;
//line 4668 "gzip.preprocessed.c"
  __cil_tmp70__1 = (char * const  *)(__cil_tmp69__1);
//line 4668 "gzip.preprocessed.c"
  __cil_tmp71__1 = (0) * (32UL);
//line 4668 "gzip.preprocessed.c"
  __cil_tmp72__1 = ((unsigned long )(longopts)) + (__cil_tmp71__1);
//line 4668 "gzip.preprocessed.c"
  __cil_tmp73__1 = (struct option *)(__cil_tmp72__1);
//line 4668 "gzip.preprocessed.c"
  __cil_tmp74__1 = (struct option  const  *)(__cil_tmp73__1);
//line 4668 "gzip.preprocessed.c"
  __cil_tmp75__1 = (int *)(0);
//line 4668 "gzip.preprocessed.c"
  //DSN changed this
  optc__1 = getopt_long(__cil_tmp67__1, __cil_tmp70__1, "ab:cdfhH?lLmMnNqrS:tvVZ123456789", __cil_tmp74__1, __cil_tmp75__1);
/*   { */
/* //line 4668 "gzip.preprocessed.c" */
/*     int  __arg_tmp_0__2  = __cil_tmp67__1; */
/* //line 4668 "gzip.preprocessed.c" */
/*     char * const  * __arg_tmp_1__2  = __cil_tmp70__1; */
/* //line 4668 "gzip.preprocessed.c" */
/*     char const   * __arg_tmp_2__2  = "ab:cdfhH?lLmMnNqrS:tvVZ123456789"; */
/* //line 4668 "gzip.preprocessed.c" */
/*     struct option  const  * __arg_tmp_3__2  = __cil_tmp74__1; */
/* //line 4668 "gzip.preprocessed.c" */
/*     int * __arg_tmp_4__2  = __cil_tmp75__1; */
/* //line 4668 "gzip.preprocessed.c" */
/*     int __return__2; */
/* //line 4668 "gzip.preprocessed.c" */
/*     optc__1 = __return__2; */
/*   } */
//line 4679 "gzip.preprocessed.c"
  decompress = 1;
//line 4668 "gzip.preprocessed.c"
  __cil_tmp66__1 = &argc__1;
//line 4668 "gzip.preprocessed.c"
  __cil_tmp67__1 = *__cil_tmp66__1;
//line 4668 "gzip.preprocessed.c"
  __cil_tmp68__1 = &argv__1;
//line 4668 "gzip.preprocessed.c"
  __cil_tmp69__1 = *__cil_tmp68__1;
//line 4668 "gzip.preprocessed.c"
  __cil_tmp70__1 = (char * const  *)(__cil_tmp69__1);
//line 4668 "gzip.preprocessed.c"
  __cil_tmp71__1 = (0) * (32UL);
//line 4668 "gzip.preprocessed.c"
  __cil_tmp72__1 = ((unsigned long )(longopts)) + (__cil_tmp71__1);
//line 4668 "gzip.preprocessed.c"
  __cil_tmp73__1 = (struct option *)(__cil_tmp72__1);
//line 4668 "gzip.preprocessed.c"
  __cil_tmp74__1 = (struct option  const  *)(__cil_tmp73__1);
//line 4668 "gzip.preprocessed.c"
  __cil_tmp75__1 = (int *)(0);
//line 4668 "gzip.preprocessed.c"
  //optc__1 = getopt_long(__cil_tmp67__1, __cil_tmp70__1, "ab:cdfhH?lLmMnNqrS:tvVZ123456789", __cil_tmp74__1, __cil_tmp75__1);
  {
//line 4668 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = __cil_tmp67__1;
//line 4668 "gzip.preprocessed.c"
    char * const  * __arg_tmp_1__2  = __cil_tmp70__1;
//line 4668 "gzip.preprocessed.c"
    char const   * __arg_tmp_2__2  = "ab:cdfhH?lLmMnNqrS:tvVZ123456789";
//line 4668 "gzip.preprocessed.c"
    struct option  const  * __arg_tmp_3__2  = __cil_tmp74__1;
//line 4668 "gzip.preprocessed.c"
    int * __arg_tmp_4__2  = __cil_tmp75__1;
//line 4668 "gzip.preprocessed.c"
    int __return__2;
//line 4668 "gzip.preprocessed.c"
    optc__1 = __return__2;
  }
//line 4725 "gzip.preprocessed.c"
  no_time = decompress;
//line 4726 "gzip.preprocessed.c"
  no_name = decompress;
//line 4727 "gzip.preprocessed.c"
  __cil_tmp85__1 = &argc__1;
//line 4727 "gzip.preprocessed.c"
  __cil_tmp86__1 = *__cil_tmp85__1;
//line 4727 "gzip.preprocessed.c"
  file_count__1 = (__cil_tmp86__1) - (optind);
//line 4751 "gzip.preprocessed.c"
  //treat_stdin();
  {
//line 4759 "gzip.preprocessed.c"
    //enter treat_stdin
    char const   * tmp__2;
    char const   * tmp___0__2;
    struct _IO_FILE * tmp___1__2;
    int  tmp___2__2;
    int  tmp___3__2;
    int  tmp___4__2;
    int  tmp___5__2;
    int  tmp___6__2;
    int  tmp___7__2;
    int  tmp___8__2;
    int  tmp___9__2;
    int  tmp___10__2;
    FILE * __restrict   __cil_tmp13__2;
    char const   * __restrict   __cil_tmp14__2;
    FILE * __restrict   __cil_tmp15__2;
    char const   * __restrict   __cil_tmp16__2;
    unsigned long  __cil_tmp17__2;
    unsigned long  __cil_tmp18__2;
    char * __cil_tmp19__2;
    char * __restrict   __cil_tmp20__2;
    char const   * __restrict   __cil_tmp21__2;
    unsigned long  __cil_tmp22__2;
    unsigned long  __cil_tmp23__2;
    char * __cil_tmp24__2;
    char * __restrict   __cil_tmp25__2;
    char const   * __restrict   __cil_tmp26__2;
    long * __cil_tmp27__2;
    char * __cil_tmp28__2;
    long * __cil_tmp29__2;
    int * __cil_tmp30__2;
    int * __cil_tmp31__2;
    int  __cil_tmp32__2;
    int * __cil_tmp33__2;
    int  __cil_tmp34__2;
    int * __cil_tmp35__2;
    int * __cil_tmp36__2;
    int  __cil_tmp37__2;
    FILE * __restrict   __cil_tmp38__2;
    char const   * __restrict   __cil_tmp39__2;
    long  __cil_tmp40__2;
    long  __cil_tmp41__2;
    FILE * __restrict   __cil_tmp42__2;
    char const   * __restrict   __cil_tmp43__2;
//line 4761 "gzip.preprocessed.c"
    tmp___1__2 = stdin;
//line 4761 "gzip.preprocessed.c"
    //tmp___2__2 = fileno(tmp___1__2);
    {
//line 4761 "gzip.preprocessed.c"
      struct _IO_FILE * __arg_tmp_0__3  = tmp___1__2;
//line 4761 "gzip.preprocessed.c"
      int __return__3;
//line 4761 "gzip.preprocessed.c"
      tmp___2__2 = __return__3;
    }
//line 4761 "gzip.preprocessed.c"
    //tmp___3__2 = isatty(tmp___2__2);
    {
//line 4761 "gzip.preprocessed.c"
      int  __arg_tmp_0__3  = tmp___2__2;
//line 4761 "gzip.preprocessed.c"
      int __return__3;
//line 4761 "gzip.preprocessed.c"
      tmp___3__2 = __return__3;
    }
//line 4771 "gzip.preprocessed.c"
    tmp___4__2 = 1;
//line 4774 "gzip.preprocessed.c"
    tmp___5__2 = 1;
//line 4777 "gzip.preprocessed.c"
    __cil_tmp17__2 = (0) * (1UL);
//line 4777 "gzip.preprocessed.c"
    __cil_tmp18__2 = ((unsigned long )(ifname)) + (__cil_tmp17__2);
//line 4777 "gzip.preprocessed.c"
    __cil_tmp19__2 = (char *)(__cil_tmp18__2);
//line 4777 "gzip.preprocessed.c"
    __cil_tmp20__2 = (char * __restrict  )(__cil_tmp19__2);
//line 4777 "gzip.preprocessed.c"
    __cil_tmp21__2 = (char const   * __restrict  )("stdin");
//line 4777 "gzip.preprocessed.c"
    //strcpy(__cil_tmp20__2, __cil_tmp21__2);
    {
//line 4777 "gzip.preprocessed.c"
      char * __restrict   __arg_tmp_0__3  = __cil_tmp20__2;
//line 4777 "gzip.preprocessed.c"
      char const   * __restrict   __arg_tmp_1__3  = __cil_tmp21__2;
    }
//line 4778 "gzip.preprocessed.c"
    __cil_tmp22__2 = (0) * (1UL);
//line 4778 "gzip.preprocessed.c"
    __cil_tmp23__2 = ((unsigned long )(ofname)) + (__cil_tmp22__2);
//line 4778 "gzip.preprocessed.c"
    __cil_tmp24__2 = (char *)(__cil_tmp23__2);
//line 4778 "gzip.preprocessed.c"
    __cil_tmp25__2 = (char * __restrict  )(__cil_tmp24__2);
//line 4778 "gzip.preprocessed.c"
    __cil_tmp26__2 = (char const   * __restrict  )("stdout");
//line 4778 "gzip.preprocessed.c"
    //strcpy(__cil_tmp25__2, __cil_tmp26__2);
    {
//line 4778 "gzip.preprocessed.c"
      char * __restrict   __arg_tmp_0__3  = __cil_tmp25__2;
//line 4778 "gzip.preprocessed.c"
      char const   * __restrict   __arg_tmp_1__3  = __cil_tmp26__2;
    }
//line 4779 "gzip.preprocessed.c"
    __cil_tmp27__2 = &time_stamp;
//line 4779 "gzip.preprocessed.c"
    *__cil_tmp27__2 = 0L;
//line 4786 "gzip.preprocessed.c"
    ifile_size = -1L;
//line 4787 "gzip.preprocessed.c"
    //clear_bufs();
    {
//line 4046 "gzip.preprocessed.c"
      //enter clear_bufs
//line 4048 "gzip.preprocessed.c"
      outcnt = 0U;
//line 4049 "gzip.preprocessed.c"
      inptr = 0U;
//line 4049 "gzip.preprocessed.c"
      insize = inptr;
//line 4050 "gzip.preprocessed.c"
      bytes_out = 0L;
//line 4050 "gzip.preprocessed.c"
      bytes_in = bytes_out;
    }
//line 4788 "gzip.preprocessed.c"
    to_stdout = 1;
//line 4789 "gzip.preprocessed.c"
    part_nb = 0;
//line 4791 "gzip.preprocessed.c"
    __cil_tmp30__2 = &method;
//line 4791 "gzip.preprocessed.c"
    //*__cil_tmp30__2 = get_method(ifd);
    {
//line 4791 "gzip.preprocessed.c"
      int  __arg_tmp_0__3  = ifd;
//line 4791 "gzip.preprocessed.c"
      int __return__3;
//line 5062 "gzip.preprocessed.c"
      //enter get_method
      int  in__3 = __arg_tmp_0__3 ;
      uch  flags___0__3;
      char  magic__3[2];
      ulg  stamp__3;
      unsigned int  tmp__3;
      int  tmp___0__3;
      int  tmp___1__3;
      unsigned int  tmp___2__3;
      int  tmp___3__3;
      int  tmp___4__3;
      unsigned int  tmp___5__3;
      int  tmp___6__3;
      int  tmp___7__3;
      unsigned int  tmp___8__3;
      int  tmp___9__3;
      int  tmp___10__3;
      unsigned int  tmp___11__3;
      int  tmp___12__3;
      int  tmp___13__3;
      unsigned int  tmp___14__3;
      int  tmp___15__3;
      int  tmp___16__3;
      unsigned int  tmp___17__3;
      int  tmp___18__3;
      int  tmp___19__3;
      unsigned int  tmp___20__3;
      int  tmp___21__3;
      int  tmp___22__3;
      unsigned int  tmp___23__3;
      int  tmp___24__3;
      int  tmp___25__3;
      unsigned int  tmp___26__3;
      int  tmp___27__3;
      int  tmp___28__3;
      unsigned int  tmp___29__3;
      unsigned int  tmp___30__3;
      unsigned int  part__3;
      unsigned int  tmp___31__3;
      int  tmp___32__3;
      int  tmp___33__3;
      unsigned int  tmp___34__3;
      int  tmp___35__3;
      int  tmp___36__3;
      unsigned int  len__3;
      unsigned int  tmp___37__3;
      int  tmp___38__3;
      int  tmp___39__3;
      unsigned int  tmp___40__3;
      int  tmp___41__3;
      int  tmp___42__3;
      unsigned int  tmp___43__3;
      unsigned int  tmp___44__3;
      char  c__3;
      unsigned int  tmp___45__3;
      int  tmp___46__3;
      char * p__3;
      char * tmp___47__3;
      char * base__3;
      unsigned int  tmp___48__3;
      int  tmp___49__3;
      int  tmp___50__3;
      char * tmp___51__3;
      unsigned int  tmp___52__3;
      int  tmp___53__3;
      int  tmp___54__3;
      int  tmp___55__3;
      int  tmp___56__3;
      int  tmp___57__3;
      int  tmp___58__3;
      int  tmp___59__3;
      int  tmp___60__3;
      int  tmp___61__3;
      int  tmp___62__3;
      unsigned long  __cil_tmp74__3;
      unsigned long  __cil_tmp75__3;
      uch  __cil_tmp76__3;
      unsigned long  __cil_tmp77__3;
      unsigned long  __cil_tmp78__3;
      unsigned long  __cil_tmp79__3;
      unsigned long  __cil_tmp80__3;
      uch  __cil_tmp81__3;
      unsigned long  __cil_tmp82__3;
      unsigned long  __cil_tmp83__3;
      unsigned long  __cil_tmp84__3;
      unsigned long  __cil_tmp85__3;
      uch  __cil_tmp86__3;
      unsigned long  __cil_tmp87__3;
      unsigned long  __cil_tmp88__3;
      unsigned long  __cil_tmp89__3;
      unsigned long  __cil_tmp90__3;
      uch  __cil_tmp91__3;
      unsigned long  __cil_tmp92__3;
      unsigned long  __cil_tmp93__3;
      int * __cil_tmp94__3;
      unsigned long  __cil_tmp95__3;
      unsigned long  __cil_tmp96__3;
      char * __cil_tmp97__3;
      void const   * __cil_tmp98__3;
      void const   * __cil_tmp99__3;
      size_t  __cil_tmp100__3;
      unsigned long  __cil_tmp101__3;
      unsigned long  __cil_tmp102__3;
      char * __cil_tmp103__3;
      void const   * __cil_tmp104__3;
      void const   * __cil_tmp105__3;
      size_t  __cil_tmp106__3;
      unsigned long  __cil_tmp107__3;
      unsigned long  __cil_tmp108__3;
      uch  __cil_tmp109__3;
      int * __cil_tmp110__3;
      int * __cil_tmp111__3;
      int  __cil_tmp112__3;
      FILE * __restrict   __cil_tmp113__3;
      char const   * __restrict   __cil_tmp114__3;
      unsigned long  __cil_tmp115__3;
      unsigned long  __cil_tmp116__3;
      char * __cil_tmp117__3;
      int * __cil_tmp118__3;
      int  __cil_tmp119__3;
      unsigned long  __cil_tmp120__3;
      unsigned long  __cil_tmp121__3;
      uch  __cil_tmp122__3;
      int  __cil_tmp123__3;
      int  __cil_tmp124__3;
      FILE * __restrict   __cil_tmp125__3;
      char const   * __restrict   __cil_tmp126__3;
      unsigned long  __cil_tmp127__3;
      unsigned long  __cil_tmp128__3;
      char * __cil_tmp129__3;
      int  __cil_tmp130__3;
      int  __cil_tmp131__3;
      FILE * __restrict   __cil_tmp132__3;
      char const   * __restrict   __cil_tmp133__3;
      unsigned long  __cil_tmp134__3;
      unsigned long  __cil_tmp135__3;
      char * __cil_tmp136__3;
      int  __cil_tmp137__3;
      int  __cil_tmp138__3;
      FILE * __restrict   __cil_tmp139__3;
      char const   * __restrict   __cil_tmp140__3;
      unsigned long  __cil_tmp141__3;
      unsigned long  __cil_tmp142__3;
      char * __cil_tmp143__3;
      int  __cil_tmp144__3;
      unsigned long  __cil_tmp145__3;
      unsigned long  __cil_tmp146__3;
      uch  __cil_tmp147__3;
      unsigned long  __cil_tmp148__3;
      unsigned long  __cil_tmp149__3;
      uch  __cil_tmp150__3;
      ulg  __cil_tmp151__3;
      ulg  __cil_tmp152__3;
      unsigned long  __cil_tmp153__3;
      unsigned long  __cil_tmp154__3;
      uch  __cil_tmp155__3;
      ulg  __cil_tmp156__3;
      ulg  __cil_tmp157__3;
      unsigned long  __cil_tmp158__3;
      unsigned long  __cil_tmp159__3;
      uch  __cil_tmp160__3;
      ulg  __cil_tmp161__3;
      ulg  __cil_tmp162__3;
      long * __cil_tmp163__3;
      long * __cil_tmp164__3;
      int  __cil_tmp165__3;
      int  __cil_tmp166__3;
      unsigned long  __cil_tmp167__3;
      unsigned long  __cil_tmp168__3;
      uch  __cil_tmp169__3;
      unsigned long  __cil_tmp170__3;
      unsigned long  __cil_tmp171__3;
      uch  __cil_tmp172__3;
      unsigned int  __cil_tmp173__3;
      unsigned int  __cil_tmp174__3;
      FILE * __restrict   __cil_tmp175__3;
      char const   * __restrict   __cil_tmp176__3;
      unsigned long  __cil_tmp177__3;
      unsigned long  __cil_tmp178__3;
      char * __cil_tmp179__3;
      int  __cil_tmp180__3;
      int  __cil_tmp181__3;
      unsigned long  __cil_tmp182__3;
      unsigned long  __cil_tmp183__3;
      uch  __cil_tmp184__3;
      unsigned long  __cil_tmp185__3;
      unsigned long  __cil_tmp186__3;
      uch  __cil_tmp187__3;
      unsigned int  __cil_tmp188__3;
      unsigned int  __cil_tmp189__3;
      FILE * __restrict   __cil_tmp190__3;
      char const   * __restrict   __cil_tmp191__3;
      unsigned long  __cil_tmp192__3;
      unsigned long  __cil_tmp193__3;
      char * __cil_tmp194__3;
      int  __cil_tmp195__3;
      int  __cil_tmp196__3;
      unsigned long  __cil_tmp197__3;
      unsigned long  __cil_tmp198__3;
      uch  __cil_tmp199__3;
      int  __cil_tmp200__3;
      unsigned long  __cil_tmp201__3;
      unsigned long  __cil_tmp202__3;
      char * __cil_tmp203__3;
      unsigned long  __cil_tmp204__3;
      unsigned long  __cil_tmp205__3;
      uch  __cil_tmp206__3;
      char  __cil_tmp207__3;
      int  __cil_tmp208__3;
      unsigned long  __cil_tmp209__3;
      unsigned long  __cil_tmp210__3;
      char * __cil_tmp211__3;
      char * __cil_tmp212__3;
      unsigned long  __cil_tmp213__3;
      unsigned long  __cil_tmp214__3;
      char * __cil_tmp215__3;
      int  __cil_tmp216__3;
      int  __cil_tmp217__3;
      unsigned long  __cil_tmp218__3;
      unsigned long  __cil_tmp219__3;
      uch  __cil_tmp220__3;
      unsigned long  __cil_tmp221__3;
      unsigned long  __cil_tmp222__3;
      unsigned long  __cil_tmp223__3;
      unsigned long  __cil_tmp224__3;
      unsigned long  __cil_tmp225__3;
      char * __cil_tmp226__3;
      void const   * __cil_tmp227__3;
      void const   * __cil_tmp228__3;
      size_t  __cil_tmp229__3;
      unsigned long  __cil_tmp230__3;
      unsigned long  __cil_tmp231__3;
      uch * __cil_tmp232__3;
      char * __cil_tmp233__3;
      void const   * __cil_tmp234__3;
      void const   * __cil_tmp235__3;
      size_t  __cil_tmp236__3;
      unsigned long  __cil_tmp237__3;
      unsigned long  __cil_tmp238__3;
      char * __cil_tmp239__3;
      void const   * __cil_tmp240__3;
      void const   * __cil_tmp241__3;
      size_t  __cil_tmp242__3;
      int * __cil_tmp243__3;
      unsigned long  __cil_tmp244__3;
      unsigned long  __cil_tmp245__3;
      char * __cil_tmp246__3;
      void const   * __cil_tmp247__3;
      void const   * __cil_tmp248__3;
      size_t  __cil_tmp249__3;
      int * __cil_tmp250__3;
      unsigned long  __cil_tmp251__3;
      unsigned long  __cil_tmp252__3;
      char * __cil_tmp253__3;
      void const   * __cil_tmp254__3;
      void const   * __cil_tmp255__3;
      size_t  __cil_tmp256__3;
      int * __cil_tmp257__3;
      int * __cil_tmp258__3;
      int * __cil_tmp259__3;
      int  __cil_tmp260__3;
      int * __cil_tmp261__3;
      FILE * __restrict   __cil_tmp262__3;
      char const   * __restrict   __cil_tmp263__3;
      unsigned long  __cil_tmp264__3;
      unsigned long  __cil_tmp265__3;
      char * __cil_tmp266__3;
      FILE * __restrict   __cil_tmp267__3;
      char const   * __restrict   __cil_tmp268__3;
      unsigned long  __cil_tmp269__3;
      unsigned long  __cil_tmp270__3;
      char * __cil_tmp271__3;
      uch * mem_272__3;
      char * mem_273__3;
      uch * mem_274__3;
      char * mem_275__3;
      uch * mem_276__3;
      char * mem_277__3;
      uch * mem_278__3;
      char * mem_279__3;
      uch * mem_280__3;
      uch * mem_281__3;
      uch * mem_282__3;
      uch * mem_283__3;
      uch * mem_284__3;
      uch * mem_285__3;
      uch * mem_286__3;
      uch * mem_287__3;
      uch * mem_288__3;
      uch * mem_289__3;
      uch * mem_290__3;
      uch * mem_291__3;
      uch * mem_292__3;
//line 5072 "gzip.preprocessed.c"
      //tmp___6__3 = fill_inbuf(0);
      {
//line 5072 "gzip.preprocessed.c"
        int  __arg_tmp_0__4  = 0;
//line 5072 "gzip.preprocessed.c"
        int __return__4;
//line 4052 "gzip.preprocessed.c"
        //enter fill_inbuf
        int  eof_ok__4 = __arg_tmp_0__4 ;
        int  len__4;
        int * tmp__4;
        ssize_t  tmp___0__4;
        unsigned long  __cil_tmp5__4;
        unsigned long  __cil_tmp6__4;
        uch * __cil_tmp7__4;
        char * __cil_tmp8__4;
        char * __cil_tmp9__4;
        void * __cil_tmp10__4;
        unsigned int  __cil_tmp11__4;
        size_t  __cil_tmp12__4;
        unsigned int  __cil_tmp13__4;
        ulg  __cil_tmp14__4;
        ulg  __cil_tmp15__4;
        ulg  __cil_tmp16__4;
        unsigned long  __cil_tmp17__4;
        unsigned long  __cil_tmp18__4;
        uch  __cil_tmp19__4;
        uch * mem_20__4;
//line 4056 "gzip.preprocessed.c"
        insize = 0U;
//line 4057 "gzip.preprocessed.c"
        //tmp__4 = __errno_location();
        {
//line 4057 "gzip.preprocessed.c"
          int *__return__5;
//line 4057 "gzip.preprocessed.c"
          tmp__4 = __return__5;
        }
//line 4057 "gzip.preprocessed.c"
        *tmp__4 = 0;
//line 4059 "gzip.preprocessed.c"
        __cil_tmp5__4 = (0) * (1UL);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp6__4 = ((unsigned long )(inbuf)) + (__cil_tmp5__4);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp7__4 = (uch *)(__cil_tmp6__4);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp8__4 = (char *)(__cil_tmp7__4);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp9__4 = (__cil_tmp8__4) + (insize);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp10__4 = (void *)(__cil_tmp9__4);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp11__4 = (32768U) - (insize);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp12__4 = (size_t )(__cil_tmp11__4);
//line 4059 "gzip.preprocessed.c"
        //tmp___0__4 = read(ifd, __cil_tmp10__4, __cil_tmp12__4);
        {
//line 4059 "gzip.preprocessed.c"
          int  __arg_tmp_0__5  = ifd;
//line 4059 "gzip.preprocessed.c"
          void * __arg_tmp_1__5  = __cil_tmp10__4;
//line 4059 "gzip.preprocessed.c"
          size_t  __arg_tmp_2__5  = __cil_tmp12__4;
//line 4059 "gzip.preprocessed.c"
          ssize_t __return__5;
//line 4059 "gzip.preprocessed.c"
          tmp___0__4 = __return__5;
        }
//line 4059 "gzip.preprocessed.c"
        len__4 = (int )(tmp___0__4);
//line 4061 "gzip.preprocessed.c"
        __cil_tmp13__4 = (unsigned int )(len__4);
//line 4061 "gzip.preprocessed.c"
        insize = (insize) + (__cil_tmp13__4);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp5__4 = (0) * (1UL);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp6__4 = ((unsigned long )(inbuf)) + (__cil_tmp5__4);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp7__4 = (uch *)(__cil_tmp6__4);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp8__4 = (char *)(__cil_tmp7__4);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp9__4 = (__cil_tmp8__4) + (insize);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp10__4 = (void *)(__cil_tmp9__4);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp11__4 = (32768U) - (insize);
//line 4059 "gzip.preprocessed.c"
        __cil_tmp12__4 = (size_t )(__cil_tmp11__4);
//line 4059 "gzip.preprocessed.c"
        //tmp___0__4 = read(ifd, __cil_tmp10__4, __cil_tmp12__4);
        {
//line 4059 "gzip.preprocessed.c"
          int  __arg_tmp_0__5  = ifd;
//line 4059 "gzip.preprocessed.c"
          void * __arg_tmp_1__5  = __cil_tmp10__4;
//line 4059 "gzip.preprocessed.c"
          size_t  __arg_tmp_2__5  = __cil_tmp12__4;
//line 4059 "gzip.preprocessed.c"
          ssize_t __return__5;
//line 4059 "gzip.preprocessed.c"
          tmp___0__4 = __return__5;
        }
//line 4059 "gzip.preprocessed.c"
        len__4 = (int )(tmp___0__4);
//line 4067 "gzip.preprocessed.c"
        __cil_tmp14__4 = (ulg )(insize);
//line 4067 "gzip.preprocessed.c"
        __cil_tmp15__4 = (ulg )(bytes_in);
//line 4067 "gzip.preprocessed.c"
        __cil_tmp16__4 = (__cil_tmp15__4) + (__cil_tmp14__4);
//line 4067 "gzip.preprocessed.c"
        bytes_in = (long )(__cil_tmp16__4);
//line 4068 "gzip.preprocessed.c"
        inptr = 1U;
//line 4069 "gzip.preprocessed.c"
        __cil_tmp17__4 = (0) * (1UL);
//line 4069 "gzip.preprocessed.c"
        __cil_tmp18__4 = ((unsigned long )(inbuf)) + (__cil_tmp17__4);
//line 4069 "gzip.preprocessed.c"
        mem_20__4 = (uch *)(__cil_tmp18__4);
//line 4069 "gzip.preprocessed.c"
        __cil_tmp19__4 = *mem_20__4;
//line 4069 "gzip.preprocessed.c"
        //exiting fill_inbuf
//line 4069 "gzip.preprocessed.c"
        __return__4 = (int )(__cil_tmp19__4);
//line 5072 "gzip.preprocessed.c"
        tmp___6__3 = __return__4;
      }
//line 5072 "gzip.preprocessed.c"
      tmp___7__3 = tmp___6__3;
//line 5072 "gzip.preprocessed.c"
      __cil_tmp87__3 = (0) * (1UL);
//line 5072 "gzip.preprocessed.c"
      __cil_tmp88__3 = ((unsigned long )(magic__3)) + (__cil_tmp87__3);
//line 5072 "gzip.preprocessed.c"
      mem_277__3 = (char *)(__cil_tmp88__3);
//line 5072 "gzip.preprocessed.c"
      *mem_277__3 = (char )(tmp___7__3);
//line 5073 "gzip.preprocessed.c"
      tmp___8__3 = inptr;
//line 5073 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5073 "gzip.preprocessed.c"
      __cil_tmp89__3 = (tmp___8__3) * (1UL);
//line 5073 "gzip.preprocessed.c"
      __cil_tmp90__3 = ((unsigned long )(inbuf)) + (__cil_tmp89__3);
//line 5073 "gzip.preprocessed.c"
      mem_278__3 = (uch *)(__cil_tmp90__3);
//line 5073 "gzip.preprocessed.c"
      __cil_tmp91__3 = *mem_278__3;
//line 5073 "gzip.preprocessed.c"
      tmp___10__3 = (int )(__cil_tmp91__3);
//line 5073 "gzip.preprocessed.c"
      __cil_tmp92__3 = (1) * (1UL);
//line 5073 "gzip.preprocessed.c"
      __cil_tmp93__3 = ((unsigned long )(magic__3)) + (__cil_tmp92__3);
//line 5073 "gzip.preprocessed.c"
      mem_279__3 = (char *)(__cil_tmp93__3);
//line 5073 "gzip.preprocessed.c"
      *mem_279__3 = (char )(tmp___10__3);
//line 5075 "gzip.preprocessed.c"
      __cil_tmp94__3 = &method;
//line 5075 "gzip.preprocessed.c"
      *__cil_tmp94__3 = -1;
//line 5076 "gzip.preprocessed.c"
      part_nb = (part_nb) + (1);
//line 5077 "gzip.preprocessed.c"
      header_bytes = 0L;
//line 5078 "gzip.preprocessed.c"
      last_member = 0;
//line 5079 "gzip.preprocessed.c"
      __cil_tmp95__3 = (0) * (1UL);
//line 5079 "gzip.preprocessed.c"
      __cil_tmp96__3 = ((unsigned long )(magic__3)) + (__cil_tmp95__3);
//line 5079 "gzip.preprocessed.c"
      __cil_tmp97__3 = (char *)(__cil_tmp96__3);
//line 5079 "gzip.preprocessed.c"
      __cil_tmp98__3 = (void const   *)(__cil_tmp97__3);
//line 5079 "gzip.preprocessed.c"
      __cil_tmp99__3 = (void const   *)("\031\139");
//line 5079 "gzip.preprocessed.c"
      __cil_tmp100__3 = (size_t )(2);
//line 5079 "gzip.preprocessed.c"
      //tmp___61__3 = memcmp(__cil_tmp98__3, __cil_tmp99__3, __cil_tmp100__3);
      {
//line 5079 "gzip.preprocessed.c"
        void const   * __arg_tmp_0__4  = __cil_tmp98__3;
//line 5079 "gzip.preprocessed.c"
        void const   * __arg_tmp_1__4  = __cil_tmp99__3;
//line 5079 "gzip.preprocessed.c"
        size_t  __arg_tmp_2__4  = __cil_tmp100__3;
//line 5079 "gzip.preprocessed.c"
        int __return__4;
//line 5079 "gzip.preprocessed.c"
        tmp___61__3 = __return__4;
      }
//line 5079 "gzip.preprocessed.c"
      __cil_tmp101__3 = (0) * (1UL);
//line 5079 "gzip.preprocessed.c"
      __cil_tmp102__3 = ((unsigned long )(magic__3)) + (__cil_tmp101__3);
//line 5079 "gzip.preprocessed.c"
      __cil_tmp103__3 = (char *)(__cil_tmp102__3);
//line 5079 "gzip.preprocessed.c"
      __cil_tmp104__3 = (void const   *)(__cil_tmp103__3);
//line 5079 "gzip.preprocessed.c"
      __cil_tmp105__3 = (void const   *)("\031\158");
//line 5079 "gzip.preprocessed.c"
      __cil_tmp106__3 = (size_t )(2);
//line 5079 "gzip.preprocessed.c"
      //tmp___62__3 = memcmp(__cil_tmp104__3, __cil_tmp105__3, __cil_tmp106__3);
      {
//line 5079 "gzip.preprocessed.c"
        void const   * __arg_tmp_0__4  = __cil_tmp104__3;
//line 5079 "gzip.preprocessed.c"
        void const   * __arg_tmp_1__4  = __cil_tmp105__3;
//line 5079 "gzip.preprocessed.c"
        size_t  __arg_tmp_2__4  = __cil_tmp106__3;
//line 5079 "gzip.preprocessed.c"
        int __return__4;
//line 5079 "gzip.preprocessed.c"
        tmp___62__3 = __return__4;
      }
//line 5081 "gzip.preprocessed.c"
      tmp___11__3 = inptr;
//line 5081 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5081 "gzip.preprocessed.c"
      __cil_tmp107__3 = (tmp___11__3) * (1UL);
//line 5081 "gzip.preprocessed.c"
      __cil_tmp108__3 = ((unsigned long )(inbuf)) + (__cil_tmp107__3);
//line 5081 "gzip.preprocessed.c"
      mem_280__3 = (uch *)(__cil_tmp108__3);
//line 5081 "gzip.preprocessed.c"
      __cil_tmp109__3 = *mem_280__3;
//line 5081 "gzip.preprocessed.c"
      tmp___13__3 = (int )(__cil_tmp109__3);
//line 5081 "gzip.preprocessed.c"
      __cil_tmp110__3 = &method;
//line 5081 "gzip.preprocessed.c"
      *__cil_tmp110__3 = tmp___13__3;
//line 5082 "gzip.preprocessed.c"
      __cil_tmp111__3 = &method;
//line 5082 "gzip.preprocessed.c"
      __cil_tmp112__3 = *__cil_tmp111__3;
//line 5089 "gzip.preprocessed.c"
      work = &unzip;
//line 5090 "gzip.preprocessed.c"
      tmp___14__3 = inptr;
//line 5090 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5090 "gzip.preprocessed.c"
      __cil_tmp120__3 = (tmp___14__3) * (1UL);
//line 5090 "gzip.preprocessed.c"
      __cil_tmp121__3 = ((unsigned long )(inbuf)) + (__cil_tmp120__3);
//line 5090 "gzip.preprocessed.c"
      mem_281__3 = (uch *)(__cil_tmp121__3);
//line 5090 "gzip.preprocessed.c"
      __cil_tmp122__3 = *mem_281__3;
//line 5090 "gzip.preprocessed.c"
      tmp___16__3 = (int )(__cil_tmp122__3);
//line 5090 "gzip.preprocessed.c"
      flags___0__3 = (uch )(tmp___16__3);
//line 5091 "gzip.preprocessed.c"
      __cil_tmp123__3 = (int )(flags___0__3);
//line 5091 "gzip.preprocessed.c"
      __cil_tmp124__3 = (__cil_tmp123__3) & (32);
//line 5098 "gzip.preprocessed.c"
      __cil_tmp130__3 = (int )(flags___0__3);
//line 5098 "gzip.preprocessed.c"
      __cil_tmp131__3 = (__cil_tmp130__3) & (2);
//line 5105 "gzip.preprocessed.c"
      __cil_tmp137__3 = (int )(flags___0__3);
//line 5105 "gzip.preprocessed.c"
      __cil_tmp138__3 = (__cil_tmp137__3) & (192);
//line 5112 "gzip.preprocessed.c"
      tmp___17__3 = inptr;
//line 5112 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5112 "gzip.preprocessed.c"
      __cil_tmp145__3 = (tmp___17__3) * (1UL);
//line 5112 "gzip.preprocessed.c"
      __cil_tmp146__3 = ((unsigned long )(inbuf)) + (__cil_tmp145__3);
//line 5112 "gzip.preprocessed.c"
      mem_282__3 = (uch *)(__cil_tmp146__3);
//line 5112 "gzip.preprocessed.c"
      __cil_tmp147__3 = *mem_282__3;
//line 5112 "gzip.preprocessed.c"
      tmp___19__3 = (int )(__cil_tmp147__3);
//line 5112 "gzip.preprocessed.c"
      stamp__3 = (ulg )(tmp___19__3);
//line 5113 "gzip.preprocessed.c"
      tmp___20__3 = inptr;
//line 5113 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5113 "gzip.preprocessed.c"
      __cil_tmp148__3 = (tmp___20__3) * (1UL);
//line 5113 "gzip.preprocessed.c"
      __cil_tmp149__3 = ((unsigned long )(inbuf)) + (__cil_tmp148__3);
//line 5113 "gzip.preprocessed.c"
      mem_283__3 = (uch *)(__cil_tmp149__3);
//line 5113 "gzip.preprocessed.c"
      __cil_tmp150__3 = *mem_283__3;
//line 5113 "gzip.preprocessed.c"
      tmp___22__3 = (int )(__cil_tmp150__3);
//line 5113 "gzip.preprocessed.c"
      __cil_tmp151__3 = (ulg )(tmp___22__3);
//line 5113 "gzip.preprocessed.c"
      __cil_tmp152__3 = (__cil_tmp151__3) << (8);
//line 5113 "gzip.preprocessed.c"
      stamp__3 = (stamp__3) | (__cil_tmp152__3);
//line 5114 "gzip.preprocessed.c"
      tmp___23__3 = inptr;
//line 5114 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5114 "gzip.preprocessed.c"
      __cil_tmp153__3 = (tmp___23__3) * (1UL);
//line 5114 "gzip.preprocessed.c"
      __cil_tmp154__3 = ((unsigned long )(inbuf)) + (__cil_tmp153__3);
//line 5114 "gzip.preprocessed.c"
      mem_284__3 = (uch *)(__cil_tmp154__3);
//line 5114 "gzip.preprocessed.c"
      __cil_tmp155__3 = *mem_284__3;
//line 5114 "gzip.preprocessed.c"
      tmp___25__3 = (int )(__cil_tmp155__3);
//line 5114 "gzip.preprocessed.c"
      __cil_tmp156__3 = (ulg )(tmp___25__3);
//line 5114 "gzip.preprocessed.c"
      __cil_tmp157__3 = (__cil_tmp156__3) << (16);
//line 5114 "gzip.preprocessed.c"
      stamp__3 = (stamp__3) | (__cil_tmp157__3);
//line 5115 "gzip.preprocessed.c"
      tmp___26__3 = inptr;
//line 5115 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5115 "gzip.preprocessed.c"
      __cil_tmp158__3 = (tmp___26__3) * (1UL);
//line 5115 "gzip.preprocessed.c"
      __cil_tmp159__3 = ((unsigned long )(inbuf)) + (__cil_tmp158__3);
//line 5115 "gzip.preprocessed.c"
      mem_285__3 = (uch *)(__cil_tmp159__3);
//line 5115 "gzip.preprocessed.c"
      __cil_tmp160__3 = *mem_285__3;
//line 5115 "gzip.preprocessed.c"
      tmp___28__3 = (int )(__cil_tmp160__3);
//line 5115 "gzip.preprocessed.c"
      __cil_tmp161__3 = (ulg )(tmp___28__3);
//line 5115 "gzip.preprocessed.c"
      __cil_tmp162__3 = (__cil_tmp161__3) << (24);
//line 5115 "gzip.preprocessed.c"
      stamp__3 = (stamp__3) | (__cil_tmp162__3);
//line 5117 "gzip.preprocessed.c"
      __cil_tmp164__3 = &time_stamp;
//line 5117 "gzip.preprocessed.c"
      *__cil_tmp164__3 = 0L;
//line 5118 "gzip.preprocessed.c"
      tmp___29__3 = inptr;
//line 5118 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5119 "gzip.preprocessed.c"
      tmp___30__3 = inptr;
//line 5119 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5120 "gzip.preprocessed.c"
      __cil_tmp165__3 = (int )(flags___0__3);
//line 5120 "gzip.preprocessed.c"
      __cil_tmp166__3 = (__cil_tmp165__3) & (2);
//line 5128 "gzip.preprocessed.c"
      __cil_tmp180__3 = (int )(flags___0__3);
//line 5128 "gzip.preprocessed.c"
      __cil_tmp181__3 = (__cil_tmp180__3) & (4);
//line 5129 "gzip.preprocessed.c"
      tmp___37__3 = inptr;
//line 5129 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5129 "gzip.preprocessed.c"
      __cil_tmp182__3 = (tmp___37__3) * (1UL);
//line 5129 "gzip.preprocessed.c"
      __cil_tmp183__3 = ((unsigned long )(inbuf)) + (__cil_tmp182__3);
//line 5129 "gzip.preprocessed.c"
      mem_288__3 = (uch *)(__cil_tmp183__3);
//line 5129 "gzip.preprocessed.c"
      __cil_tmp184__3 = *mem_288__3;
//line 5129 "gzip.preprocessed.c"
      tmp___39__3 = (int )(__cil_tmp184__3);
//line 5129 "gzip.preprocessed.c"
      len__3 = (unsigned int )(tmp___39__3);
//line 5130 "gzip.preprocessed.c"
      tmp___40__3 = inptr;
//line 5130 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5130 "gzip.preprocessed.c"
      __cil_tmp185__3 = (tmp___40__3) * (1UL);
//line 5130 "gzip.preprocessed.c"
      __cil_tmp186__3 = ((unsigned long )(inbuf)) + (__cil_tmp185__3);
//line 5130 "gzip.preprocessed.c"
      mem_289__3 = (uch *)(__cil_tmp186__3);
//line 5130 "gzip.preprocessed.c"
      __cil_tmp187__3 = *mem_289__3;
//line 5130 "gzip.preprocessed.c"
      tmp___42__3 = (int )(__cil_tmp187__3);
//line 5130 "gzip.preprocessed.c"
      __cil_tmp188__3 = (unsigned int )(tmp___42__3);
//line 5130 "gzip.preprocessed.c"
      __cil_tmp189__3 = (__cil_tmp188__3) << (8);
//line 5130 "gzip.preprocessed.c"
      len__3 = (len__3) | (__cil_tmp189__3);
//line 5135 "gzip.preprocessed.c"
      tmp___44__3 = len__3;
//line 5135 "gzip.preprocessed.c"
      len__3 = (len__3) - (1U);
//line 5135 "gzip.preprocessed.c"
      tmp___43__3 = inptr;
//line 5135 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5135 "gzip.preprocessed.c"
      tmp___44__3 = len__3;
//line 5135 "gzip.preprocessed.c"
      len__3 = (len__3) - (1U);
//line 5135 "gzip.preprocessed.c"
      tmp___43__3 = inptr;
//line 5135 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
//line 5135 "gzip.preprocessed.c"
      tmp___44__3 = len__3;
//line 5135 "gzip.preprocessed.c"
      len__3 = (len__3) - (1U);
//line 5137 "gzip.preprocessed.c"
      __cil_tmp195__3 = (int )(flags___0__3);
//line 5137 "gzip.preprocessed.c"
      __cil_tmp196__3 = (__cil_tmp195__3) & (8);
//line 5157 "gzip.preprocessed.c"
      __cil_tmp216__3 = (int )(flags___0__3);
//line 5157 "gzip.preprocessed.c"
      __cil_tmp217__3 = (__cil_tmp216__3) & (16);
//line 5161 "gzip.preprocessed.c"
      __cil_tmp221__3 = (2UL) * (8UL);
//line 5161 "gzip.preprocessed.c"
      __cil_tmp222__3 = (unsigned long )(inptr);
//line 5161 "gzip.preprocessed.c"
      __cil_tmp223__3 = (__cil_tmp222__3) + (__cil_tmp221__3);
//line 5161 "gzip.preprocessed.c"
      header_bytes = (long )(__cil_tmp223__3);
//line 5186 "gzip.preprocessed.c"
      __cil_tmp259__3 = &method;
//line 5186 "gzip.preprocessed.c"
      __cil_tmp260__3 = *__cil_tmp259__3;
//line 5186 "gzip.preprocessed.c"
      __cil_tmp261__3 = &method;
//line 5186 "gzip.preprocessed.c"
      //exiting get_method
//line 5186 "gzip.preprocessed.c"
      __return__3 = *__cil_tmp261__3;
//line 4791 "gzip.preprocessed.c"
      *__cil_tmp30__2 = __return__3;
    }
//line 4792 "gzip.preprocessed.c"
    __cil_tmp31__2 = &method;
//line 4792 "gzip.preprocessed.c"
    __cil_tmp32__2 = *__cil_tmp31__2;
//line 4801 "gzip.preprocessed.c"
    //tmp___8__2 = fileno(stdout);
    {
//line 4801 "gzip.preprocessed.c"
      struct _IO_FILE * __arg_tmp_0__3  = stdout;
//line 4801 "gzip.preprocessed.c"
      int __return__3;
//line 4801 "gzip.preprocessed.c"
      tmp___8__2 = __return__3;
    }
//line 4801 "gzip.preprocessed.c"
    //tmp___9__2 = fileno(stdin);
    {
//line 4801 "gzip.preprocessed.c"
      struct _IO_FILE * __arg_tmp_0__3  = stdin;
//line 4801 "gzip.preprocessed.c"
      int __return__3;
//line 4801 "gzip.preprocessed.c"
      tmp___9__2 = __return__3;
    }
//line 4801 "gzip.preprocessed.c"
    //tmp___10__2 = *work(tmp___9__2, tmp___8__2);
    {
//line 4801 "gzip.preprocessed.c"
      int  __arg_tmp_0__3  = tmp___9__2;
//line 4801 "gzip.preprocessed.c"
      int  __arg_tmp_1__3  = tmp___8__2;
//line 4801 "gzip.preprocessed.c"
      int __return__3;
//line 3944 "gzip.preprocessed.c"
      //enter unzip
      int  in__3 = __arg_tmp_0__3 ;
      int  out__3 = __arg_tmp_1__3 ;
      ulg  orig_crc__3;
      ulg  orig_len___0__3;
      int  n__3;
      uch  buf__3[16];
      int  res__3;
      int  tmp__3;
      ulg  n___0__3;
      int  tmp___0__3;
      uch  c__3;
      unsigned int  tmp___1__3;
      int  tmp___2__3;
      int  tmp___3__3;
      unsigned int  tmp___4__3;
      ulg  tmp___5__3;
      unsigned int  tmp___6__3;
      int  tmp___7__3;
      int  tmp___8__3;
      unsigned int  tmp___9__3;
      int  tmp___10__3;
      int  tmp___11__3;
      ulg  tmp___12__3;
      void * __cil_tmp24__3;
      uch * __cil_tmp25__3;
      unsigned long  __cil_tmp26__3;
      unsigned long  __cil_tmp27__3;
      uch * __cil_tmp28__3;
      uch * __cil_tmp29__3;
      uch * __cil_tmp30__3;
      uch * __cil_tmp31__3;
      uch  __cil_tmp32__3;
      ush  __cil_tmp33__3;
      int  __cil_tmp34__3;
      int  __cil_tmp35__3;
      unsigned long  __cil_tmp36__3;
      unsigned long  __cil_tmp37__3;
      uch * __cil_tmp38__3;
      uch * __cil_tmp39__3;
      uch * __cil_tmp40__3;
      uch * __cil_tmp41__3;
      uch  __cil_tmp42__3;
      ush  __cil_tmp43__3;
      int  __cil_tmp44__3;
      int  __cil_tmp45__3;
      ulg  __cil_tmp46__3;
      ulg  __cil_tmp47__3;
      unsigned long  __cil_tmp48__3;
      unsigned long  __cil_tmp49__3;
      uch * __cil_tmp50__3;
      uch * __cil_tmp51__3;
      uch * __cil_tmp52__3;
      uch  __cil_tmp53__3;
      ush  __cil_tmp54__3;
      int  __cil_tmp55__3;
      int  __cil_tmp56__3;
      unsigned long  __cil_tmp57__3;
      unsigned long  __cil_tmp58__3;
      uch * __cil_tmp59__3;
      uch * __cil_tmp60__3;
      uch * __cil_tmp61__3;
      uch  __cil_tmp62__3;
      ush  __cil_tmp63__3;
      int  __cil_tmp64__3;
      int  __cil_tmp65__3;
      ulg  __cil_tmp66__3;
      unsigned long  __cil_tmp67__3;
      unsigned long  __cil_tmp68__3;
      uch * __cil_tmp69__3;
      uch * __cil_tmp70__3;
      uch * __cil_tmp71__3;
      uch * __cil_tmp72__3;
      uch  __cil_tmp73__3;
      ush  __cil_tmp74__3;
      int  __cil_tmp75__3;
      int  __cil_tmp76__3;
      unsigned long  __cil_tmp77__3;
      unsigned long  __cil_tmp78__3;
      uch * __cil_tmp79__3;
      uch * __cil_tmp80__3;
      uch * __cil_tmp81__3;
      uch * __cil_tmp82__3;
      uch  __cil_tmp83__3;
      ush  __cil_tmp84__3;
      int  __cil_tmp85__3;
      int  __cil_tmp86__3;
      ulg  __cil_tmp87__3;
      ulg  __cil_tmp88__3;
      unsigned long  __cil_tmp89__3;
      unsigned long  __cil_tmp90__3;
      uch * __cil_tmp91__3;
      uch * __cil_tmp92__3;
      uch * __cil_tmp93__3;
      uch  __cil_tmp94__3;
      ush  __cil_tmp95__3;
      int  __cil_tmp96__3;
      int  __cil_tmp97__3;
      unsigned long  __cil_tmp98__3;
      unsigned long  __cil_tmp99__3;
      uch * __cil_tmp100__3;
      uch * __cil_tmp101__3;
      uch * __cil_tmp102__3;
      uch  __cil_tmp103__3;
      ush  __cil_tmp104__3;
      int  __cil_tmp105__3;
      int  __cil_tmp106__3;
      ulg  __cil_tmp107__3;
      int * __cil_tmp108__3;
      int  __cil_tmp109__3;
      char * __cil_tmp110__3;
      char * __cil_tmp111__3;
      int * __cil_tmp112__3;
      int  __cil_tmp113__3;
      unsigned long  __cil_tmp114__3;
      unsigned long  __cil_tmp115__3;
      uch * __cil_tmp116__3;
      uch * __cil_tmp117__3;
      uch * __cil_tmp118__3;
      uch * __cil_tmp119__3;
      uch  __cil_tmp120__3;
      ush  __cil_tmp121__3;
      int  __cil_tmp122__3;
      int  __cil_tmp123__3;
      unsigned long  __cil_tmp124__3;
      unsigned long  __cil_tmp125__3;
      uch * __cil_tmp126__3;
      uch * __cil_tmp127__3;
      uch * __cil_tmp128__3;
      uch * __cil_tmp129__3;
      uch  __cil_tmp130__3;
      ush  __cil_tmp131__3;
      int  __cil_tmp132__3;
      int  __cil_tmp133__3;
      ulg  __cil_tmp134__3;
      ulg  __cil_tmp135__3;
      unsigned long  __cil_tmp136__3;
      unsigned long  __cil_tmp137__3;
      uch * __cil_tmp138__3;
      uch * __cil_tmp139__3;
      uch * __cil_tmp140__3;
      uch  __cil_tmp141__3;
      ush  __cil_tmp142__3;
      int  __cil_tmp143__3;
      int  __cil_tmp144__3;
      unsigned long  __cil_tmp145__3;
      unsigned long  __cil_tmp146__3;
      uch * __cil_tmp147__3;
      uch * __cil_tmp148__3;
      uch * __cil_tmp149__3;
      uch  __cil_tmp150__3;
      ush  __cil_tmp151__3;
      int  __cil_tmp152__3;
      int  __cil_tmp153__3;
      ulg  __cil_tmp154__3;
      unsigned long  __cil_tmp155__3;
      unsigned long  __cil_tmp156__3;
      unsigned long  __cil_tmp157__3;
      uch * __cil_tmp158__3;
      uch * __cil_tmp159__3;
      uch * __cil_tmp160__3;
      uch * __cil_tmp161__3;
      uch  __cil_tmp162__3;
      ush  __cil_tmp163__3;
      int  __cil_tmp164__3;
      int  __cil_tmp165__3;
      unsigned long  __cil_tmp166__3;
      unsigned long  __cil_tmp167__3;
      uch * __cil_tmp168__3;
      uch * __cil_tmp169__3;
      uch * __cil_tmp170__3;
      uch * __cil_tmp171__3;
      uch  __cil_tmp172__3;
      ush  __cil_tmp173__3;
      int  __cil_tmp174__3;
      int  __cil_tmp175__3;
      ulg  __cil_tmp176__3;
      ulg  __cil_tmp177__3;
      unsigned long  __cil_tmp178__3;
      unsigned long  __cil_tmp179__3;
      uch * __cil_tmp180__3;
      uch * __cil_tmp181__3;
      uch * __cil_tmp182__3;
      uch  __cil_tmp183__3;
      ush  __cil_tmp184__3;
      int  __cil_tmp185__3;
      int  __cil_tmp186__3;
      unsigned long  __cil_tmp187__3;
      unsigned long  __cil_tmp188__3;
      uch * __cil_tmp189__3;
      uch * __cil_tmp190__3;
      uch * __cil_tmp191__3;
      uch  __cil_tmp192__3;
      ush  __cil_tmp193__3;
      int  __cil_tmp194__3;
      int  __cil_tmp195__3;
      ulg  __cil_tmp196__3;
      unsigned long  __cil_tmp197__3;
      unsigned long  __cil_tmp198__3;
      FILE * __restrict   __cil_tmp199__3;
      char const   * __restrict   __cil_tmp200__3;
      unsigned long  __cil_tmp201__3;
      unsigned long  __cil_tmp202__3;
      uch * __cil_tmp203__3;
      uch * __cil_tmp204__3;
      uch * __cil_tmp205__3;
      uch * __cil_tmp206__3;
      uch  __cil_tmp207__3;
      ush  __cil_tmp208__3;
      int  __cil_tmp209__3;
      int  __cil_tmp210__3;
      unsigned long  __cil_tmp211__3;
      unsigned long  __cil_tmp212__3;
      uch * __cil_tmp213__3;
      uch * __cil_tmp214__3;
      uch * __cil_tmp215__3;
      uch * __cil_tmp216__3;
      uch  __cil_tmp217__3;
      ush  __cil_tmp218__3;
      int  __cil_tmp219__3;
      int  __cil_tmp220__3;
      ulg  __cil_tmp221__3;
      ulg  __cil_tmp222__3;
      unsigned long  __cil_tmp223__3;
      unsigned long  __cil_tmp224__3;
      uch * __cil_tmp225__3;
      uch * __cil_tmp226__3;
      uch * __cil_tmp227__3;
      uch  __cil_tmp228__3;
      ush  __cil_tmp229__3;
      int  __cil_tmp230__3;
      int  __cil_tmp231__3;
      unsigned long  __cil_tmp232__3;
      unsigned long  __cil_tmp233__3;
      uch * __cil_tmp234__3;
      uch * __cil_tmp235__3;
      uch * __cil_tmp236__3;
      uch  __cil_tmp237__3;
      ush  __cil_tmp238__3;
      int  __cil_tmp239__3;
      int  __cil_tmp240__3;
      ulg  __cil_tmp241__3;
      unsigned long  __cil_tmp242__3;
      char * __cil_tmp243__3;
      unsigned long  __cil_tmp244__3;
      unsigned long  __cil_tmp245__3;
      uch  __cil_tmp246__3;
      unsigned long  __cil_tmp247__3;
      unsigned long  __cil_tmp248__3;
      char * __cil_tmp249__3;
      char * __cil_tmp250__3;
      unsigned long  __cil_tmp251__3;
      unsigned long  __cil_tmp252__3;
      uch  __cil_tmp253__3;
      unsigned long  __cil_tmp254__3;
      unsigned long  __cil_tmp255__3;
      unsigned long  __cil_tmp256__3;
      unsigned long  __cil_tmp257__3;
      uch * __cil_tmp258__3;
      uch * __cil_tmp259__3;
      uch * __cil_tmp260__3;
      uch  __cil_tmp261__3;
      ush  __cil_tmp262__3;
      int  __cil_tmp263__3;
      int  __cil_tmp264__3;
      unsigned long  __cil_tmp265__3;
      unsigned long  __cil_tmp266__3;
      uch * __cil_tmp267__3;
      uch * __cil_tmp268__3;
      uch * __cil_tmp269__3;
      uch  __cil_tmp270__3;
      ush  __cil_tmp271__3;
      int  __cil_tmp272__3;
      int  __cil_tmp273__3;
      ulg  __cil_tmp274__3;
      ulg  __cil_tmp275__3;
      unsigned long  __cil_tmp276__3;
      unsigned long  __cil_tmp277__3;
      uch  __cil_tmp278__3;
      ush  __cil_tmp279__3;
      int  __cil_tmp280__3;
      int  __cil_tmp281__3;
      unsigned long  __cil_tmp282__3;
      unsigned long  __cil_tmp283__3;
      uch  __cil_tmp284__3;
      ush  __cil_tmp285__3;
      int  __cil_tmp286__3;
      int  __cil_tmp287__3;
      ulg  __cil_tmp288__3;
      unsigned long  __cil_tmp289__3;
      unsigned long  __cil_tmp290__3;
      uch * __cil_tmp291__3;
      uch * __cil_tmp292__3;
      uch * __cil_tmp293__3;
      uch * __cil_tmp294__3;
      uch  __cil_tmp295__3;
      ush  __cil_tmp296__3;
      int  __cil_tmp297__3;
      int  __cil_tmp298__3;
      unsigned long  __cil_tmp299__3;
      unsigned long  __cil_tmp300__3;
      uch * __cil_tmp301__3;
      uch * __cil_tmp302__3;
      uch * __cil_tmp303__3;
      uch * __cil_tmp304__3;
      uch  __cil_tmp305__3;
      ush  __cil_tmp306__3;
      int  __cil_tmp307__3;
      int  __cil_tmp308__3;
      ulg  __cil_tmp309__3;
      ulg  __cil_tmp310__3;
      unsigned long  __cil_tmp311__3;
      unsigned long  __cil_tmp312__3;
      uch * __cil_tmp313__3;
      uch * __cil_tmp314__3;
      uch * __cil_tmp315__3;
      uch  __cil_tmp316__3;
      ush  __cil_tmp317__3;
      int  __cil_tmp318__3;
      int  __cil_tmp319__3;
      unsigned long  __cil_tmp320__3;
      unsigned long  __cil_tmp321__3;
      uch * __cil_tmp322__3;
      uch * __cil_tmp323__3;
      uch * __cil_tmp324__3;
      uch  __cil_tmp325__3;
      ush  __cil_tmp326__3;
      int  __cil_tmp327__3;
      int  __cil_tmp328__3;
      ulg  __cil_tmp329__3;
      unsigned long  __cil_tmp330__3;
      unsigned long  __cil_tmp331__3;
      uch  __cil_tmp332__3;
      unsigned long  __cil_tmp333__3;
      unsigned long  __cil_tmp334__3;
      unsigned long  __cil_tmp335__3;
      unsigned long  __cil_tmp336__3;
      uch * __cil_tmp337__3;
      uch * __cil_tmp338__3;
      uch * __cil_tmp339__3;
      uch * __cil_tmp340__3;
      uch  __cil_tmp341__3;
      ush  __cil_tmp342__3;
      int  __cil_tmp343__3;
      int  __cil_tmp344__3;
      unsigned long  __cil_tmp345__3;
      unsigned long  __cil_tmp346__3;
      uch * __cil_tmp347__3;
      uch * __cil_tmp348__3;
      uch * __cil_tmp349__3;
      uch * __cil_tmp350__3;
      uch  __cil_tmp351__3;
      ush  __cil_tmp352__3;
      int  __cil_tmp353__3;
      int  __cil_tmp354__3;
      ulg  __cil_tmp355__3;
      ulg  __cil_tmp356__3;
      unsigned long  __cil_tmp357__3;
      unsigned long  __cil_tmp358__3;
      uch * __cil_tmp359__3;
      uch * __cil_tmp360__3;
      uch * __cil_tmp361__3;
      uch  __cil_tmp362__3;
      ush  __cil_tmp363__3;
      int  __cil_tmp364__3;
      int  __cil_tmp365__3;
      unsigned long  __cil_tmp366__3;
      unsigned long  __cil_tmp367__3;
      uch * __cil_tmp368__3;
      uch * __cil_tmp369__3;
      uch * __cil_tmp370__3;
      uch  __cil_tmp371__3;
      ush  __cil_tmp372__3;
      int  __cil_tmp373__3;
      int  __cil_tmp374__3;
      ulg  __cil_tmp375__3;
      unsigned long  __cil_tmp376__3;
      unsigned long  __cil_tmp377__3;
      uch * __cil_tmp378__3;
      uch * __cil_tmp379__3;
      uch * __cil_tmp380__3;
      uch * __cil_tmp381__3;
      uch  __cil_tmp382__3;
      ush  __cil_tmp383__3;
      int  __cil_tmp384__3;
      int  __cil_tmp385__3;
      unsigned long  __cil_tmp386__3;
      unsigned long  __cil_tmp387__3;
      uch * __cil_tmp388__3;
      uch * __cil_tmp389__3;
      uch * __cil_tmp390__3;
      uch * __cil_tmp391__3;
      uch  __cil_tmp392__3;
      ush  __cil_tmp393__3;
      int  __cil_tmp394__3;
      int  __cil_tmp395__3;
      ulg  __cil_tmp396__3;
      ulg  __cil_tmp397__3;
      unsigned long  __cil_tmp398__3;
      unsigned long  __cil_tmp399__3;
      uch * __cil_tmp400__3;
      uch * __cil_tmp401__3;
      uch * __cil_tmp402__3;
      uch  __cil_tmp403__3;
      ush  __cil_tmp404__3;
      int  __cil_tmp405__3;
      int  __cil_tmp406__3;
      unsigned long  __cil_tmp407__3;
      unsigned long  __cil_tmp408__3;
      uch * __cil_tmp409__3;
      uch * __cil_tmp410__3;
      uch * __cil_tmp411__3;
      uch  __cil_tmp412__3;
      ush  __cil_tmp413__3;
      int  __cil_tmp414__3;
      int  __cil_tmp415__3;
      ulg  __cil_tmp416__3;
      unsigned long  __cil_tmp417__3;
      unsigned long  __cil_tmp418__3;
      uch * __cil_tmp419__3;
      char * __cil_tmp420__3;
      ulg  __cil_tmp421__3;
      char * __cil_tmp422__3;
      unsigned int  __cil_tmp423__3;
      unsigned long  __cil_tmp424__3;
      unsigned long  __cil_tmp425__3;
      uch * __cil_tmp426__3;
      uch * __cil_tmp427__3;
      uch * __cil_tmp428__3;
      uch * __cil_tmp429__3;
      uch  __cil_tmp430__3;
      ush  __cil_tmp431__3;
      int  __cil_tmp432__3;
      int  __cil_tmp433__3;
      unsigned long  __cil_tmp434__3;
      unsigned long  __cil_tmp435__3;
      uch * __cil_tmp436__3;
      uch * __cil_tmp437__3;
      uch * __cil_tmp438__3;
      uch * __cil_tmp439__3;
      uch  __cil_tmp440__3;
      ush  __cil_tmp441__3;
      int  __cil_tmp442__3;
      int  __cil_tmp443__3;
      ulg  __cil_tmp444__3;
      ulg  __cil_tmp445__3;
      unsigned long  __cil_tmp446__3;
      unsigned long  __cil_tmp447__3;
      uch * __cil_tmp448__3;
      uch * __cil_tmp449__3;
      uch * __cil_tmp450__3;
      uch  __cil_tmp451__3;
      ush  __cil_tmp452__3;
      int  __cil_tmp453__3;
      int  __cil_tmp454__3;
      unsigned long  __cil_tmp455__3;
      unsigned long  __cil_tmp456__3;
      uch * __cil_tmp457__3;
      uch * __cil_tmp458__3;
      uch * __cil_tmp459__3;
      uch  __cil_tmp460__3;
      ush  __cil_tmp461__3;
      int  __cil_tmp462__3;
      int  __cil_tmp463__3;
      ulg  __cil_tmp464__3;
      unsigned long  __cil_tmp465__3;
      FILE * __restrict   __cil_tmp466__3;
      char const   * __restrict   __cil_tmp467__3;
      unsigned long  __cil_tmp468__3;
      unsigned long  __cil_tmp469__3;
      char * __cil_tmp470__3;
      FILE * __restrict   __cil_tmp471__3;
      char const   * __restrict   __cil_tmp472__3;
      unsigned long  __cil_tmp473__3;
      unsigned long  __cil_tmp474__3;
      char * __cil_tmp475__3;
      uch * mem_476__3;
      uch * mem_477__3;
      uch * mem_478__3;
      uch * mem_479__3;
      uch * mem_480__3;
      uch * mem_481__3;
      uch * mem_482__3;
      uch * mem_483__3;
//line 3947 "gzip.preprocessed.c"
      orig_crc__3 = (ulg )(0);
//line 3948 "gzip.preprocessed.c"
      orig_len___0__3 = (ulg )(0);
//line 3951 "gzip.preprocessed.c"
      ifd = in__3;
//line 3952 "gzip.preprocessed.c"
      ofd = out__3;
//line 3953 "gzip.preprocessed.c"
      __cil_tmp24__3 = (void *)(0);
//line 3953 "gzip.preprocessed.c"
      __cil_tmp25__3 = (uch *)(__cil_tmp24__3);
//line 3953 "gzip.preprocessed.c"
      //updcrc(__cil_tmp25__3, 0U);
      {
//line 3953 "gzip.preprocessed.c"
        uch * __arg_tmp_0__4  = __cil_tmp25__3;
//line 3953 "gzip.preprocessed.c"
        unsigned int  __arg_tmp_1__4  = 0U;
//line 4029 "gzip.preprocessed.c"
        //enter updcrc
        uch * s__4 = __arg_tmp_0__4 ;
        unsigned int  n__4 = __arg_tmp_1__4 ;
        ulg  c__4;
        uch * tmp__4;
        void * __cil_tmp5__4;
        unsigned long  __cil_tmp6__4;
        unsigned long  __cil_tmp7__4;
        ulg  __cil_tmp8__4;
        uch  __cil_tmp9__4;
        int  __cil_tmp10__4;
        int  __cil_tmp11__4;
        int  __cil_tmp12__4;
        int  __cil_tmp13__4;
        unsigned long  __cil_tmp14__4;
        unsigned long  __cil_tmp15__4;
        ulg  __cil_tmp16__4;
        ulg * mem_17__4;
//line 4035 "gzip.preprocessed.c"
        __cil_tmp5__4 = (void *)(0);
//line 4035 "gzip.preprocessed.c"
        __cil_tmp6__4 = (unsigned long )(__cil_tmp5__4);
//line 4035 "gzip.preprocessed.c"
        __cil_tmp7__4 = (unsigned long )(s__4);
//line 4036 "gzip.preprocessed.c"
        c__4 = (ulg )(4294967295L);
//line 4043 "gzip.preprocessed.c"
        //crc___0 = c__4; //DSN REMOVED its a static variable
//line 4044 "gzip.preprocessed.c"
        //exiting updcrc
//line 4044 "gzip.preprocessed.c"
        ulg __return__4 = (c__4) ^ (4294967295UL);//DSN added
      }
//line 3958 "gzip.preprocessed.c"
      __cil_tmp108__3 = &method;
//line 3958 "gzip.preprocessed.c"
      __cil_tmp109__3 = *__cil_tmp108__3;
//line 3959 "gzip.preprocessed.c"
      //tmp__3 = inflate();
      {
//line 3959 "gzip.preprocessed.c"
        int __return__4;
//line 2305 "gzip.preprocessed.c"
        //enter inflate
        int  e__4;
        int  r__4;
        unsigned int  h__4;
        int * __cil_tmp4__4;
        int  __cil_tmp5__4;
//line 2310 "gzip.preprocessed.c"
        outcnt = 0U;
//line 2311 "gzip.preprocessed.c"
        bk = 0U;
//line 2312 "gzip.preprocessed.c"
        bb = (ulg )(0);
//line 2313 "gzip.preprocessed.c"
        h__4 = 0U;
//line 2315 "gzip.preprocessed.c"
        hufts = 0U;
//line 2316 "gzip.preprocessed.c"
        //r__4 = inflate_block(&e__4);
        {
//line 2316 "gzip.preprocessed.c"
          int * __arg_tmp_0__5  = &e__4;//DSN fixed
//line 2316 "gzip.preprocessed.c"
          int __return__5;
//line 2281 "gzip.preprocessed.c"
          //enter inflate_block
          int * e__5 = __arg_tmp_0__5 ;
          unsigned int  t__5;
          ulg  b__5;
          unsigned int  k__5;
          unsigned int  tmp__5;
          int  tmp___0__5;
          int  tmp___1__5;
          unsigned int  tmp___2__5;
          int  tmp___3__5;
          int  tmp___4__5;
          int  tmp___5__5;
          int  tmp___6__5;
          int  tmp___7__5;
          unsigned long  __cil_tmp14__5;
          unsigned long  __cil_tmp15__5;
          uch  __cil_tmp16__5;
          uch  __cil_tmp17__5;
          ulg  __cil_tmp18__5;
          ulg  __cil_tmp19__5;
          int  __cil_tmp20__5;
          unsigned long  __cil_tmp21__5;
          unsigned long  __cil_tmp22__5;
          uch  __cil_tmp23__5;
          uch  __cil_tmp24__5;
          ulg  __cil_tmp25__5;
          ulg  __cil_tmp26__5;
          unsigned int  __cil_tmp27__5;
          uch * mem_28__5;
          uch * mem_29__5;
//line 2287 "gzip.preprocessed.c"
          b__5 = bb;
//line 2288 "gzip.preprocessed.c"
          k__5 = bk;
//line 2289 "gzip.preprocessed.c"
          tmp__5 = inptr;
//line 2289 "gzip.preprocessed.c"
          inptr = (inptr) + (1U);
//line 2289 "gzip.preprocessed.c"
          __cil_tmp14__5 = (tmp__5) * (1UL);
//line 2289 "gzip.preprocessed.c"
          __cil_tmp15__5 = ((unsigned long )(inbuf)) + (__cil_tmp14__5);
//line 2289 "gzip.preprocessed.c"
          mem_28__5 = (uch *)(__cil_tmp15__5);
//line 2289 "gzip.preprocessed.c"
          __cil_tmp16__5 = *mem_28__5;
//line 2289 "gzip.preprocessed.c"
          tmp___1__5 = (int )(__cil_tmp16__5);
//line 2289 "gzip.preprocessed.c"
          __cil_tmp17__5 = (uch )(tmp___1__5);
//line 2289 "gzip.preprocessed.c"
          __cil_tmp18__5 = (ulg )(__cil_tmp17__5);
//line 2289 "gzip.preprocessed.c"
          __cil_tmp19__5 = (__cil_tmp18__5) << (k__5);
//line 2289 "gzip.preprocessed.c"
          b__5 = (b__5) | (__cil_tmp19__5);
//line 2289 "gzip.preprocessed.c"
          k__5 = (k__5) + (8U);
//line 2290 "gzip.preprocessed.c"
          __cil_tmp20__5 = (int )(b__5);
//line 2290 "gzip.preprocessed.c"
          *e__5 = (__cil_tmp20__5) & (1);
//line 2291 "gzip.preprocessed.c"
          b__5 = (b__5) >> (1);
//line 2291 "gzip.preprocessed.c"
          k__5 = (k__5) - (1U);
//line 2293 "gzip.preprocessed.c"
          __cil_tmp27__5 = (unsigned int )(b__5);
//line 2293 "gzip.preprocessed.c"
          t__5 = (__cil_tmp27__5) & (3U);
//line 2294 "gzip.preprocessed.c"
          b__5 = (b__5) >> (2);
//line 2294 "gzip.preprocessed.c"
          k__5 = (k__5) - (2U);
//line 2295 "gzip.preprocessed.c"
          bb = b__5;
//line 2296 "gzip.preprocessed.c"
          bk = k__5;
//line 2298 "gzip.preprocessed.c"
          //tmp___5__5 = inflate_dynamic();
          {
//line 2298 "gzip.preprocessed.c"
            int __return__6;
//line 2164 "gzip.preprocessed.c"
            //enter inflate_dynamic
            int  i__6;
            unsigned int  j__6;
            unsigned int  l__6;
            unsigned int  m__6;
            unsigned int  n__6;
            struct huft * tl__6;
            struct huft * td__6;
            int  bl__6;
            int  bd__6;
            unsigned int  nb__6;
            unsigned int  nl__6;
            unsigned int  nd__6;
            unsigned int  ll__6[316];
            ulg  b__6;
            unsigned int  k__6;
            unsigned int  tmp__6;
            int  tmp___0__6;
            int  tmp___1__6;
            unsigned int  tmp___2__6;
            int  tmp___3__6;
            int  tmp___4__6;
            unsigned int  tmp___5__6;
            int  tmp___6__6;
            int  tmp___7__6;
            unsigned int  tmp___8__6;
            int  tmp___9__6;
            int  tmp___10__6;
            unsigned int  tmp___11__6;
            int  tmp___12__6;
            int  tmp___13__6;
            int  tmp___14__6;
            unsigned int  tmp___15__6;
            int  tmp___16__6;
            int  tmp___17__6;
            int  tmp___18__6;
            unsigned int  tmp___19__6;
            unsigned int  tmp___20__6;
            int  tmp___21__6;
            int  tmp___22__6;
            int  tmp___23__6;
            unsigned int  tmp___24__6;
            unsigned int  tmp___25__6;
            int  tmp___26__6;
            int  tmp___27__6;
            int  tmp___28__6;
            unsigned int  tmp___29__6;
            int  tmp___30__6;
            unsigned long  __cil_tmp48__6;
            unsigned long  __cil_tmp49__6;
            uch  __cil_tmp50__6;
            uch  __cil_tmp51__6;
            ulg  __cil_tmp52__6;
            ulg  __cil_tmp53__6;
            unsigned int  __cil_tmp54__6;
            unsigned int  __cil_tmp55__6;
            unsigned long  __cil_tmp56__6;
            unsigned long  __cil_tmp57__6;
            uch  __cil_tmp58__6;
            uch  __cil_tmp59__6;
            ulg  __cil_tmp60__6;
            ulg  __cil_tmp61__6;
            unsigned int  __cil_tmp62__6;
            unsigned int  __cil_tmp63__6;
            unsigned long  __cil_tmp64__6;
            unsigned long  __cil_tmp65__6;
            uch  __cil_tmp66__6;
            uch  __cil_tmp67__6;
            ulg  __cil_tmp68__6;
            ulg  __cil_tmp69__6;
            unsigned int  __cil_tmp70__6;
            unsigned int  __cil_tmp71__6;
            unsigned long  __cil_tmp72__6;
            unsigned long  __cil_tmp73__6;
            uch  __cil_tmp74__6;
            uch  __cil_tmp75__6;
            ulg  __cil_tmp76__6;
            ulg  __cil_tmp77__6;
            unsigned long  __cil_tmp78__6;
            unsigned long  __cil_tmp79__6;
            unsigned int  __cil_tmp80__6;
            unsigned long  __cil_tmp81__6;
            unsigned long  __cil_tmp82__6;
            unsigned int  __cil_tmp83__6;
            unsigned long  __cil_tmp84__6;
            unsigned long  __cil_tmp85__6;
            unsigned int  __cil_tmp86__6;
            unsigned long  __cil_tmp87__6;
            unsigned long  __cil_tmp88__6;
            int * __cil_tmp89__6;
            unsigned long  __cil_tmp90__6;
            unsigned long  __cil_tmp91__6;
            unsigned int * __cil_tmp92__6;
            void * __cil_tmp93__6;
            ush * __cil_tmp94__6;
            void * __cil_tmp95__6;
            ush * __cil_tmp96__6;
            struct huft ** __cil_tmp97__6;
            struct huft * __cil_tmp98__6;
            int * __cil_tmp99__6;
            int  __cil_tmp100__6;
            unsigned long  __cil_tmp101__6;
            unsigned long  __cil_tmp102__6;
            ush  __cil_tmp103__6;
            unsigned int  __cil_tmp104__6;
            int * __cil_tmp105__6;
            int  __cil_tmp106__6;
            unsigned int  __cil_tmp107__6;
            unsigned long  __cil_tmp108__6;
            unsigned long  __cil_tmp109__6;
            uch  __cil_tmp110__6;
            uch  __cil_tmp111__6;
            ulg  __cil_tmp112__6;
            ulg  __cil_tmp113__6;
            struct huft ** __cil_tmp114__6;
            unsigned int  __cil_tmp115__6;
            unsigned int  __cil_tmp116__6;
            struct huft ** __cil_tmp117__6;
            struct huft * __cil_tmp118__6;
            struct huft ** __cil_tmp119__6;
            struct huft * __cil_tmp120__6;
            unsigned long  __cil_tmp121__6;
            unsigned long  __cil_tmp122__6;
            uch  __cil_tmp123__6;
            struct huft ** __cil_tmp124__6;
            struct huft * __cil_tmp125__6;
            unsigned long  __cil_tmp126__6;
            unsigned long  __cil_tmp127__6;
            ush  __cil_tmp128__6;
            unsigned long  __cil_tmp129__6;
            unsigned long  __cil_tmp130__6;
            unsigned long  __cil_tmp131__6;
            unsigned long  __cil_tmp132__6;
            uch  __cil_tmp133__6;
            uch  __cil_tmp134__6;
            ulg  __cil_tmp135__6;
            ulg  __cil_tmp136__6;
            unsigned int  __cil_tmp137__6;
            unsigned int  __cil_tmp138__6;
            unsigned int  __cil_tmp139__6;
            unsigned int  __cil_tmp140__6;
            unsigned long  __cil_tmp141__6;
            unsigned long  __cil_tmp142__6;
            unsigned long  __cil_tmp143__6;
            unsigned long  __cil_tmp144__6;
            uch  __cil_tmp145__6;
            uch  __cil_tmp146__6;
            ulg  __cil_tmp147__6;
            ulg  __cil_tmp148__6;
            unsigned int  __cil_tmp149__6;
            unsigned int  __cil_tmp150__6;
            unsigned int  __cil_tmp151__6;
            unsigned int  __cil_tmp152__6;
            unsigned long  __cil_tmp153__6;
            unsigned long  __cil_tmp154__6;
            unsigned long  __cil_tmp155__6;
            unsigned long  __cil_tmp156__6;
            uch  __cil_tmp157__6;
            uch  __cil_tmp158__6;
            ulg  __cil_tmp159__6;
            ulg  __cil_tmp160__6;
            unsigned int  __cil_tmp161__6;
            unsigned int  __cil_tmp162__6;
            unsigned int  __cil_tmp163__6;
            unsigned int  __cil_tmp164__6;
            unsigned long  __cil_tmp165__6;
            unsigned long  __cil_tmp166__6;
            struct huft ** __cil_tmp167__6;
            struct huft * __cil_tmp168__6;
            int * __cil_tmp169__6;
            unsigned long  __cil_tmp170__6;
            unsigned long  __cil_tmp171__6;
            unsigned int * __cil_tmp172__6;
            unsigned long  __cil_tmp173__6;
            unsigned long  __cil_tmp174__6;
            ush * __cil_tmp175__6;
            unsigned long  __cil_tmp176__6;
            unsigned long  __cil_tmp177__6;
            ush * __cil_tmp178__6;
            FILE * __restrict   __cil_tmp179__6;
            char const   * __restrict   __cil_tmp180__6;
            struct huft ** __cil_tmp181__6;
            struct huft * __cil_tmp182__6;
            int * __cil_tmp183__6;
            unsigned long  __cil_tmp184__6;
            unsigned long  __cil_tmp185__6;
            unsigned int * __cil_tmp186__6;
            unsigned int * __cil_tmp187__6;
            unsigned long  __cil_tmp188__6;
            unsigned long  __cil_tmp189__6;
            ush * __cil_tmp190__6;
            unsigned long  __cil_tmp191__6;
            unsigned long  __cil_tmp192__6;
            ush * __cil_tmp193__6;
            FILE * __restrict   __cil_tmp194__6;
            char const   * __restrict   __cil_tmp195__6;
            struct huft ** __cil_tmp196__6;
            struct huft * __cil_tmp197__6;
            struct huft ** __cil_tmp198__6;
            struct huft * __cil_tmp199__6;
            struct huft ** __cil_tmp200__6;
            struct huft * __cil_tmp201__6;
            struct huft ** __cil_tmp202__6;
            struct huft * __cil_tmp203__6;
            int * __cil_tmp204__6;
            int  __cil_tmp205__6;
            int * __cil_tmp206__6;
            int  __cil_tmp207__6;
            struct huft ** __cil_tmp208__6;
            struct huft * __cil_tmp209__6;
            struct huft ** __cil_tmp210__6;
            struct huft * __cil_tmp211__6;
            uch * mem_212__6;
            uch * mem_213__6;
            uch * mem_214__6;
            uch * mem_215__6;
            unsigned int * mem_216__6;
            unsigned int * mem_217__6;
            unsigned int * mem_218__6;
            unsigned int * mem_219__6;
            ush * mem_220__6;
            uch * mem_221__6;
            uch * mem_222__6;
            ush * mem_223__6;
            unsigned int * mem_224__6;
            uch * mem_225__6;
            unsigned int * mem_226__6;
            uch * mem_227__6;
            unsigned int * mem_228__6;
            uch * mem_229__6;
            unsigned int * mem_230__6;
//line 2181 "gzip.preprocessed.c"
            b__6 = bb;
//line 2182 "gzip.preprocessed.c"
            k__6 = bk;
//line 2184 "gzip.preprocessed.c"
            __cil_tmp54__6 = (unsigned int )(b__6);
//line 2184 "gzip.preprocessed.c"
            __cil_tmp55__6 = (__cil_tmp54__6) & (31U);
//line 2184 "gzip.preprocessed.c"
            nl__6 = (257U) + (__cil_tmp55__6);
//line 2185 "gzip.preprocessed.c"
            b__6 = (b__6) >> (5);
//line 2185 "gzip.preprocessed.c"
            k__6 = (k__6) - (5U);
//line 2186 "gzip.preprocessed.c"
            tmp___2__6 = inptr;
//line 2186 "gzip.preprocessed.c"
            inptr = (inptr) + (1U);
//line 2186 "gzip.preprocessed.c"
            __cil_tmp56__6 = (tmp___2__6) * (1UL);
//line 2186 "gzip.preprocessed.c"
            __cil_tmp57__6 = ((unsigned long )(inbuf)) + (__cil_tmp56__6);
//line 2186 "gzip.preprocessed.c"
            mem_213__6 = (uch *)(__cil_tmp57__6);
//line 2186 "gzip.preprocessed.c"
            __cil_tmp58__6 = *mem_213__6;
//line 2186 "gzip.preprocessed.c"
            tmp___4__6 = (int )(__cil_tmp58__6);
//line 2186 "gzip.preprocessed.c"
            __cil_tmp59__6 = (uch )(tmp___4__6);
//line 2186 "gzip.preprocessed.c"
            __cil_tmp60__6 = (ulg )(__cil_tmp59__6);
//line 2186 "gzip.preprocessed.c"
            __cil_tmp61__6 = (__cil_tmp60__6) << (k__6);
//line 2186 "gzip.preprocessed.c"
            b__6 = (b__6) | (__cil_tmp61__6);
//line 2186 "gzip.preprocessed.c"
            k__6 = (k__6) + (8U);
//line 2187 "gzip.preprocessed.c"
            __cil_tmp62__6 = (unsigned int )(b__6);
//line 2187 "gzip.preprocessed.c"
            __cil_tmp63__6 = (__cil_tmp62__6) & (31U);
//line 2187 "gzip.preprocessed.c"
            nd__6 = (1U) + (__cil_tmp63__6);
//line 2188 "gzip.preprocessed.c"
            b__6 = (b__6) >> (5);
//line 2188 "gzip.preprocessed.c"
            k__6 = (k__6) - (5U);
//line 2189 "gzip.preprocessed.c"
            tmp___5__6 = inptr;
//line 2189 "gzip.preprocessed.c"
            inptr = (inptr) + (1U);
//line 2189 "gzip.preprocessed.c"
            __cil_tmp64__6 = (tmp___5__6) * (1UL);
//line 2189 "gzip.preprocessed.c"
            __cil_tmp65__6 = ((unsigned long )(inbuf)) + (__cil_tmp64__6);
//line 2189 "gzip.preprocessed.c"
            mem_214__6 = (uch *)(__cil_tmp65__6);
//line 2189 "gzip.preprocessed.c"
            __cil_tmp66__6 = *mem_214__6;
//line 2189 "gzip.preprocessed.c"
            tmp___7__6 = (int )(__cil_tmp66__6);
//line 2189 "gzip.preprocessed.c"
            __cil_tmp67__6 = (uch )(tmp___7__6);
//line 2189 "gzip.preprocessed.c"
            __cil_tmp68__6 = (ulg )(__cil_tmp67__6);
//line 2189 "gzip.preprocessed.c"
            __cil_tmp69__6 = (__cil_tmp68__6) << (k__6);
//line 2189 "gzip.preprocessed.c"
            b__6 = (b__6) | (__cil_tmp69__6);
//line 2189 "gzip.preprocessed.c"
            k__6 = (k__6) + (8U);
//line 2190 "gzip.preprocessed.c"
            __cil_tmp70__6 = (unsigned int )(b__6);
//line 2190 "gzip.preprocessed.c"
            __cil_tmp71__6 = (__cil_tmp70__6) & (15U);
//line 2190 "gzip.preprocessed.c"
            nb__6 = (4U) + (__cil_tmp71__6);
//line 2191 "gzip.preprocessed.c"
            b__6 = (b__6) >> (4);
//line 2191 "gzip.preprocessed.c"
            k__6 = (k__6) - (4U);
//line 2194 "gzip.preprocessed.c"
            j__6 = 0U;
//line 2197 "gzip.preprocessed.c"
            __cil_tmp78__6 = (j__6) * (4UL);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp79__6 = ((unsigned long )(border)) + (__cil_tmp78__6);
//line 2197 "gzip.preprocessed.c"
            mem_216__6 = (unsigned int *)(__cil_tmp79__6);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp80__6 = *mem_216__6;
//line 2197 "gzip.preprocessed.c"
            __cil_tmp81__6 = (__cil_tmp80__6) * (4UL);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp82__6 = ((unsigned long )(ll__6)) + (__cil_tmp81__6);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp83__6 = (unsigned int )(b__6);
//line 2197 "gzip.preprocessed.c"
            mem_217__6 = (unsigned int *)(__cil_tmp82__6);
//line 2197 "gzip.preprocessed.c"
            *mem_217__6 = (__cil_tmp83__6) & (7U);
//line 2198 "gzip.preprocessed.c"
            b__6 = (b__6) >> (3);
//line 2198 "gzip.preprocessed.c"
            k__6 = (k__6) - (3U);
//line 2194 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp78__6 = (j__6) * (4UL);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp79__6 = ((unsigned long )(border)) + (__cil_tmp78__6);
//line 2197 "gzip.preprocessed.c"
            mem_216__6 = (unsigned int *)(__cil_tmp79__6);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp80__6 = *mem_216__6;
//line 2197 "gzip.preprocessed.c"
            __cil_tmp81__6 = (__cil_tmp80__6) * (4UL);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp82__6 = ((unsigned long )(ll__6)) + (__cil_tmp81__6);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp83__6 = (unsigned int )(b__6);
//line 2197 "gzip.preprocessed.c"
            mem_217__6 = (unsigned int *)(__cil_tmp82__6);
//line 2197 "gzip.preprocessed.c"
            *mem_217__6 = (__cil_tmp83__6) & (7U);
//line 2198 "gzip.preprocessed.c"
            b__6 = (b__6) >> (3);
//line 2198 "gzip.preprocessed.c"
            k__6 = (k__6) - (3U);
//line 2194 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2196 "gzip.preprocessed.c"
            tmp___8__6 = inptr;
//line 2196 "gzip.preprocessed.c"
            inptr = (inptr) + (1U);
//line 2196 "gzip.preprocessed.c"
            __cil_tmp72__6 = (tmp___8__6) * (1UL);
//line 2196 "gzip.preprocessed.c"
            __cil_tmp73__6 = ((unsigned long )(inbuf)) + (__cil_tmp72__6);
//line 2196 "gzip.preprocessed.c"
            mem_215__6 = (uch *)(__cil_tmp73__6);
//line 2196 "gzip.preprocessed.c"
            __cil_tmp74__6 = *mem_215__6;
//line 2196 "gzip.preprocessed.c"
            tmp___10__6 = (int )(__cil_tmp74__6);
//line 2196 "gzip.preprocessed.c"
            __cil_tmp75__6 = (uch )(tmp___10__6);
//line 2196 "gzip.preprocessed.c"
            __cil_tmp76__6 = (ulg )(__cil_tmp75__6);
//line 2196 "gzip.preprocessed.c"
            __cil_tmp77__6 = (__cil_tmp76__6) << (k__6);
//line 2196 "gzip.preprocessed.c"
            b__6 = (b__6) | (__cil_tmp77__6);
//line 2196 "gzip.preprocessed.c"
            k__6 = (k__6) + (8U);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp78__6 = (j__6) * (4UL);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp79__6 = ((unsigned long )(border)) + (__cil_tmp78__6);
//line 2197 "gzip.preprocessed.c"
            mem_216__6 = (unsigned int *)(__cil_tmp79__6);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp80__6 = *mem_216__6;
//line 2197 "gzip.preprocessed.c"
            __cil_tmp81__6 = (__cil_tmp80__6) * (4UL);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp82__6 = ((unsigned long )(ll__6)) + (__cil_tmp81__6);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp83__6 = (unsigned int )(b__6);
//line 2197 "gzip.preprocessed.c"
            mem_217__6 = (unsigned int *)(__cil_tmp82__6);
//line 2197 "gzip.preprocessed.c"
            *mem_217__6 = (__cil_tmp83__6) & (7U);
//line 2198 "gzip.preprocessed.c"
            b__6 = (b__6) >> (3);
//line 2198 "gzip.preprocessed.c"
            k__6 = (k__6) - (3U);
//line 2194 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp78__6 = (j__6) * (4UL);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp79__6 = ((unsigned long )(border)) + (__cil_tmp78__6);
//line 2197 "gzip.preprocessed.c"
            mem_216__6 = (unsigned int *)(__cil_tmp79__6);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp80__6 = *mem_216__6;
//line 2197 "gzip.preprocessed.c"
            __cil_tmp81__6 = (__cil_tmp80__6) * (4UL);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp82__6 = ((unsigned long )(ll__6)) + (__cil_tmp81__6);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp83__6 = (unsigned int )(b__6);
//line 2197 "gzip.preprocessed.c"
            mem_217__6 = (unsigned int *)(__cil_tmp82__6);
//line 2197 "gzip.preprocessed.c"
            *mem_217__6 = (__cil_tmp83__6) & (7U);
//line 2198 "gzip.preprocessed.c"
            b__6 = (b__6) >> (3);
//line 2198 "gzip.preprocessed.c"
            k__6 = (k__6) - (3U);
//line 2194 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp78__6 = (j__6) * (4UL);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp79__6 = ((unsigned long )(border)) + (__cil_tmp78__6);
//line 2197 "gzip.preprocessed.c"
            mem_216__6 = (unsigned int *)(__cil_tmp79__6);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp80__6 = *mem_216__6;
//line 2197 "gzip.preprocessed.c"
            __cil_tmp81__6 = (__cil_tmp80__6) * (4UL);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp82__6 = ((unsigned long )(ll__6)) + (__cil_tmp81__6);
//line 2197 "gzip.preprocessed.c"
            __cil_tmp83__6 = (unsigned int )(b__6);
//line 2197 "gzip.preprocessed.c"
            mem_217__6 = (unsigned int *)(__cil_tmp82__6);
//line 2197 "gzip.preprocessed.c"
            *mem_217__6 = (__cil_tmp83__6) & (7U);
//line 2198 "gzip.preprocessed.c"
            b__6 = (b__6) >> (3);
//line 2198 "gzip.preprocessed.c"
            k__6 = (k__6) - (3U);
//line 2194 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
//line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
//line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
//line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
//line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
//line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
//line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
//line 2202 "gzip.preprocessed.c"
            __cil_tmp89__6 = &bl__6;
//line 2202 "gzip.preprocessed.c"
            *__cil_tmp89__6 = 7;
//line 2203 "gzip.preprocessed.c"
            __cil_tmp90__6 = (0) * (4UL);
//line 2203 "gzip.preprocessed.c"
            __cil_tmp91__6 = ((unsigned long )(ll__6)) + (__cil_tmp90__6);
//line 2203 "gzip.preprocessed.c"
            __cil_tmp92__6 = (unsigned int *)(__cil_tmp91__6);
//line 2203 "gzip.preprocessed.c"
            __cil_tmp93__6 = (void *)(0);
//line 2203 "gzip.preprocessed.c"
            __cil_tmp94__6 = (ush *)(__cil_tmp93__6);
//line 2203 "gzip.preprocessed.c"
            __cil_tmp95__6 = (void *)(0);
//line 2203 "gzip.preprocessed.c"
            __cil_tmp96__6 = (ush *)(__cil_tmp95__6);
//line 2203 "gzip.preprocessed.c"
            //i__6 = huft_build(__cil_tmp92__6, 19U, 19U, __cil_tmp94__6, __cil_tmp96__6, &tl__6, &bl__6);
            {
//line 2203 "gzip.preprocessed.c"
              unsigned int * __arg_tmp_0__7  = __cil_tmp92__6;
//line 2203 "gzip.preprocessed.c"
              unsigned int  __arg_tmp_1__7  = 19U;
//line 2203 "gzip.preprocessed.c"
              unsigned int  __arg_tmp_2__7  = 19U;
//line 2203 "gzip.preprocessed.c"
              ush * __arg_tmp_3__7  = __cil_tmp94__6;
//line 2203 "gzip.preprocessed.c"
              ush * __arg_tmp_4__7  = __cil_tmp96__6;
//line 2203 "gzip.preprocessed.c"
              struct huft ** __arg_tmp_5__7  = &tl__6;
//line 2203 "gzip.preprocessed.c"
              int * __arg_tmp_6__7  = &bl__6;
//line 2203 "gzip.preprocessed.c"
              int __return__7;
//line 1849 "gzip.preprocessed.c"
              //enter huft_build
              unsigned int * b__7 = __arg_tmp_0__7 ;
              unsigned int  n__7 = __arg_tmp_1__7 ;
              unsigned int  s__7 = __arg_tmp_2__7 ;
              ush * d__7 = __arg_tmp_3__7 ;
              ush * e__7 = __arg_tmp_4__7 ;
              struct huft ** t__7 = __arg_tmp_5__7 ;
              int * m__7 = __arg_tmp_6__7 ;
              unsigned int  a__7;
              unsigned int  c__7[17];
              unsigned int  f__7;
              int  g__7;
              int  h__7;
              unsigned int  i__7;
              unsigned int  j__7;
              int  k__7;
              int  l__7;
              unsigned int * p__7;
              struct huft * q__7;
              struct huft  r__7;
              struct huft * u__7[16];
              unsigned int  v__7[288];
              int  w__7;
              unsigned int  x__7[17];
              unsigned int * xp__7;
              int  y__7;
              unsigned int  z__7;
              unsigned int * tmp__7;
              unsigned int * tmp___0__7;
              unsigned int  tmp___1__7;
              unsigned int * tmp___2__7;
              void * tmp___3__7;
              int  tmp___4__7;
              unsigned int * tmp___5__7;
              unsigned int  tmp___6__7;
              int  tmp___7__7;
              unsigned long  __cil_tmp36__7;
              unsigned long  __cil_tmp37__7;
              unsigned int * __cil_tmp38__7;
              voidp  __cil_tmp39__7;
              unsigned int  __cil_tmp40__7;
              unsigned long  __cil_tmp41__7;
              unsigned long  __cil_tmp42__7;
              unsigned int  __cil_tmp43__7;
              unsigned long  __cil_tmp44__7;
              unsigned long  __cil_tmp45__7;
              unsigned int  __cil_tmp46__7;
              unsigned long  __cil_tmp47__7;
              unsigned long  __cil_tmp48__7;
              unsigned int  __cil_tmp49__7;
              void * __cil_tmp50__7;
              unsigned long  __cil_tmp51__7;
              unsigned long  __cil_tmp52__7;
              unsigned int  __cil_tmp53__7;
              unsigned long  __cil_tmp54__7;
              unsigned long  __cil_tmp55__7;
              unsigned int  __cil_tmp56__7;
              unsigned long  __cil_tmp57__7;
              unsigned long  __cil_tmp58__7;
              unsigned int  __cil_tmp59__7;
              unsigned int  __cil_tmp60__7;
              unsigned int  __cil_tmp61__7;
              unsigned long  __cil_tmp62__7;
              unsigned long  __cil_tmp63__7;
              unsigned int  __cil_tmp64__7;
              unsigned int  __cil_tmp65__7;
              unsigned int  __cil_tmp66__7;
              unsigned long  __cil_tmp67__7;
              unsigned long  __cil_tmp68__7;
              unsigned int  __cil_tmp69__7;
              unsigned long  __cil_tmp70__7;
              unsigned long  __cil_tmp71__7;
              unsigned int  __cil_tmp72__7;
              unsigned long  __cil_tmp73__7;
              unsigned long  __cil_tmp74__7;
              unsigned long  __cil_tmp75__7;
              unsigned long  __cil_tmp76__7;
              unsigned int * __cil_tmp77__7;
              unsigned long  __cil_tmp78__7;
              unsigned long  __cil_tmp79__7;
              unsigned int * __cil_tmp80__7;
              unsigned int  __cil_tmp81__7;
              unsigned long  __cil_tmp82__7;
              unsigned long  __cil_tmp83__7;
              unsigned long  __cil_tmp84__7;
              unsigned long  __cil_tmp85__7;
              unsigned long  __cil_tmp86__7;
              unsigned long  __cil_tmp87__7;
              unsigned int  __cil_tmp88__7;
              unsigned long  __cil_tmp89__7;
              unsigned long  __cil_tmp90__7;
              unsigned long  __cil_tmp91__7;
              unsigned long  __cil_tmp92__7;
              unsigned long  __cil_tmp93__7;
              unsigned long  __cil_tmp94__7;
              unsigned long  __cil_tmp95__7;
              unsigned long  __cil_tmp96__7;
              void * __cil_tmp97__7;
              void * __cil_tmp98__7;
              unsigned long  __cil_tmp99__7;
              unsigned long  __cil_tmp100__7;
              int  __cil_tmp101__7;
              int  __cil_tmp102__7;
              unsigned int  __cil_tmp103__7;
              int  __cil_tmp104__7;
              int  __cil_tmp105__7;
              unsigned int  __cil_tmp106__7;
              unsigned int  __cil_tmp107__7;
              unsigned long  __cil_tmp108__7;
              unsigned long  __cil_tmp109__7;
              unsigned int * __cil_tmp110__7;
              unsigned int  __cil_tmp111__7;
              unsigned int  __cil_tmp112__7;
              int  __cil_tmp113__7;
              unsigned int  __cil_tmp114__7;
              unsigned long  __cil_tmp115__7;
              unsigned long  __cil_tmp116__7;
              void * __cil_tmp117__7;
              struct huft * __cil_tmp118__7;
              unsigned long  __cil_tmp119__7;
              unsigned long  __cil_tmp120__7;
              unsigned long  __cil_tmp121__7;
              unsigned long  __cil_tmp122__7;
              struct huft * __cil_tmp123__7;
              unsigned int  __cil_tmp124__7;
              unsigned long  __cil_tmp125__7;
              unsigned long  __cil_tmp126__7;
              void * __cil_tmp127__7;
              unsigned long  __cil_tmp128__7;
              unsigned long  __cil_tmp129__7;
              unsigned long  __cil_tmp130__7;
              unsigned long  __cil_tmp131__7;
              unsigned int  __cil_tmp132__7;
              int  __cil_tmp133__7;
              int  __cil_tmp134__7;
              unsigned long  __cil_tmp135__7;
              unsigned long  __cil_tmp136__7;
              struct huft * __cil_tmp137__7;
              struct huft * __cil_tmp138__7;
              int  __cil_tmp139__7;
              unsigned long  __cil_tmp140__7;
              unsigned long  __cil_tmp141__7;
              unsigned int * __cil_tmp142__7;
              unsigned int * __cil_tmp143__7;
              unsigned long  __cil_tmp144__7;
              unsigned long  __cil_tmp145__7;
              unsigned int  __cil_tmp146__7;
              unsigned int  __cil_tmp147__7;
              unsigned int  __cil_tmp148__7;
              unsigned int  __cil_tmp149__7;
              unsigned int  __cil_tmp150__7;
              ush * __cil_tmp151__7;
              ush  __cil_tmp152__7;
              unsigned int  __cil_tmp153__7;
              unsigned int  __cil_tmp154__7;
              ush * __cil_tmp155__7;
              int  __cil_tmp156__7;
              int  __cil_tmp157__7;
              struct huft * __cil_tmp158__7;
              int  __cil_tmp159__7;
              int  __cil_tmp160__7;
              unsigned long  __cil_tmp161__7;
              unsigned long  __cil_tmp162__7;
              unsigned int  __cil_tmp163__7;
              int  __cil_tmp164__7;
              int  __cil_tmp165__7;
              unsigned int  __cil_tmp166__7;
              unsigned int  __cil_tmp167__7;
	      //             union __anonunion_v_47  r_v168__7; DSN REMOVED
              uch  r_b169__7;
              uch  r_e170__7;
              unsigned int * mem_171__7;
              unsigned int * mem_172__7;
              unsigned int * mem_173__7;
              unsigned int * mem_174__7;
              unsigned int * mem_175__7;
              unsigned int * mem_176__7;
              unsigned int * mem_177__7;
              unsigned int * mem_178__7;
              unsigned int * mem_179__7;
              unsigned int * mem_180__7;
              unsigned int * mem_181__7;
              unsigned int * mem_182__7;
              unsigned int * mem_183__7;
              unsigned int * mem_184__7;
              unsigned int * mem_185__7;
              struct huft ** mem_186__7;
              unsigned int * mem_187__7;
              struct huft ** mem_188__7;
              struct huft ** mem_189__7;
              unsigned int * mem_190__7;
              struct huft ** mem_191__7;
              unsigned int * mem_192__7;
//line 1877 "gzip.preprocessed.c"
              __cil_tmp36__7 = (0) * (4UL);
//line 1877 "gzip.preprocessed.c"
              __cil_tmp37__7 = ((unsigned long )(c__7)) + (__cil_tmp36__7);
//line 1877 "gzip.preprocessed.c"
              __cil_tmp38__7 = (unsigned int *)(__cil_tmp37__7);
//line 1877 "gzip.preprocessed.c"
              __cil_tmp39__7 = (voidp )(__cil_tmp38__7);
//line 1877 "gzip.preprocessed.c"
              //memset(__cil_tmp39__7, 0, 68UL);
              {
//line 1877 "gzip.preprocessed.c"
                voidp  __arg_tmp_0__8  = __cil_tmp39__7;
//line 1877 "gzip.preprocessed.c"
                int  __arg_tmp_1__8  = 0;
//line 1877 "gzip.preprocessed.c"
                unsigned long  __arg_tmp_2__8  = 68UL;
              }
//line 1878 "gzip.preprocessed.c"
              p__7 = b__7;
//line 1878 "gzip.preprocessed.c"
              i__7 = n__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
//line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
//line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
//line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
//line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
//line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
//line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
//line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
//line 1881 "gzip.preprocessed.c"
/*              __cil_tmp42__7 = ((u
				 }
				 } DSN*/
	    }
	  }
	}
      }
    }
  }
}
