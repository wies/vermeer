//Based on
//https://stackoverflow.com/questions/1719784/c-programming-forward-variable-argument-list
#include <stdarg.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <string.h>

static FILE* pfile;

int dsn_log(const char* format, ...)
{
  if(!pfile){
    pfile = fopen("dsn_logfile.txt","w");
    assert(pfile);
    //Use line buffering. _IOFBF is anothe option
    setvbuf(pfile,NULL,_IOLBF,0);
  }

  va_list arglist;
  va_start(arglist,format);
  int result = vfprintf(pfile,format,arglist);
  va_end(arglist);
  return result;
}

void main_argc_argv_dsn_printer(int *p_argc, char ***p_argv)
{
  int i, j;
  int argc = *p_argc;
  char **argv = *p_argv;

  dsn_log("\n    /********************************************************/\n");
  dsn_log("    /* argc = %d */\n", argc);
  dsn_log("    int argc__1 = %d;\n", argc);
  dsn_log("    _dsn_mem_%p/*|int |*/ = %d;\n", p_argc, argc);

  dsn_log("    /* argv = %p */\n", argv);
  dsn_log("    char **argv__1 = %p;\n", argv);
  dsn_log("    _dsn_mem_%p/*|char **|*/ = %p;\n", p_argv, argv);
  // I don't think we need this, so commenting out.
  //dsn_log("    /* *argv = %p */\n", *argv);
  //dsn_log("    _dsn_mem_%p/*|char *|*/ = %p;\n", argv, *argv);
  for (i = 0; i < *p_argc; i++){
    dsn_log("    /* argv[%d] = \"%s\" */\n", i, argv[i]);
    for (j = 0; argv[i][j] != 0; j++)
      dsn_log("    _dsn_mem_%p/*|char |*/ = %d; /* '%c' */\n",
              argv[i]+j, argv[i][j], argv[i][j]);
  }
  dsn_log("    /********************************************************/\n\n");
}

int sprintf_dsn_wrapper(char *str, const char *format, ...)
{
  va_list arglist;
  va_start(arglist, format);
  int result = vsprintf(str, format, arglist);
  va_end(arglist);

  size_t i, len = strlen(str);
  for (i = 0; i < len; i++)
    dsn_log("/* sprintf_dsn_wrapper */ _dsn_mem_%p = %d\n", str+i, str[i]);
  dsn_log("/* sprintf_dsn_wrapper */ _dsn_mem_%p = 0\n", str+len);

  return result;
}
