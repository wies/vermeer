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

int sprintf_dsn_wrapper(char *str, const char *format, ...)
{
  va_list arglist;
  va_start(arglist, format);
  int result = vsprintf(str, format, arglist);
  va_end(arglist);

  size_t i, len = strlen(str);
  for (i = 0; i < len; i++)
    dsn_log("/* sprintf_dsn_wrapper */ _dsn_mem_%p = %d\n", str+i, str[i]);

  return result;
}
