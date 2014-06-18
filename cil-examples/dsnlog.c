//Based on
//https://stackoverflow.com/questions/1719784/c-programming-forward-variable-argument-list
#include <stdarg.h>
#include <stdio.h>
#include <assert.h>

static FILE* pfile;

int dsn_log(const char* format, ...)
{
  if(!pfile){
    pfile = fopen("dsn_logfile.txt","w");
    assert(pfile);
  }

  va_list arglist;
  va_start(arglist,format);
  int result = vfprintf(pfile,format,arglist);
  va_end(arglist);
  return result;
}
