//Based on
//https://stackoverflow.com/questions/1719784/c-programming-forward-variable-argument-list
#include <stdarg.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>

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

// As is obvious here, no wrapper is needed. Just for debugging purposes.
double pow_dsn_wrapper(double x, double y) { return pow(x, y); }
