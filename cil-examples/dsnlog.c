//Based on
//https://stackoverflow.com/questions/1719784/c-programming-forward-variable-argument-list
#include <stdarg.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <unistd.h>
#include <getopt.h>

typedef unsigned char uch;

static int unknown_index = 1;

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

  dsn_log("\n    //////////////////////////////////////////////////////////\n");
  dsn_log("    // Setting up argc and argv.                            //\n");
  dsn_log("    //////////////////////////////////////////////////////////\n");
  dsn_log("    // argc = %d\n", argc);
  dsn_log("    int argc__1 = %d;\n", argc);
  dsn_log("    _dsn_mem_%p/*|int |*/ = %d;\n", p_argc, argc);

  dsn_log("    // argv = %p\n", argv);
  dsn_log("    char **argv__1 = %p;\n", argv);
  dsn_log("    _dsn_mem_%p/*|char **|*/ = %p;\n", p_argv, argv);
  for (i = 0; i < *p_argc; i++){
    dsn_log("    // argv[%d] = \"%s\"\n", i, argv[i]);
    dsn_log("    _dsn_mem_%p/*|char *|*/ = %p;\n", argv+i, argv[i]);
    for (j = 0; argv[i][j] != 0; j++)
      dsn_log("    _dsn_mem_%p/*|char |*/ = %d; // '%c'\n",
              argv[i]+j, argv[i][j], argv[i][j]);
  }
  dsn_log("    //////////////////////////////////////////////////////////\n\n");
}

void *memset_dsn_wrapper(void *s, int c, size_t n)
{
  void *result = memset(s, c, n);

  dsn_log("/* [memset] Filling %d bytes with %d. */\n", n, c);
  dsn_log("/* [memset] Warning: byte-granularity */\n");
  if (c != 0)
    dsn_log("/* [memset] Warning: non-zero initialization */\n");

  uch *p = (uch *)s;
  uch *end = p + n;
  for (; p < end; p++)
    dsn_log("/* [memset] */ _dsn_mem_%p/*|unknown_%d:unsigned char |*/ = %d;\n",
            p, unknown_index, c);
  unknown_index++;

  return result;
}

char *strcpy_dsn_wrapper(char *dest, const char *src)
{
  char *result = strcpy(dest, src);

  size_t i, len = strlen(src);
  for (i = 0; i < len; i++)
    dsn_log("/* [strcpy] */ _dsn_mem_%p/*|char |*/ = %d;\n", dest+i, dest[i]);
  dsn_log("/* [strcpy] */ _dsn_mem_%p/*|char |*/ = 0;\n", dest+len);
  return result;
}

char *strncpy_dsn_wrapper(char *dest, const char *src, size_t n)
{
  char *result = strncpy(dest, src, n);

  size_t i;
  // strncpy always writes exactly n bytes (with possible trailing nulls).
  for (i = 0; i < n; i++)
    dsn_log("/* [strncpy] */ _dsn_mem_%p/*|char |*/ = %d;\n", dest+i, dest[i]);
  return result;
}

ssize_t read_dsn_wrapper(int fildes, void *buf, size_t nbyte)
{
  ssize_t result = read(fildes, buf, nbyte);

  if (result == -1){
    dsn_log("/* [read] read() failed with an error. */\n");
    return -1;
  } else if (result == 0){
    dsn_log("/* [read] Nothing actually read (returns 0). */\n");
    return 0;
  }

  dsn_log("/* [read] Read %d bytes. */\n", result);
  dsn_log("/* [read] Warning: byte-granularity */\n");
  uch *p = (uch *)buf;
  uch *end = p + result;
  for (; p < end; p++)
    dsn_log("/* [read] */ _dsn_mem_%p/*|unknown_%d:unsigned char |*/ = %d;\n",
            p, unknown_index, *p);
  unknown_index++;

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
    dsn_log("/* [sprintf] */ _dsn_mem_%p/*|char |*/ = %d;\n", str+i, str[i]);
  dsn_log("/* [sprintf] */ _dsn_mem_%p/*|char |*/ = 0;\n", str+len);

  return result;
}

int getopt_long_dsn_wrapper(int argc, char * const argv[],
                            const char *optstring,
                            const struct option *longopts, int *longindex)
{
  const struct option *p = longopts;
  while (! (p->name == 0 && p->has_arg == 0 && p->flag == 0 && p->val == 0)){
    if (p->flag != 0)
      dsn_log("/* [getopt_long] */ "
              "Error: non-zero flag pointer in longopts not yet supported.\n");
    p++;
  }

  int old_optind = optind;
  char *old_optarg = optarg;
  int result = getopt_long(argc, argv, optstring, longopts, longindex);

  if (old_optind != optind)
    dsn_log("/* [getopt_long] */ optind = %d;\n", optind);
  if (old_optarg != optarg)
    dsn_log("/* [getopt_long] */ optarg = %p;\n", optarg);
  if (longindex != 0)
    dsn_log("/* [getopt_long] */ _dsn_mem_%p/*|int |*/ = %d;\n",
            longindex, *longindex);

  return result;
}
