//Based on
//https://stackoverflow.com/questions/1719784/c-programming-forward-variable-argument-list
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <strings.h>
#include <assert.h>
#include <getopt.h>

typedef unsigned char uch;

static int unknown_index = 1;

int dsn_assert(int x)
{
  assert(x);
}

int dsn_log(const char* format, ...)
{
  static FILE *pfile = 0;
  if(!pfile){
    pfile = fopen("dsn_logfile.txt","w");
    assert(pfile);
    //Use line buffering. _IOFBF is another option
    setvbuf(pfile,NULL,_IOLBF,0);
  }

  va_list arglist;
  va_start(arglist,format);
  int result = vfprintf(pfile,format,arglist);
  va_end(arglist);
  return result;
}

int dsn_log_var(const char* format, ...)
{
  static FILE *pfile = 0;
  if(!pfile){
    pfile = fopen("var_snapshots.txt","w");
    assert(pfile);
    //Use line buffering. _IOFBF is another option
    setvbuf(pfile,NULL,_IOLBF,0);
  }

  va_list arglist;
  va_start(arglist,format);
  int result = vfprintf(pfile,format,arglist);
  va_end(arglist);
  return result;
}

void main_argc_argv_dsn_printer(int *p_argc, char ***p_argv,
                                int line_no, char *src_file)
{
  int i, j;
  int argc = *p_argc;
  char **argv = *p_argv;

  dsn_log("\n    //////////////////////////////////////////////////////////\n");
  dsn_log("    // Setting up argc and argv.                            //\n");
  dsn_log("    //////////////////////////////////////////////////////////\n");
  dsn_log("    // argc = %d\n", argc);
  dsn_log("#line %d \"%s\"\n", line_no, src_file);
  dsn_log("    long long main__1__argc = %d;\n", argc);
  dsn_log("#line %d \"%s\"\n", line_no, src_file);
  dsn_log("    _dsn_mem_%p/*|int |*/ = %d;\n", p_argc, argc);

  dsn_log("    // argv = %p\n", argv);
  dsn_log("#line %d \"%s\"\n", line_no, src_file);
  dsn_log("    long long main__1__argv = %p;\n", argv);
  dsn_log("#line %d \"%s\"\n", line_no, src_file);
  dsn_log("    _dsn_mem_%p/*|char **|*/ = %p;\n", p_argv, argv);
  for (i = 0; i < *p_argc; i++){
    dsn_log("    // argv[%d] = \"%s\"\n", i, argv[i]);
    dsn_log("#line %d \"%s\"\n", line_no, src_file);
    dsn_log("    _dsn_mem_%p/*|char *|*/ = %p;\n", argv+i, argv[i]);
    for (j = 0; argv[i][j] != 0; j++){
      dsn_log("#line %d \"%s\"\n", line_no, src_file);
      dsn_log("    _dsn_mem_%p/*|char |*/ = %d; // '%c'\n",
              argv[i]+j, argv[i][j], argv[i][j]); }
  }
  dsn_log("    //////////////////////////////////////////////////////////\n\n");
}

void *realloc_dsn_wrapper(void *ptr, size_t size)
{
  void *old_ptr = ptr;
  void *result = realloc(ptr, size);

  if (old_ptr != 0 && size != 0 && old_ptr != result){
    dsn_log("/* [realloc] Error: memory region relocated. */\n");
    //assert("Unimplemented: realloc() relocated memory region." && 0);
  }

  return result;
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
    dsn_log("/* [memset] */ _dsn_mem_%p/*|unknown_%d:unsigned char |*/ = %u;\n",
            p, unknown_index, c);
  unknown_index++;

  return result;
}

void bcopy_dsn_wrapper(const void *src, void *dest, size_t n)
{
  bcopy(src, dest, n);

  size_t i;
  uch *p = (uch *)dest;
  uch *end = p + n;
  dsn_log("/* [bcopy] Warning: assuming unsigned char. */\n");
  for (; p < end; p++)
    dsn_log("/* [bcopy] */ _dsn_mem_%p/*|unknown %d:unsigned char |*/ = %u;\n",
            p, unknown_index, *p);
  unknown_index++;
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
#if 0
  uch *p = (uch *)buf;
  uch *end = p + result;
  for (; p < end; p++)
    dsn_log("/* [read] */ _dsn_mem_%p/*|unknown_%d:unsigned char |*/ = %d;\n",
            p, unknown_index, *p);
#else
  char *p = (uch *)buf;
  char *end = p + result;
  for (; p < end; p++)
    dsn_log("/* [read] */ _dsn_mem_%p/*|unknown_%d:char |*/ = %d;\n",
            p, unknown_index, *p);
#endif
  unknown_index++;

  return result;
}

size_t fread_dsn_wrapper(void *ptr, size_t size, size_t nmemb, FILE *stream)
{
  size_t result = fread(ptr, size, nmemb, stream);

  if (size != 1){
    dsn_log("/* [fread] Error: size requested is not 1. */");
    assert("Unimplemented: fread(): size requested is not 1." && 0);
  }
  dsn_log("/* [fread] Read %d bytes. */\n", result);
  dsn_log("/* [read] Warning: byte-granularity */\n");

#if 0
  uch *p = (uch *)buf;
  uch *end = p + result;
  for (; p < end; p++)
    dsn_log("/* [fread] */ _dsn_mem_%p/*|unknown_%d:unsigned char |*/ = %d;\n",
            p, unknown_index, *p);
#else
  char *p = (uch *)ptr;
  char *end = p + result;
  for (; p < end; p++)
    dsn_log("/* [fread] */ _dsn_mem_%p/*|unknown_%d:char |*/ = %d;\n",
            p, unknown_index, *p);
#endif
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
      dsn_log("/* [getopt_long] Error: non-zero flag pointer in longopts"
                              " not yet supported. */\n");
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
