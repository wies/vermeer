extern char *optarg;
extern int optind;
extern int opterr;
extern int optopt;
struct option
{
  const char *name;
  int has_arg;
  int *flag;
  int val;
};
extern int getopt_long (int argc, char *const *argv, const char *shortopts,
          const struct option *longopts, int *longind);
extern int getopt_long_only (int argc, char *const *argv,
        const char *shortopts,
               const struct option *longopts, int *longind);
extern int _getopt_internal (int argc, char *const *argv,
        const char *shortopts,
               const struct option *longopts, int *longind,
        int long_only);
   typedef void *voidp;

typedef long unsigned int size_t;







typedef unsigned char __u_char;
typedef unsigned short int __u_short;
typedef unsigned int __u_int;
typedef unsigned long int __u_long;


typedef signed char __int8_t;
typedef unsigned char __uint8_t;
typedef signed short int __int16_t;
typedef unsigned short int __uint16_t;
typedef signed int __int32_t;
typedef unsigned int __uint32_t;

typedef signed long int __int64_t;
typedef unsigned long int __uint64_t;







typedef long int __quad_t;
typedef unsigned long int __u_quad_t;
typedef unsigned long int __dev_t;
typedef unsigned int __uid_t;
typedef unsigned int __gid_t;
typedef unsigned long int __ino_t;
typedef unsigned long int __ino64_t;
typedef unsigned int __mode_t;
typedef unsigned long int __nlink_t;
typedef long int __off_t;
typedef long int __off64_t;
typedef int __pid_t;
typedef struct { int __val[2]; } __fsid_t;
typedef long int __clock_t;
typedef unsigned long int __rlim_t;
typedef unsigned long int __rlim64_t;
typedef unsigned int __id_t;
typedef long int __time_t;
typedef unsigned int __useconds_t;
typedef long int __suseconds_t;
typedef int __daddr_t;
typedef long int __swblk_t;
typedef int __key_t;
typedef int __clockid_t;
typedef void * __timer_t;
typedef long int __blksize_t;
typedef long int __blkcnt_t;
typedef long int __blkcnt64_t;
typedef unsigned long int __fsblkcnt_t;
typedef unsigned long int __fsblkcnt64_t;
typedef unsigned long int __fsfilcnt_t;
typedef unsigned long int __fsfilcnt64_t;
typedef long int __ssize_t;
typedef __off64_t __loff_t;
typedef __quad_t *__qaddr_t;
typedef char *__caddr_t;
typedef long int __intptr_t;
typedef unsigned int __socklen_t;
struct _IO_FILE;

typedef struct _IO_FILE FILE;


typedef struct _IO_FILE __FILE;
typedef struct
{
  int __count;
  union
  {
    unsigned int __wch;
    char __wchb[4];
  } __value;
} __mbstate_t;
typedef struct
{
  __off_t __pos;
  __mbstate_t __state;
} _G_fpos_t;
typedef struct
{
  __off64_t __pos;
  __mbstate_t __state;
} _G_fpos64_t;
typedef int _G_int16_t __attribute__ ((__mode__ (__HI__)));
typedef int _G_int32_t __attribute__ ((__mode__ (__SI__)));
typedef unsigned int _G_uint16_t __attribute__ ((__mode__ (__HI__)));
typedef unsigned int _G_uint32_t __attribute__ ((__mode__ (__SI__)));
typedef __builtin_va_list __gnuc_va_list;
struct _IO_jump_t; struct _IO_FILE;
typedef void _IO_lock_t;
struct _IO_marker {
  struct _IO_marker *_next;
  struct _IO_FILE *_sbuf;
  int _pos;
};
enum __codecvt_result
{
  __codecvt_ok,
  __codecvt_partial,
  __codecvt_error,
  __codecvt_noconv
};
struct _IO_FILE {
  int _flags;
  char* _IO_read_ptr;
  char* _IO_read_end;
  char* _IO_read_base;
  char* _IO_write_base;
  char* _IO_write_ptr;
  char* _IO_write_end;
  char* _IO_buf_base;
  char* _IO_buf_end;
  char *_IO_save_base;
  char *_IO_backup_base;
  char *_IO_save_end;
  struct _IO_marker *_markers;
  struct _IO_FILE *_chain;
  int _fileno;
  int _flags2;
  __off_t _old_offset;
  unsigned short _cur_column;
  signed char _vtable_offset;
  char _shortbuf[1];
  _IO_lock_t *_lock;
  __off64_t _offset;
  void *__pad1;
  void *__pad2;
  void *__pad3;
  void *__pad4;
  size_t __pad5;
  int _mode;
  char _unused2[15 * sizeof (int) - 4 * sizeof (void *) - sizeof (size_t)];
};
typedef struct _IO_FILE _IO_FILE;
struct _IO_FILE_plus;
extern struct _IO_FILE_plus _IO_2_1_stdin_;
extern struct _IO_FILE_plus _IO_2_1_stdout_;
extern struct _IO_FILE_plus _IO_2_1_stderr_;
typedef __ssize_t __io_read_fn (void *__cookie, char *__buf, size_t __nbytes);
typedef __ssize_t __io_write_fn (void *__cookie, __const char *__buf,
     size_t __n);
typedef int __io_seek_fn (void *__cookie, __off64_t *__pos, int __w);
typedef int __io_close_fn (void *__cookie);
extern int __underflow (_IO_FILE *);
extern int __uflow (_IO_FILE *);
extern int __overflow (_IO_FILE *, int);
extern int _IO_getc (_IO_FILE *__fp);
extern int _IO_putc (int __c, _IO_FILE *__fp);
extern int _IO_feof (_IO_FILE *__fp) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_ferror (_IO_FILE *__fp) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_peekc_locked (_IO_FILE *__fp);
extern void _IO_flockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
extern void _IO_funlockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_ftrylockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_vfscanf (_IO_FILE * __restrict, const char * __restrict,
   __gnuc_va_list, int *__restrict);
extern int _IO_vfprintf (_IO_FILE *__restrict, const char *__restrict,
    __gnuc_va_list);
extern __ssize_t _IO_padn (_IO_FILE *, int, __ssize_t);
extern size_t _IO_sgetn (_IO_FILE *, void *, size_t);
extern __off64_t _IO_seekoff (_IO_FILE *, __off64_t, int, int);
extern __off64_t _IO_seekpos (_IO_FILE *, __off64_t, int);
extern void _IO_free_backup_area (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
typedef __gnuc_va_list va_list;
typedef __off_t off_t;
typedef __ssize_t ssize_t;

typedef _G_fpos_t fpos_t;

extern struct _IO_FILE *stdin;
extern struct _IO_FILE *stdout;
extern struct _IO_FILE *stderr;

extern int remove (__const char *__filename) __attribute__ ((__nothrow__ , __leaf__));
extern int rename (__const char *__old, __const char *__new) __attribute__ ((__nothrow__ , __leaf__));

extern int renameat (int __oldfd, __const char *__old, int __newfd,
       __const char *__new) __attribute__ ((__nothrow__ , __leaf__));

extern FILE *tmpfile (void) ;
extern char *tmpnam (char *__s) __attribute__ ((__nothrow__ , __leaf__)) ;


extern char *tmpnam_r (char *__s) __attribute__ ((__nothrow__ , __leaf__)) ;
extern char *tempnam (__const char *__dir, __const char *__pfx)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

extern int fclose (FILE *__stream);
extern int fflush (FILE *__stream);

extern int fflush_unlocked (FILE *__stream);

extern FILE *fopen (__const char *__restrict __filename,
      __const char *__restrict __modes) ;
extern FILE *freopen (__const char *__restrict __filename,
        __const char *__restrict __modes,
        FILE *__restrict __stream) ;

extern FILE *fdopen (int __fd, __const char *__modes) __attribute__ ((__nothrow__ , __leaf__)) ;
extern FILE *fmemopen (void *__s, size_t __len, __const char *__modes)
  __attribute__ ((__nothrow__ , __leaf__)) ;
extern FILE *open_memstream (char **__bufloc, size_t *__sizeloc) __attribute__ ((__nothrow__ , __leaf__)) ;

extern void setbuf (FILE *__restrict __stream, char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__));
extern int setvbuf (FILE *__restrict __stream, char *__restrict __buf,
      int __modes, size_t __n) __attribute__ ((__nothrow__ , __leaf__));

extern void setbuffer (FILE *__restrict __stream, char *__restrict __buf,
         size_t __size) __attribute__ ((__nothrow__ , __leaf__));
extern void setlinebuf (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));

extern int fprintf (FILE *__restrict __stream,
      __const char *__restrict __format, ...);
extern int printf (__const char *__restrict __format, ...);
extern int sprintf (char *__restrict __s,
      __const char *__restrict __format, ...) __attribute__ ((__nothrow__));
extern int vfprintf (FILE *__restrict __s, __const char *__restrict __format,
       __gnuc_va_list __arg);
extern int vprintf (__const char *__restrict __format, __gnuc_va_list __arg);
extern int vsprintf (char *__restrict __s, __const char *__restrict __format,
       __gnuc_va_list __arg) __attribute__ ((__nothrow__));


extern int snprintf (char *__restrict __s, size_t __maxlen,
       __const char *__restrict __format, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 4)));
extern int vsnprintf (char *__restrict __s, size_t __maxlen,
        __const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 0)));

extern int vdprintf (int __fd, __const char *__restrict __fmt,
       __gnuc_va_list __arg)
     __attribute__ ((__format__ (__printf__, 2, 0)));
extern int dprintf (int __fd, __const char *__restrict __fmt, ...)
     __attribute__ ((__format__ (__printf__, 2, 3)));

extern int fscanf (FILE *__restrict __stream,
     __const char *__restrict __format, ...) ;
extern int scanf (__const char *__restrict __format, ...) ;
extern int sscanf (__const char *__restrict __s,
     __const char *__restrict __format, ...) __attribute__ ((__nothrow__ , __leaf__));
extern int fscanf (FILE *__restrict __stream, __const char *__restrict __format, ...) __asm__ ("" "__isoc99_fscanf") ;
extern int scanf (__const char *__restrict __format, ...) __asm__ ("" "__isoc99_scanf") ;
extern int sscanf (__const char *__restrict __s, __const char *__restrict __format, ...) __asm__ ("" "__isoc99_sscanf") __attribute__ ((__nothrow__ , __leaf__));


extern int vfscanf (FILE *__restrict __s, __const char *__restrict __format,
      __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 2, 0))) ;
extern int vscanf (__const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (__const char *__restrict __s,
      __const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__format__ (__scanf__, 2, 0)));
extern int vfscanf (FILE *__restrict __s, __const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vfscanf")
     __attribute__ ((__format__ (__scanf__, 2, 0))) ;
extern int vscanf (__const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vscanf")
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (__const char *__restrict __s, __const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vsscanf") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__format__ (__scanf__, 2, 0)));


extern int fgetc (FILE *__stream);
extern int getc (FILE *__stream);
extern int getchar (void);

extern int getc_unlocked (FILE *__stream);
extern int getchar_unlocked (void);
extern int fgetc_unlocked (FILE *__stream);

extern int fputc (int __c, FILE *__stream);
extern int putc (int __c, FILE *__stream);
extern int putchar (int __c);

extern int fputc_unlocked (int __c, FILE *__stream);
extern int putc_unlocked (int __c, FILE *__stream);
extern int putchar_unlocked (int __c);
extern int getw (FILE *__stream);
extern int putw (int __w, FILE *__stream);

extern char *fgets (char *__restrict __s, int __n, FILE *__restrict __stream)
     ;
extern char *gets (char *__s) ;

extern __ssize_t __getdelim (char **__restrict __lineptr,
          size_t *__restrict __n, int __delimiter,
          FILE *__restrict __stream) ;
extern __ssize_t getdelim (char **__restrict __lineptr,
        size_t *__restrict __n, int __delimiter,
        FILE *__restrict __stream) ;
extern __ssize_t getline (char **__restrict __lineptr,
       size_t *__restrict __n,
       FILE *__restrict __stream) ;

extern int fputs (__const char *__restrict __s, FILE *__restrict __stream);
extern int puts (__const char *__s);
extern int ungetc (int __c, FILE *__stream);
extern size_t fread (void *__restrict __ptr, size_t __size,
       size_t __n, FILE *__restrict __stream) ;
extern size_t fwrite (__const void *__restrict __ptr, size_t __size,
        size_t __n, FILE *__restrict __s);

extern size_t fread_unlocked (void *__restrict __ptr, size_t __size,
         size_t __n, FILE *__restrict __stream) ;
extern size_t fwrite_unlocked (__const void *__restrict __ptr, size_t __size,
          size_t __n, FILE *__restrict __stream);

extern int fseek (FILE *__stream, long int __off, int __whence);
extern long int ftell (FILE *__stream) ;
extern void rewind (FILE *__stream);

extern int fseeko (FILE *__stream, __off_t __off, int __whence);
extern __off_t ftello (FILE *__stream) ;

extern int fgetpos (FILE *__restrict __stream, fpos_t *__restrict __pos);
extern int fsetpos (FILE *__stream, __const fpos_t *__pos);


extern void clearerr (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int feof (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ferror (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;

extern void clearerr_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int feof_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ferror_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;

extern void perror (__const char *__s);

extern int sys_nerr;
extern __const char *__const sys_errlist[];
extern int fileno (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int fileno_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern FILE *popen (__const char *__command, __const char *__modes) ;
extern int pclose (FILE *__stream);
extern char *ctermid (char *__s) __attribute__ ((__nothrow__ , __leaf__));
extern void flockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int ftrylockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern void funlockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));



extern void *memcpy (void *__restrict __dest,
       __const void *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern void *memmove (void *__dest, __const void *__src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern void *memccpy (void *__restrict __dest, __const void *__restrict __src,
        int __c, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern void *memset (void *__s, int __c, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int memcmp (__const void *__s1, __const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern void *memchr (__const void *__s, int __c, size_t __n)
      __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));


extern char *strcpy (char *__restrict __dest, __const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strncpy (char *__restrict __dest,
        __const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strcat (char *__restrict __dest, __const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strncat (char *__restrict __dest, __const char *__restrict __src,
        size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int strcmp (__const char *__s1, __const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int strncmp (__const char *__s1, __const char *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int strcoll (__const char *__s1, __const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern size_t strxfrm (char *__restrict __dest,
         __const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));

typedef struct __locale_struct
{
  struct __locale_data *__locales[13];
  const unsigned short int *__ctype_b;
  const int *__ctype_tolower;
  const int *__ctype_toupper;
  const char *__names[13];
} *__locale_t;
typedef __locale_t locale_t;
extern int strcoll_l (__const char *__s1, __const char *__s2, __locale_t __l)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 3)));
extern size_t strxfrm_l (char *__dest, __const char *__src, size_t __n,
    __locale_t __l) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)));
extern char *strdup (__const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));
extern char *strndup (__const char *__string, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));

extern char *strchr (__const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern char *strrchr (__const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));


extern size_t strcspn (__const char *__s, __const char *__reject)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern size_t strspn (__const char *__s, __const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strpbrk (__const char *__s, __const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strstr (__const char *__haystack, __const char *__needle)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strtok (char *__restrict __s, __const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));

extern char *__strtok_r (char *__restrict __s,
    __const char *__restrict __delim,
    char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
extern char *strtok_r (char *__restrict __s, __const char *__restrict __delim,
         char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));

extern size_t strlen (__const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));

extern size_t strnlen (__const char *__string, size_t __maxlen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));

extern char *strerror (int __errnum) __attribute__ ((__nothrow__ , __leaf__));

extern int strerror_r (int __errnum, char *__buf, size_t __buflen) __asm__ ("" "__xpg_strerror_r") __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern char *strerror_l (int __errnum, __locale_t __l) __attribute__ ((__nothrow__ , __leaf__));
extern void __bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void bcopy (__const void *__src, void *__dest, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern void bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int bcmp (__const void *__s1, __const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *index (__const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern char *rindex (__const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern int ffs (int __i) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int strcasecmp (__const char *__s1, __const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int strncasecmp (__const char *__s1, __const char *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strsep (char **__restrict __stringp,
       __const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strsignal (int __sig) __attribute__ ((__nothrow__ , __leaf__));
extern char *__stpcpy (char *__restrict __dest, __const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *stpcpy (char *__restrict __dest, __const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *__stpncpy (char *__restrict __dest,
   __const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *stpncpy (char *__restrict __dest,
        __const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

typedef unsigned char uch;
typedef unsigned short ush;
typedef unsigned long ulg;
extern int method;
extern uch inbuf[];
extern uch outbuf[];
extern ush d_buf[];
extern uch window[];
   extern ush prev[];
extern unsigned insize;
extern unsigned inptr;
extern unsigned outcnt;
extern long bytes_in;
extern long bytes_out;
extern long header_bytes;
extern int ifd;
extern int ofd;
extern char ifname[];
extern char ofname[];
extern char *progname;
extern long time_stamp;
extern long ifile_size;
typedef int file_t;
extern int decrypt;
extern int exit_code;
extern int verbose;
extern int quiet;
extern int level;
extern int test;
extern int to_stdout;
extern int save_orig_name;
extern int zip (int in, int out);
extern int file_read (char *buf, unsigned size);
extern int unzip (int in, int out);
extern int check_zipfile (int in);
extern int unpack (int in, int out);
extern int unlzh (int in, int out);
void abort_gzip (void);
void lm_init (int pack_level, ush *flags);
ulg deflate (void);
void ct_init (ush *attr, int *method);
int ct_tally (int dist, int lc);
ulg flush_block (char *buf, ulg stored_len, int eof);
void bi_init (file_t zipfile);
void send_bits (int value, int length);
unsigned bi_reverse (unsigned value, int length);
void bi_windup (void);
void copy_block (char *buf, unsigned len, int header);
extern int (*read_buf) (char *buf, unsigned size);
extern int copy (int in, int out);
extern ulg updcrc (uch *s, unsigned n);
extern void clear_bufs (void);
extern int fill_inbuf (int eof_ok);
extern void flush_outbuf (void);
extern void flush_window (void);
extern void write_buf (int fd, voidp buf, unsigned cnt);
extern char *strlwr (char *s);
extern char *basename (char *fname);
extern void make_simple_name (char *name);
extern char *add_envopt (int *argcp, char ***argvp, char *env);
extern void error (char *m);
extern void warn (char *a, char *b);
extern void read_error (void);
extern void write_error (void);
extern void display_ratio (long num, long den, FILE *file);
extern voidp xmalloc (unsigned int size);
extern int inflate (void);
extern int maxbits;
extern int block_mode;
extern int lzw (int in, int out);
extern int unlzw (int in, int out);

enum
{
  _ISupper = ((0) < 8 ? ((1 << (0)) << 8) : ((1 << (0)) >> 8)),
  _ISlower = ((1) < 8 ? ((1 << (1)) << 8) : ((1 << (1)) >> 8)),
  _ISalpha = ((2) < 8 ? ((1 << (2)) << 8) : ((1 << (2)) >> 8)),
  _ISdigit = ((3) < 8 ? ((1 << (3)) << 8) : ((1 << (3)) >> 8)),
  _ISxdigit = ((4) < 8 ? ((1 << (4)) << 8) : ((1 << (4)) >> 8)),
  _ISspace = ((5) < 8 ? ((1 << (5)) << 8) : ((1 << (5)) >> 8)),
  _ISprint = ((6) < 8 ? ((1 << (6)) << 8) : ((1 << (6)) >> 8)),
  _ISgraph = ((7) < 8 ? ((1 << (7)) << 8) : ((1 << (7)) >> 8)),
  _ISblank = ((8) < 8 ? ((1 << (8)) << 8) : ((1 << (8)) >> 8)),
  _IScntrl = ((9) < 8 ? ((1 << (9)) << 8) : ((1 << (9)) >> 8)),
  _ISpunct = ((10) < 8 ? ((1 << (10)) << 8) : ((1 << (10)) >> 8)),
  _ISalnum = ((11) < 8 ? ((1 << (11)) << 8) : ((1 << (11)) >> 8))
};
extern __const unsigned short int **__ctype_b_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const));
extern __const __int32_t **__ctype_tolower_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const));
extern __const __int32_t **__ctype_toupper_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const));

extern int isalnum (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isalpha (int) __attribute__ ((__nothrow__ , __leaf__));
extern int iscntrl (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isdigit (int) __attribute__ ((__nothrow__ , __leaf__));
extern int islower (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isgraph (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isprint (int) __attribute__ ((__nothrow__ , __leaf__));
extern int ispunct (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isspace (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isupper (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isxdigit (int) __attribute__ ((__nothrow__ , __leaf__));
extern int tolower (int __c) __attribute__ ((__nothrow__ , __leaf__));
extern int toupper (int __c) __attribute__ ((__nothrow__ , __leaf__));


extern int isblank (int) __attribute__ ((__nothrow__ , __leaf__));

extern int isascii (int __c) __attribute__ ((__nothrow__ , __leaf__));
extern int toascii (int __c) __attribute__ ((__nothrow__ , __leaf__));
extern int _toupper (int) __attribute__ ((__nothrow__ , __leaf__));
extern int _tolower (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isalnum_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isalpha_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int iscntrl_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isdigit_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int islower_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isgraph_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isprint_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int ispunct_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isspace_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isupper_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isxdigit_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isblank_l (int, __locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int __tolower_l (int __c, __locale_t __l) __attribute__ ((__nothrow__ , __leaf__));
extern int tolower_l (int __c, __locale_t __l) __attribute__ ((__nothrow__ , __leaf__));
extern int __toupper_l (int __c, __locale_t __l) __attribute__ ((__nothrow__ , __leaf__));
extern int toupper_l (int __c, __locale_t __l) __attribute__ ((__nothrow__ , __leaf__));


typedef __u_char u_char;
typedef __u_short u_short;
typedef __u_int u_int;
typedef __u_long u_long;
typedef __quad_t quad_t;
typedef __u_quad_t u_quad_t;
typedef __fsid_t fsid_t;
typedef __loff_t loff_t;
typedef __ino_t ino_t;
typedef __dev_t dev_t;
typedef __gid_t gid_t;
typedef __mode_t mode_t;
typedef __nlink_t nlink_t;
typedef __uid_t uid_t;
typedef __pid_t pid_t;
typedef __id_t id_t;
typedef __daddr_t daddr_t;
typedef __caddr_t caddr_t;
typedef __key_t key_t;

typedef __clock_t clock_t;



typedef __time_t time_t;


typedef __clockid_t clockid_t;
typedef __timer_t timer_t;
typedef unsigned long int ulong;
typedef unsigned short int ushort;
typedef unsigned int uint;
typedef int int8_t __attribute__ ((__mode__ (__QI__)));
typedef int int16_t __attribute__ ((__mode__ (__HI__)));
typedef int int32_t __attribute__ ((__mode__ (__SI__)));
typedef int int64_t __attribute__ ((__mode__ (__DI__)));
typedef unsigned int u_int8_t __attribute__ ((__mode__ (__QI__)));
typedef unsigned int u_int16_t __attribute__ ((__mode__ (__HI__)));
typedef unsigned int u_int32_t __attribute__ ((__mode__ (__SI__)));
typedef unsigned int u_int64_t __attribute__ ((__mode__ (__DI__)));
typedef int register_t __attribute__ ((__mode__ (__word__)));
typedef int __sig_atomic_t;
typedef struct
  {
    unsigned long int __val[(1024 / (8 * sizeof (unsigned long int)))];
  } __sigset_t;
typedef __sigset_t sigset_t;
struct timespec
  {
    __time_t tv_sec;
    long int tv_nsec;
  };
struct timeval
  {
    __time_t tv_sec;
    __suseconds_t tv_usec;
  };
typedef __suseconds_t suseconds_t;
typedef long int __fd_mask;
typedef struct
  {
    __fd_mask __fds_bits[1024 / (8 * (int) sizeof (__fd_mask))];
  } fd_set;
typedef __fd_mask fd_mask;

extern int select (int __nfds, fd_set *__restrict __readfds,
     fd_set *__restrict __writefds,
     fd_set *__restrict __exceptfds,
     struct timeval *__restrict __timeout);
extern int pselect (int __nfds, fd_set *__restrict __readfds,
      fd_set *__restrict __writefds,
      fd_set *__restrict __exceptfds,
      const struct timespec *__restrict __timeout,
      const __sigset_t *__restrict __sigmask);


__extension__
extern unsigned int gnu_dev_major (unsigned long long int __dev)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
__extension__
extern unsigned int gnu_dev_minor (unsigned long long int __dev)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
__extension__
extern unsigned long long int gnu_dev_makedev (unsigned int __major,
            unsigned int __minor)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

typedef __blksize_t blksize_t;
typedef __blkcnt_t blkcnt_t;
typedef __fsblkcnt_t fsblkcnt_t;
typedef __fsfilcnt_t fsfilcnt_t;
typedef unsigned long int pthread_t;
typedef union
{
  char __size[56];
  long int __align;
} pthread_attr_t;
typedef struct __pthread_internal_list
{
  struct __pthread_internal_list *__prev;
  struct __pthread_internal_list *__next;
} __pthread_list_t;
typedef union
{
  struct __pthread_mutex_s
  {
    int __lock;
    unsigned int __count;
    int __owner;
    unsigned int __nusers;
    int __kind;
    int __spins;
    __pthread_list_t __list;
  } __data;
  char __size[40];
  long int __align;
} pthread_mutex_t;
typedef union
{
  char __size[4];
  int __align;
} pthread_mutexattr_t;
typedef union
{
  struct
  {
    int __lock;
    unsigned int __futex;
    __extension__ unsigned long long int __total_seq;
    __extension__ unsigned long long int __wakeup_seq;
    __extension__ unsigned long long int __woken_seq;
    void *__mutex;
    unsigned int __nwaiters;
    unsigned int __broadcast_seq;
  } __data;
  char __size[48];
  __extension__ long long int __align;
} pthread_cond_t;
typedef union
{
  char __size[4];
  int __align;
} pthread_condattr_t;
typedef unsigned int pthread_key_t;
typedef int pthread_once_t;
typedef union
{
  struct
  {
    int __lock;
    unsigned int __nr_readers;
    unsigned int __readers_wakeup;
    unsigned int __writer_wakeup;
    unsigned int __nr_readers_queued;
    unsigned int __nr_writers_queued;
    int __writer;
    int __shared;
    unsigned long int __pad1;
    unsigned long int __pad2;
    unsigned int __flags;
  } __data;
  char __size[56];
  long int __align;
} pthread_rwlock_t;
typedef union
{
  char __size[8];
  long int __align;
} pthread_rwlockattr_t;
typedef volatile int pthread_spinlock_t;
typedef union
{
  char __size[32];
  long int __align;
} pthread_barrier_t;
typedef union
{
  char __size[4];
  int __align;
} pthread_barrierattr_t;


extern int __sigismember (__const __sigset_t *, int);
extern int __sigaddset (__sigset_t *, int);
extern int __sigdelset (__sigset_t *, int);

typedef __sig_atomic_t sig_atomic_t;

typedef union sigval
  {
    int sival_int;
    void *sival_ptr;
  } sigval_t;
typedef struct siginfo
  {
    int si_signo;
    int si_errno;
    int si_code;
    union
      {
 int _pad[((128 / sizeof (int)) - 4)];
 struct
   {
     __pid_t si_pid;
     __uid_t si_uid;
   } _kill;
 struct
   {
     int si_tid;
     int si_overrun;
     sigval_t si_sigval;
   } _timer;
 struct
   {
     __pid_t si_pid;
     __uid_t si_uid;
     sigval_t si_sigval;
   } _rt;
 struct
   {
     __pid_t si_pid;
     __uid_t si_uid;
     int si_status;
     __clock_t si_utime;
     __clock_t si_stime;
   } _sigchld;
 struct
   {
     void *si_addr;
   } _sigfault;
 struct
   {
     long int si_band;
     int si_fd;
   } _sigpoll;
      } _sifields;
  } siginfo_t;
enum
{
  SI_ASYNCNL = -60,
  SI_TKILL = -6,
  SI_SIGIO,
  SI_ASYNCIO,
  SI_MESGQ,
  SI_TIMER,
  SI_QUEUE,
  SI_USER,
  SI_KERNEL = 0x80
};
enum
{
  ILL_ILLOPC = 1,
  ILL_ILLOPN,
  ILL_ILLADR,
  ILL_ILLTRP,
  ILL_PRVOPC,
  ILL_PRVREG,
  ILL_COPROC,
  ILL_BADSTK
};
enum
{
  FPE_INTDIV = 1,
  FPE_INTOVF,
  FPE_FLTDIV,
  FPE_FLTOVF,
  FPE_FLTUND,
  FPE_FLTRES,
  FPE_FLTINV,
  FPE_FLTSUB
};
enum
{
  SEGV_MAPERR = 1,
  SEGV_ACCERR
};
enum
{
  BUS_ADRALN = 1,
  BUS_ADRERR,
  BUS_OBJERR
};
enum
{
  TRAP_BRKPT = 1,
  TRAP_TRACE
};
enum
{
  CLD_EXITED = 1,
  CLD_KILLED,
  CLD_DUMPED,
  CLD_TRAPPED,
  CLD_STOPPED,
  CLD_CONTINUED
};
enum
{
  POLL_IN = 1,
  POLL_OUT,
  POLL_MSG,
  POLL_ERR,
  POLL_PRI,
  POLL_HUP
};
typedef struct sigevent
  {
    sigval_t sigev_value;
    int sigev_signo;
    int sigev_notify;
    union
      {
 int _pad[((64 / sizeof (int)) - 4)];
 __pid_t _tid;
 struct
   {
     void (*_function) (sigval_t);
     void *_attribute;
   } _sigev_thread;
      } _sigev_un;
  } sigevent_t;
enum
{
  SIGEV_SIGNAL = 0,
  SIGEV_NONE,
  SIGEV_THREAD,
  SIGEV_THREAD_ID = 4
};
typedef void (*__sighandler_t) (int);
extern __sighandler_t __sysv_signal (int __sig, __sighandler_t __handler)
     __attribute__ ((__nothrow__ , __leaf__));

extern __sighandler_t signal (int __sig, __sighandler_t __handler)
     __attribute__ ((__nothrow__ , __leaf__));

extern int kill (__pid_t __pid, int __sig) __attribute__ ((__nothrow__ , __leaf__));
extern int killpg (__pid_t __pgrp, int __sig) __attribute__ ((__nothrow__ , __leaf__));

extern int raise (int __sig) __attribute__ ((__nothrow__ , __leaf__));

extern __sighandler_t ssignal (int __sig, __sighandler_t __handler)
     __attribute__ ((__nothrow__ , __leaf__));
extern int gsignal (int __sig) __attribute__ ((__nothrow__ , __leaf__));
extern void psignal (int __sig, __const char *__s);
extern void psiginfo (__const siginfo_t *__pinfo, __const char *__s);
extern int __sigpause (int __sig_or_mask, int __is_sig);
extern int sigblock (int __mask) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern int sigsetmask (int __mask) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern int siggetmask (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
typedef __sighandler_t sig_t;
extern int sigemptyset (sigset_t *__set) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigfillset (sigset_t *__set) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigaddset (sigset_t *__set, int __signo) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigdelset (sigset_t *__set, int __signo) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigismember (__const sigset_t *__set, int __signo)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
struct sigaction
  {
    union
      {
 __sighandler_t sa_handler;
 void (*sa_sigaction) (int, siginfo_t *, void *);
      }
    __sigaction_handler;
    __sigset_t sa_mask;
    int sa_flags;
    void (*sa_restorer) (void);
  };
extern int sigprocmask (int __how, __const sigset_t *__restrict __set,
   sigset_t *__restrict __oset) __attribute__ ((__nothrow__ , __leaf__));
extern int sigsuspend (__const sigset_t *__set) __attribute__ ((__nonnull__ (1)));
extern int sigaction (int __sig, __const struct sigaction *__restrict __act,
        struct sigaction *__restrict __oact) __attribute__ ((__nothrow__ , __leaf__));
extern int sigpending (sigset_t *__set) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigwait (__const sigset_t *__restrict __set, int *__restrict __sig)
     __attribute__ ((__nonnull__ (1, 2)));
extern int sigwaitinfo (__const sigset_t *__restrict __set,
   siginfo_t *__restrict __info) __attribute__ ((__nonnull__ (1)));
extern int sigtimedwait (__const sigset_t *__restrict __set,
    siginfo_t *__restrict __info,
    __const struct timespec *__restrict __timeout)
     __attribute__ ((__nonnull__ (1)));
extern int sigqueue (__pid_t __pid, int __sig, __const union sigval __val)
     __attribute__ ((__nothrow__ , __leaf__));
extern __const char *__const _sys_siglist[65];
extern __const char *__const sys_siglist[65];
struct sigvec
  {
    __sighandler_t sv_handler;
    int sv_mask;
    int sv_flags;
  };
extern int sigvec (int __sig, __const struct sigvec *__vec,
     struct sigvec *__ovec) __attribute__ ((__nothrow__ , __leaf__));
struct _fpreg
{
  unsigned short significand[4];
  unsigned short exponent;
};
struct _fpxreg
{
  unsigned short significand[4];
  unsigned short exponent;
  unsigned short padding[3];
};
struct _xmmreg
{
  __uint32_t element[4];
};
struct _fpstate
{
  __uint16_t cwd;
  __uint16_t swd;
  __uint16_t ftw;
  __uint16_t fop;
  __uint64_t rip;
  __uint64_t rdp;
  __uint32_t mxcsr;
  __uint32_t mxcr_mask;
  struct _fpxreg _st[8];
  struct _xmmreg _xmm[16];
  __uint32_t padding[24];
};
struct sigcontext
{
  unsigned long r8;
  unsigned long r9;
  unsigned long r10;
  unsigned long r11;
  unsigned long r12;
  unsigned long r13;
  unsigned long r14;
  unsigned long r15;
  unsigned long rdi;
  unsigned long rsi;
  unsigned long rbp;
  unsigned long rbx;
  unsigned long rdx;
  unsigned long rax;
  unsigned long rcx;
  unsigned long rsp;
  unsigned long rip;
  unsigned long eflags;
  unsigned short cs;
  unsigned short gs;
  unsigned short fs;
  unsigned short __pad0;
  unsigned long err;
  unsigned long trapno;
  unsigned long oldmask;
  unsigned long cr2;
  struct _fpstate * fpstate;
  unsigned long __reserved1 [8];
};
extern int sigreturn (struct sigcontext *__scp) __attribute__ ((__nothrow__ , __leaf__));
extern int siginterrupt (int __sig, int __interrupt) __attribute__ ((__nothrow__ , __leaf__));
struct sigstack
  {
    void *ss_sp;
    int ss_onstack;
  };
enum
{
  SS_ONSTACK = 1,
  SS_DISABLE
};
typedef struct sigaltstack
  {
    void *ss_sp;
    int ss_flags;
    size_t ss_size;
  } stack_t;
typedef long int greg_t;
typedef greg_t gregset_t[23];
struct _libc_fpxreg
{
  unsigned short int significand[4];
  unsigned short int exponent;
  unsigned short int padding[3];
};
struct _libc_xmmreg
{
  __uint32_t element[4];
};
struct _libc_fpstate
{
  __uint16_t cwd;
  __uint16_t swd;
  __uint16_t ftw;
  __uint16_t fop;
  __uint64_t rip;
  __uint64_t rdp;
  __uint32_t mxcsr;
  __uint32_t mxcr_mask;
  struct _libc_fpxreg _st[8];
  struct _libc_xmmreg _xmm[16];
  __uint32_t padding[24];
};
typedef struct _libc_fpstate *fpregset_t;
typedef struct
  {
    gregset_t gregs;
    fpregset_t fpregs;
    unsigned long __reserved1 [8];
} mcontext_t;
typedef struct ucontext
  {
    unsigned long int uc_flags;
    struct ucontext *uc_link;
    stack_t uc_stack;
    mcontext_t uc_mcontext;
    __sigset_t uc_sigmask;
    struct _libc_fpstate __fpregs_mem;
  } ucontext_t;
extern int sigstack (struct sigstack *__ss, struct sigstack *__oss)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern int sigaltstack (__const struct sigaltstack *__restrict __ss,
   struct sigaltstack *__restrict __oss) __attribute__ ((__nothrow__ , __leaf__));
extern int pthread_sigmask (int __how,
       __const __sigset_t *__restrict __newmask,
       __sigset_t *__restrict __oldmask)__attribute__ ((__nothrow__ , __leaf__));
extern int pthread_kill (pthread_t __threadid, int __signo) __attribute__ ((__nothrow__ , __leaf__));
extern int __libc_current_sigrtmin (void) __attribute__ ((__nothrow__ , __leaf__));
extern int __libc_current_sigrtmax (void) __attribute__ ((__nothrow__ , __leaf__));


struct stat
  {
    __dev_t st_dev;
    __ino_t st_ino;
    __nlink_t st_nlink;
    __mode_t st_mode;
    __uid_t st_uid;
    __gid_t st_gid;
    int __pad0;
    __dev_t st_rdev;
    __off_t st_size;
    __blksize_t st_blksize;
    __blkcnt_t st_blocks;
    struct timespec st_atim;
    struct timespec st_mtim;
    struct timespec st_ctim;
    long int __unused[3];
  };
extern int stat (__const char *__restrict __file,
   struct stat *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int fstat (int __fd, struct stat *__buf) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int fstatat (int __fd, __const char *__restrict __file,
      struct stat *__restrict __buf, int __flag)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
extern int lstat (__const char *__restrict __file,
    struct stat *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int chmod (__const char *__file, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int lchmod (__const char *__file, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int fchmod (int __fd, __mode_t __mode) __attribute__ ((__nothrow__ , __leaf__));
extern int fchmodat (int __fd, __const char *__file, __mode_t __mode,
       int __flag)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2))) ;
extern __mode_t umask (__mode_t __mask) __attribute__ ((__nothrow__ , __leaf__));
extern int mkdir (__const char *__path, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int mkdirat (int __fd, __const char *__path, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int mknod (__const char *__path, __mode_t __mode, __dev_t __dev)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int mknodat (int __fd, __const char *__path, __mode_t __mode,
      __dev_t __dev) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int mkfifo (__const char *__path, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int mkfifoat (int __fd, __const char *__path, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int utimensat (int __fd, __const char *__path,
        __const struct timespec __times[2],
        int __flags)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int futimens (int __fd, __const struct timespec __times[2]) __attribute__ ((__nothrow__ , __leaf__));
extern int __fxstat (int __ver, int __fildes, struct stat *__stat_buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));
extern int __xstat (int __ver, __const char *__filename,
      struct stat *__stat_buf) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
extern int __lxstat (int __ver, __const char *__filename,
       struct stat *__stat_buf) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
extern int __fxstatat (int __ver, int __fildes, __const char *__filename,
         struct stat *__stat_buf, int __flag)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4)));
extern int __xmknod (int __ver, __const char *__path, __mode_t __mode,
       __dev_t *__dev) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)));
extern int __xmknodat (int __ver, int __fd, __const char *__path,
         __mode_t __mode, __dev_t *__dev)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 5)));


extern int *__errno_location (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

static file_t zfile;
static unsigned short bi_buf;
static int bi_valid;
int (*read_buf) (char *buf, unsigned size);
void bi_init (zipfile)
    file_t zipfile;
{
    zfile = zipfile;
    bi_buf = 0;
    bi_valid = 0;
    if (zfile != (-1)) {
 read_buf = file_read;
    }
}
void send_bits(value, length)
    int value;
    int length;
{
    if (bi_valid > (int)(8 * 2*sizeof(char)) - length) {
        bi_buf |= (value << bi_valid);
        { if (outcnt < 16384 -2) { outbuf[outcnt++] = (uch) ((bi_buf) & 0xff); outbuf[outcnt++] = (uch) ((ush)(bi_buf) >> 8); } else { {outbuf[outcnt++]=(uch)((uch)((bi_buf) & 0xff)); if (outcnt==16384) flush_outbuf();}; {outbuf[outcnt++]=(uch)((uch)((ush)(bi_buf) >> 8)); if (outcnt==16384) flush_outbuf();}; } };
        bi_buf = (ush)value >> ((8 * 2*sizeof(char)) - bi_valid);
        bi_valid += length - (8 * 2*sizeof(char));
    } else {
        bi_buf |= value << bi_valid;
        bi_valid += length;
    }
}
unsigned bi_reverse(code, len)
    unsigned code;
    int len;
{
    register unsigned res = 0;
    do {
        res |= code & 1;
        code >>= 1, res <<= 1;
    } while (--len > 0);
    return res >> 1;
}
void bi_windup()
{
    if (bi_valid > 8) {
        { if (outcnt < 16384 -2) { outbuf[outcnt++] = (uch) ((bi_buf) & 0xff); outbuf[outcnt++] = (uch) ((ush)(bi_buf) >> 8); } else { {outbuf[outcnt++]=(uch)((uch)((bi_buf) & 0xff)); if (outcnt==16384) flush_outbuf();}; {outbuf[outcnt++]=(uch)((uch)((ush)(bi_buf) >> 8)); if (outcnt==16384) flush_outbuf();}; } };
    } else if (bi_valid > 0) {
        {outbuf[outcnt++]=(uch)(bi_buf); if (outcnt==16384) flush_outbuf();};
    }
    bi_buf = 0;
    bi_valid = 0;
}
void copy_block(buf, len, header)
    char *buf;
    unsigned len;
    int header;
{
    bi_windup();
    if (header) {
        { if (outcnt < 16384 -2) { outbuf[outcnt++] = (uch) (((ush)len) & 0xff); outbuf[outcnt++] = (uch) ((ush)((ush)len) >> 8); } else { {outbuf[outcnt++]=(uch)((uch)(((ush)len) & 0xff)); if (outcnt==16384) flush_outbuf();}; {outbuf[outcnt++]=(uch)((uch)((ush)((ush)len) >> 8)); if (outcnt==16384) flush_outbuf();}; } };
        { if (outcnt < 16384 -2) { outbuf[outcnt++] = (uch) (((ush)~len) & 0xff); outbuf[outcnt++] = (uch) ((ush)((ush)~len) >> 8); } else { {outbuf[outcnt++]=(uch)((uch)(((ush)~len) & 0xff)); if (outcnt==16384) flush_outbuf();}; {outbuf[outcnt++]=(uch)((uch)((ush)((ush)~len) >> 8)); if (outcnt==16384) flush_outbuf();}; } };
    }
    while (len--) {
 {outbuf[outcnt++]=(uch)(*buf++); if (outcnt==16384) flush_outbuf();};
    }
}
typedef ush Pos;
typedef unsigned IPos;
ulg window_size = (ulg)2*0x8000;
long block_start;
static unsigned ins_h;
unsigned int prev_length;
      unsigned strstart;
      unsigned match_start;
static int eofile;
static unsigned lookahead;
unsigned max_chain_length;
static unsigned int max_lazy_match;
static int compr_level;
unsigned good_match;
typedef struct config {
   ush good_length;
   ush max_lazy;
   ush nice_length;
   ush max_chain;
} config;
  int nice_match;
static config configuration_table[10] = {
        {0, 0, 0, 0},
        {4, 4, 8, 4},
        {4, 5, 16, 8},
        {4, 6, 32, 32},
        {4, 4, 16, 16},
        {8, 16, 32, 32},
        {8, 16, 128, 128},
        {8, 32, 128, 256},
        {32, 128, 258, 1024},
        {32, 258, 258, 4096}};
static void fill_window (void);
static ulg deflate_fast (void);
      int longest_match (IPos cur_match);
void lm_init (pack_level, flags)
    int pack_level;
    ush *flags;
{
    register unsigned j;
    if (pack_level < 1 || pack_level > 9) error("bad pack level");
    compr_level = pack_level;
    memset ((voidp)((char*)(prev+0x8000)), 0, ((unsigned)(1<<15)*sizeof(*(prev+0x8000))));
    max_lazy_match = configuration_table[pack_level].max_lazy;
    good_match = configuration_table[pack_level].good_length;
    nice_match = configuration_table[pack_level].nice_length;
    max_chain_length = configuration_table[pack_level].max_chain;
    if (pack_level == 1) {
       *flags |= 4;
    } else if (pack_level == 9) {
       *flags |= 2;
    }
    strstart = 0;
    block_start = 0L;
    lookahead = read_buf((char*)window,
    sizeof(int) <= 2 ? (unsigned)0x8000 : 2*0x8000);
    if (lookahead == 0 || lookahead == (unsigned)(-1)) {
       eofile = 1, lookahead = 0;
       return;
    }
    eofile = 0;
    while (lookahead < (258 +3 +1) && !eofile) fill_window();
    ins_h = 0;
    for (j=0; j<3 -1; j++) (ins_h = (((ins_h)<<((15 +3 -1)/3)) ^ (window[j])) & ((unsigned)(1<<15)-1));
}
int longest_match(cur_match)
    IPos cur_match;
{
    unsigned chain_length = max_chain_length;
    register uch *scan = window + strstart;
    register uch *match;
    register int len;
    int best_len = prev_length;
    IPos limit = strstart > (IPos)(0x8000 -(258 +3 +1)) ? strstart - (IPos)(0x8000 -(258 +3 +1)) : 0;
    register uch *strend = window + strstart + 258;
    register uch scan_end1 = scan[best_len-1];
    register uch scan_end = scan[best_len];
    if (prev_length >= good_match) {
        chain_length >>= 2;
    }
    ;
    do {
        ;
        match = window + cur_match;
        if (match[best_len] != scan_end ||
            match[best_len-1] != scan_end1 ||
            *match != *scan ||
            *++match != scan[1]) continue;
        scan += 2, match++;
        do {
        } while (*++scan == *++match && *++scan == *++match &&
                 *++scan == *++match && *++scan == *++match &&
                 *++scan == *++match && *++scan == *++match &&
                 *++scan == *++match && *++scan == *++match &&
                 scan < strend);
        len = 258 - (int)(strend - scan);
        scan = strend - 258;
        if (len > best_len) {
            match_start = cur_match;
            best_len = len;
            if (len >= nice_match) break;
            scan_end1 = scan[best_len-1];
            scan_end = scan[best_len];
        }
    } while ((cur_match = prev[cur_match & (0x8000 -1)]) > limit
      && --chain_length != 0);
    return best_len;
}
static void fill_window()
{
    register unsigned n, m;
    unsigned more = (unsigned)(window_size - (ulg)lookahead - (ulg)strstart);
    if (more == (unsigned)(-1)) {
        more--;
    } else if (strstart >= 0x8000 +(0x8000 -(258 +3 +1))) {
        ;
        memcpy((char*)window, (char*)window+0x8000, (unsigned)0x8000);
        match_start -= 0x8000;
        strstart -= 0x8000;
        block_start -= (long) 0x8000;
        for (n = 0; n < (unsigned)(1<<15); n++) {
            m = (prev+0x8000)[n];
            (prev+0x8000)[n] = (Pos)(m >= 0x8000 ? m-0x8000 : 0);
        }
        for (n = 0; n < 0x8000; n++) {
            m = prev[n];
            prev[n] = (Pos)(m >= 0x8000 ? m-0x8000 : 0);
        }
        more += 0x8000;
    }
    if (!eofile) {
        n = read_buf((char*)window+strstart+lookahead, more);
        if (n == 0 || n == (unsigned)(-1)) {
            eofile = 1;
        } else {
            lookahead += n;
        }
    }
}
static ulg deflate_fast()
{
    IPos hash_head;
    int flush;
    unsigned match_length = 0;
    prev_length = 3 -1;
    while (lookahead != 0) {
        ((ins_h = (((ins_h)<<((15 +3 -1)/3)) ^ (window[(strstart) + 3 -1])) & ((unsigned)(1<<15)-1)), prev[(strstart) & (0x8000 -1)] = hash_head = (prev+0x8000)[ins_h], (prev+0x8000)[ins_h] = (strstart));
        if (hash_head != 0 && strstart - hash_head <= (0x8000 -(258 +3 +1))) {
            match_length = longest_match (hash_head);
            if (match_length > lookahead) match_length = lookahead;
        }
        if (match_length >= 3) {
            ;
            flush = ct_tally(strstart-match_start, match_length - 3);
            lookahead -= match_length;
            if (match_length <= max_lazy_match) {
                match_length--;
                do {
                    strstart++;
                    ((ins_h = (((ins_h)<<((15 +3 -1)/3)) ^ (window[(strstart) + 3 -1])) & ((unsigned)(1<<15)-1)), prev[(strstart) & (0x8000 -1)] = hash_head = (prev+0x8000)[ins_h], (prev+0x8000)[ins_h] = (strstart));
                } while (--match_length != 0);
         strstart++;
            } else {
         strstart += match_length;
         match_length = 0;
         ins_h = window[strstart];
         (ins_h = (((ins_h)<<((15 +3 -1)/3)) ^ (window[strstart+1])) & ((unsigned)(1<<15)-1));
            }
        } else {
            ;
            flush = ct_tally (0, window[strstart]);
            lookahead--;
     strstart++;
        }
        if (flush) flush_block(block_start >= 0L ? (char*)&window[(unsigned)block_start] : (char*)((void *)0), (long)strstart - block_start, (0)), block_start = strstart;
        while (lookahead < (258 +3 +1) && !eofile) fill_window();
    }
    return flush_block(block_start >= 0L ? (char*)&window[(unsigned)block_start] : (char*)((void *)0), (long)strstart - block_start, (1));
}
ulg deflate()
{
    IPos hash_head;
    IPos prev_match;
    int flush;
    int match_available = 0;
    register unsigned match_length = 3 -1;
    if (compr_level <= 3) return deflate_fast();
    while (lookahead != 0) {
        ((ins_h = (((ins_h)<<((15 +3 -1)/3)) ^ (window[(strstart) + 3 -1])) & ((unsigned)(1<<15)-1)), prev[(strstart) & (0x8000 -1)] = hash_head = (prev+0x8000)[ins_h], (prev+0x8000)[ins_h] = (strstart));
        prev_length = match_length, prev_match = match_start;
        match_length = 3 -1;
        if (hash_head != 0 && prev_length < max_lazy_match &&
            strstart - hash_head <= (0x8000 -(258 +3 +1))) {
            match_length = longest_match (hash_head);
            if (match_length > lookahead) match_length = lookahead;
            if (match_length == 3 && strstart-match_start > 4096){
                match_length--;
            }
        }
        if (prev_length >= 3 && match_length <= prev_length) {
            ;
            flush = ct_tally(strstart-1-prev_match, prev_length - 3);
            lookahead -= prev_length-1;
            prev_length -= 2;
            do {
                strstart++;
                ((ins_h = (((ins_h)<<((15 +3 -1)/3)) ^ (window[(strstart) + 3 -1])) & ((unsigned)(1<<15)-1)), prev[(strstart) & (0x8000 -1)] = hash_head = (prev+0x8000)[ins_h], (prev+0x8000)[ins_h] = (strstart));
            } while (--prev_length != 0);
            match_available = 0;
            match_length = 3 -1;
            strstart++;
            if (flush) flush_block(block_start >= 0L ? (char*)&window[(unsigned)block_start] : (char*)((void *)0), (long)strstart - block_start, (0)), block_start = strstart;
        } else if (match_available) {
            ;
            if (ct_tally (0, window[strstart-1])) {
                flush_block(block_start >= 0L ? (char*)&window[(unsigned)block_start] : (char*)((void *)0), (long)strstart - block_start, (0)), block_start = strstart;
            }
            strstart++;
            lookahead--;
        } else {
            match_available = 1;
            strstart++;
            lookahead--;
        }
        ;
        while (lookahead < (258 +3 +1) && !eofile) fill_window();
    }
    if (match_available) ct_tally (0, window[strstart-1]);
    return flush_block(block_start >= 0L ? (char*)&window[(unsigned)block_start] : (char*)((void *)0), (long)strstart - block_start, (1));
}
typedef int wchar_t;

union wait
  {
    int w_status;
    struct
      {
 unsigned int __w_termsig:7;
 unsigned int __w_coredump:1;
 unsigned int __w_retcode:8;
 unsigned int:16;
      } __wait_terminated;
    struct
      {
 unsigned int __w_stopval:8;
 unsigned int __w_stopsig:8;
 unsigned int:16;
      } __wait_stopped;
  };
typedef union
  {
    union wait *__uptr;
    int *__iptr;
  } __WAIT_STATUS __attribute__ ((__transparent_union__));

typedef struct
  {
    int quot;
    int rem;
  } div_t;
typedef struct
  {
    long int quot;
    long int rem;
  } ldiv_t;


__extension__ typedef struct
  {
    long long int quot;
    long long int rem;
  } lldiv_t;

extern size_t __ctype_get_mb_cur_max (void) __attribute__ ((__nothrow__ , __leaf__)) ;

extern double atof (__const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;
extern int atoi (__const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;
extern long int atol (__const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;


__extension__ extern long long int atoll (__const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;


extern double strtod (__const char *__restrict __nptr,
        char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;


extern float strtof (__const char *__restrict __nptr,
       char **__restrict __endptr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern long double strtold (__const char *__restrict __nptr,
       char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;


extern long int strtol (__const char *__restrict __nptr,
   char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern unsigned long int strtoul (__const char *__restrict __nptr,
      char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;

__extension__
extern long long int strtoq (__const char *__restrict __nptr,
        char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
__extension__
extern unsigned long long int strtouq (__const char *__restrict __nptr,
           char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;

__extension__
extern long long int strtoll (__const char *__restrict __nptr,
         char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
__extension__
extern unsigned long long int strtoull (__const char *__restrict __nptr,
     char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;

extern char *l64a (long int __n) __attribute__ ((__nothrow__ , __leaf__)) ;
extern long int a64l (__const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;
extern long int random (void) __attribute__ ((__nothrow__ , __leaf__));
extern void srandom (unsigned int __seed) __attribute__ ((__nothrow__ , __leaf__));
extern char *initstate (unsigned int __seed, char *__statebuf,
   size_t __statelen) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern char *setstate (char *__statebuf) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
struct random_data
  {
    int32_t *fptr;
    int32_t *rptr;
    int32_t *state;
    int rand_type;
    int rand_deg;
    int rand_sep;
    int32_t *end_ptr;
  };
extern int random_r (struct random_data *__restrict __buf,
       int32_t *__restrict __result) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int srandom_r (unsigned int __seed, struct random_data *__buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int initstate_r (unsigned int __seed, char *__restrict __statebuf,
   size_t __statelen,
   struct random_data *__restrict __buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)));
extern int setstate_r (char *__restrict __statebuf,
         struct random_data *__restrict __buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern int rand (void) __attribute__ ((__nothrow__ , __leaf__));
extern void srand (unsigned int __seed) __attribute__ ((__nothrow__ , __leaf__));

extern int rand_r (unsigned int *__seed) __attribute__ ((__nothrow__ , __leaf__));
extern double drand48 (void) __attribute__ ((__nothrow__ , __leaf__));
extern double erand48 (unsigned short int __xsubi[3]) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern long int lrand48 (void) __attribute__ ((__nothrow__ , __leaf__));
extern long int nrand48 (unsigned short int __xsubi[3])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern long int mrand48 (void) __attribute__ ((__nothrow__ , __leaf__));
extern long int jrand48 (unsigned short int __xsubi[3])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void srand48 (long int __seedval) __attribute__ ((__nothrow__ , __leaf__));
extern unsigned short int *seed48 (unsigned short int __seed16v[3])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void lcong48 (unsigned short int __param[7]) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
struct drand48_data
  {
    unsigned short int __x[3];
    unsigned short int __old_x[3];
    unsigned short int __c;
    unsigned short int __init;
    unsigned long long int __a;
  };
extern int drand48_r (struct drand48_data *__restrict __buffer,
        double *__restrict __result) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int erand48_r (unsigned short int __xsubi[3],
        struct drand48_data *__restrict __buffer,
        double *__restrict __result) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int lrand48_r (struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int nrand48_r (unsigned short int __xsubi[3],
        struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int mrand48_r (struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int jrand48_r (unsigned short int __xsubi[3],
        struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int srand48_r (long int __seedval, struct drand48_data *__buffer)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int seed48_r (unsigned short int __seed16v[3],
       struct drand48_data *__buffer) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int lcong48_r (unsigned short int __param[7],
        struct drand48_data *__buffer)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;


extern void *realloc (void *__ptr, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__warn_unused_result__));
extern void free (void *__ptr) __attribute__ ((__nothrow__ , __leaf__));

extern void cfree (void *__ptr) __attribute__ ((__nothrow__ , __leaf__));

extern void *alloca (size_t __size) __attribute__ ((__nothrow__ , __leaf__));

extern void *valloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern int posix_memalign (void **__memptr, size_t __alignment, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;

extern void abort (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern int atexit (void (*__func) (void)) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern int on_exit (void (*__func) (int __status, void *__arg), void *__arg)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern void exit (int __status) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));


extern void _Exit (int __status) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));


extern char *getenv (__const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;

extern char *__secure_getenv (__const char *__name)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int putenv (char *__string) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int setenv (__const char *__name, __const char *__value, int __replace)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int unsetenv (__const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int clearenv (void) __attribute__ ((__nothrow__ , __leaf__));
extern char *mktemp (char *__template) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int mkstemp (char *__template) __attribute__ ((__nonnull__ (1))) ;
extern int mkstemps (char *__template, int __suffixlen) __attribute__ ((__nonnull__ (1))) ;
extern char *mkdtemp (char *__template) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;

extern int system (__const char *__command) ;

extern char *realpath (__const char *__restrict __name,
         char *__restrict __resolved) __attribute__ ((__nothrow__ , __leaf__)) ;
typedef int (*__compar_fn_t) (__const void *, __const void *);

extern void *bsearch (__const void *__key, __const void *__base,
        size_t __nmemb, size_t __size, __compar_fn_t __compar)
     __attribute__ ((__nonnull__ (1, 2, 5))) ;
extern void qsort (void *__base, size_t __nmemb, size_t __size,
     __compar_fn_t __compar) __attribute__ ((__nonnull__ (1, 4)));
extern int abs (int __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
extern long int labs (long int __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;

__extension__ extern long long int llabs (long long int __x)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;

extern div_t div (int __numer, int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
extern ldiv_t ldiv (long int __numer, long int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;


__extension__ extern lldiv_t lldiv (long long int __numer,
        long long int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;

extern char *ecvt (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;
extern char *fcvt (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;
extern char *gcvt (double __value, int __ndigit, char *__buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3))) ;
extern char *qecvt (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;
extern char *qfcvt (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;
extern char *qgcvt (long double __value, int __ndigit, char *__buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3))) ;
extern int ecvt_r (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign, char *__restrict __buf,
     size_t __len) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));
extern int fcvt_r (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign, char *__restrict __buf,
     size_t __len) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));
extern int qecvt_r (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign,
      char *__restrict __buf, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));
extern int qfcvt_r (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign,
      char *__restrict __buf, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));

extern int mblen (__const char *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int mbtowc (wchar_t *__restrict __pwc,
     __const char *__restrict __s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int wctomb (char *__s, wchar_t __wchar) __attribute__ ((__nothrow__ , __leaf__)) ;
extern size_t mbstowcs (wchar_t *__restrict __pwcs,
   __const char *__restrict __s, size_t __n) __attribute__ ((__nothrow__ , __leaf__));
extern size_t wcstombs (char *__restrict __s,
   __const wchar_t *__restrict __pwcs, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__));

extern int rpmatch (__const char *__response) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int getsubopt (char **__restrict __optionp,
        char *__const *__restrict __tokens,
        char **__restrict __valuep)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2, 3))) ;
extern int getloadavg (double __loadavg[], int __nelem)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

struct huft {
  uch e;
  uch b;
  union {
    ush n;
    struct huft *t;
  } v;
};
int huft_build (unsigned *, unsigned, unsigned, ush *, ush *, struct huft **, int *);
int huft_free (struct huft *);
int inflate_codes (struct huft *, struct huft *, int, int);
int inflate_stored (void);
int inflate_fixed (void);
int inflate_dynamic (void);
int inflate_block (int *);
int inflate (void);
static unsigned border[] = {
        16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15};
static ush cplens[] = {
        3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
        35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258, 0, 0};
static ush cplext[] = {
        0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
        3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 99, 99};
static ush cpdist[] = {
        1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
        257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
        8193, 12289, 16385, 24577};
static ush cpdext[] = {
        0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
        7, 7, 8, 8, 9, 9, 10, 10, 11, 11,
        12, 12, 13, 13};
ulg bb;
unsigned bk;
ush mask_bits[] = {
    0x0000,
    0x0001, 0x0003, 0x0007, 0x000f, 0x001f, 0x003f, 0x007f, 0x00ff,
    0x01ff, 0x03ff, 0x07ff, 0x0fff, 0x1fff, 0x3fff, 0x7fff, 0xffff
};
int lbits = 9;
int dbits = 6;
unsigned hufts;
int huft_build(b, n, s, d, e, t, m)
unsigned *b;
unsigned n;
unsigned s;
ush *d;
ush *e;
struct huft **t;
int *m;
{
  unsigned a;
  unsigned c[16 +1];
  unsigned f;
  int g;
  int h;
  register unsigned i;
  register unsigned j;
  register int k;
  int l;
  register unsigned *p;
  register struct huft *q;
  struct huft r;
  struct huft *u[16];
  unsigned v[288];
  register int w;
  unsigned x[16 +1];
  unsigned *xp;
  int y;
  unsigned z;
  memset ((voidp)(c), 0, (sizeof(c)));
  p = b; i = n;
  do {
    ;
    c[*p]++;
    p++;
  } while (--i);
  if (c[0] == n)
  {
    *t = (struct huft *)((void *)0);
    *m = 0;
    return 0;
  }
  l = *m;
  for (j = 1; j <= 16; j++)
    if (c[j])
      break;
  k = j;
  if ((unsigned)l < j)
    l = j;
  for (i = 16; i; i--)
    if (c[i])
      break;
  g = i;
  if ((unsigned)l > i)
    l = i;
  *m = l;
  for (y = 1 << j; j < i; j++, y <<= 1)
    if ((y -= c[j]) < 0)
      return 2;
  if ((y -= c[i]) < 0)
    return 2;
  c[i] += y;
  x[1] = j = 0;
  p = c + 1; xp = x + 2;
  while (--i) {
    *xp++ = (j += *p++);
  }
  p = b; i = 0;
  do {
    if ((j = *p++) != 0)
      v[x[j]++] = i;
  } while (++i < n);
  x[0] = i = 0;
  p = v;
  h = -1;
  w = -l;
  u[0] = (struct huft *)((void *)0);
  q = (struct huft *)((void *)0);
  z = 0;
  for (; k <= g; k++)
  {
    a = c[k];
    while (a--)
    {
      while (k > w + l)
      {
        h++;
        w += l;
        z = (z = g - w) > (unsigned)l ? l : z;
        if ((f = 1 << (j = k - w)) > a + 1)
        {
          f -= a + 1;
          xp = c + k;
          while (++j < z)
          {
            if ((f <<= 1) <= *++xp)
              break;
            f -= *xp;
          }
        }
        z = 1 << j;
        if ((q = (struct huft *)malloc((z + 1)*sizeof(struct huft))) ==
            (struct huft *)((void *)0))
        {
          if (h)
            huft_free(u[0]);
          return 3;
        }
        hufts += z + 1;
        *t = q + 1;
        *(t = &(q->v.t)) = (struct huft *)((void *)0);
        u[h] = ++q;
        if (h)
        {
          x[h] = i;
          r.b = (uch)l;
          r.e = (uch)(16 + j);
          r.v.t = q;
          j = i >> (w - l);
          u[h-1][j] = r;
        }
      }
      r.b = (uch)(k - w);
      if (p >= v + n)
        r.e = 99;
      else if (*p < s)
      {
        r.e = (uch)(*p < 256 ? 16 : 15);
        r.v.n = (ush)(*p);
 p++;
      }
      else
      {
        r.e = (uch)e[*p - s];
        r.v.n = d[*p++ - s];
      }
      f = 1 << (k - w);
      for (j = i >> w; j < z; j += f)
        q[j] = r;
      for (j = 1 << (k - 1); i & j; j >>= 1)
        i ^= j;
      i ^= j;
      while ((i & ((1 << w) - 1)) != x[h])
      {
        h--;
        w -= l;
      }
    }
  }
  return y != 0 && g != 1;
}
int huft_free(t)
struct huft *t;
{
  register struct huft *p, *q;
  p = t;
  while (p != (struct huft *)((void *)0))
  {
    q = (--p)->v.t;
    free((char*)p);
    p = q;
  }
  return 0;
}
int inflate_codes(tl, td, bl, bd)
struct huft *tl, *td;
int bl, bd;
{
  register unsigned e;
  unsigned n, d;
  unsigned w;
  struct huft *t;
  unsigned ml, md;
  register ulg b;
  register unsigned k;
  b = bb;
  k = bk;
  w = outcnt;
  ml = mask_bits[bl];
  md = mask_bits[bd];
  for (;;)
  {
    {while(k<((unsigned)bl)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
    if ((e = (t = tl + ((unsigned)b & ml))->e) > 16)
      do {
        if (e == 99)
          return 1;
        {b>>=(t->b);k-=(t->b);}
        e -= 16;
        {while(k<(e)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
      } while ((e = (t = t->v.t + ((unsigned)b & mask_bits[e]))->e) > 16);
    {b>>=(t->b);k-=(t->b);}
    if (e == 16)
    {
      window[w++] = (uch)t->v.n;
      ;
      if (w == 0x8000)
      {
        (outcnt=(w),flush_window());
        w = 0;
      }
    }
    else
    {
      if (e == 15)
        break;
      {while(k<(e)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
      n = t->v.n + ((unsigned)b & mask_bits[e]);
      {b>>=(e);k-=(e);};
      {while(k<((unsigned)bd)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
      if ((e = (t = td + ((unsigned)b & md))->e) > 16)
        do {
          if (e == 99)
            return 1;
          {b>>=(t->b);k-=(t->b);}
          e -= 16;
          {while(k<(e)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
        } while ((e = (t = t->v.t + ((unsigned)b & mask_bits[e]))->e) > 16);
      {b>>=(t->b);k-=(t->b);}
      {while(k<(e)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
      d = w - t->v.n - ((unsigned)b & mask_bits[e]);
      {b>>=(e);k-=(e);}
      ;
      do {
        n -= (e = (e = 0x8000 - ((d &= 0x8000 -1) > w ? d : w)) > n ? n : e);
        if (w - d >= e)
        {
          memcpy(window + w, window + d, e);
          w += e;
          d += e;
        }
        else
          do {
            window[w++] = window[d++];
     ;
          } while (--e);
        if (w == 0x8000)
        {
          (outcnt=(w),flush_window());
          w = 0;
        }
      } while (n);
    }
  }
  outcnt = w;
  bb = b;
  bk = k;
  return 0;
}
int inflate_stored()
{
  unsigned n;
  unsigned w;
  register ulg b;
  register unsigned k;
  b = bb;
  k = bk;
  w = outcnt;
  n = k & 7;
  {b>>=(n);k-=(n);};
  {while(k<(16)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
  n = ((unsigned)b & 0xffff);
  {b>>=(16);k-=(16);}
  {while(k<(16)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
  if (n != (unsigned)((~b) & 0xffff))
    return 1;
  {b>>=(16);k-=(16);}
  while (n--)
  {
    {while(k<(8)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
    window[w++] = (uch)b;
    if (w == 0x8000)
    {
      (outcnt=(w),flush_window());
      w = 0;
    }
    {b>>=(8);k-=(8);}
  }
  outcnt = w;
  bb = b;
  bk = k;
  return 0;
}
int inflate_fixed()
{
  int i;
  struct huft *tl;
  struct huft *td;
  int bl;
  int bd;
  unsigned l[288];
  for (i = 0; i < 144; i++)
    l[i] = 8;
  for (; i < 256; i++)
    l[i] = 9;
  for (; i < 280; i++)
    l[i] = 7;
  for (; i < 288; i++)
    l[i] = 8;
  bl = 7;
  if ((i = huft_build(l, 288, 257, cplens, cplext, &tl, &bl)) != 0)
    return i;
  for (i = 0; i < 30; i++)
    l[i] = 5;
  bd = 5;
  if ((i = huft_build(l, 30, 0, cpdist, cpdext, &td, &bd)) > 1)
  {
    huft_free(tl);
    return i;
  }
  if (inflate_codes(tl, td, bl, bd))
    return 1;
  huft_free(tl);
  huft_free(td);
  return 0;
}
int inflate_dynamic()
{
  int i;
  unsigned j;
  unsigned l;
  unsigned m;
  unsigned n;
  struct huft *tl;
  struct huft *td;
  int bl;
  int bd;
  unsigned nb;
  unsigned nl;
  unsigned nd;
  unsigned ll[286+30];
  register ulg b;
  register unsigned k;
  b = bb;
  k = bk;
  {while(k<(5)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
  nl = 257 + ((unsigned)b & 0x1f);
  {b>>=(5);k-=(5);}
  {while(k<(5)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
  nd = 1 + ((unsigned)b & 0x1f);
  {b>>=(5);k-=(5);}
  {while(k<(4)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
  nb = 4 + ((unsigned)b & 0xf);
  {b>>=(4);k-=(4);}
  if (nl > 286 || nd > 30)
    return 1;
  for (j = 0; j < nb; j++)
  {
    {while(k<(3)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
    ll[border[j]] = (unsigned)b & 7;
    {b>>=(3);k-=(3);}
  }
  for (; j < 19; j++)
    ll[border[j]] = 0;
  bl = 7;
  if ((i = huft_build(ll, 19, 19, ((void *)0), ((void *)0), &tl, &bl)) != 0)
  {
    if (i == 1)
      huft_free(tl);
    return i;
  }
  n = nl + nd;
  m = mask_bits[bl];
  i = l = 0;
  while ((unsigned)i < n)
  {
    {while(k<((unsigned)bl)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
    j = (td = tl + ((unsigned)b & m))->b;
    {b>>=(j);k-=(j);}
    j = td->v.n;
    if (j < 16)
      ll[i++] = l = j;
    else if (j == 16)
    {
      {while(k<(2)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
      j = 3 + ((unsigned)b & 3);
      {b>>=(2);k-=(2);}
      if ((unsigned)i + j > n)
        return 1;
      while (j--)
        ll[i++] = l;
    }
    else if (j == 17)
    {
      {while(k<(3)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
      j = 3 + ((unsigned)b & 7);
      {b>>=(3);k-=(3);}
      if ((unsigned)i + j > n)
        return 1;
      while (j--)
        ll[i++] = 0;
      l = 0;
    }
    else
    {
      {while(k<(7)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
      j = 11 + ((unsigned)b & 0x7f);
      {b>>=(7);k-=(7);}
      if ((unsigned)i + j > n)
        return 1;
      while (j--)
        ll[i++] = 0;
      l = 0;
    }
  }
  huft_free(tl);
  bb = b;
  bk = k;
  bl = lbits;
  if ((i = huft_build(ll, nl, 257, cplens, cplext, &tl, &bl)) != 0)
  {
    if (i == 1) {
      fprintf(stderr, " incomplete literal tree\n");
      huft_free(tl);
    }
    return i;
  }
  bd = dbits;
  if ((i = huft_build(ll + nl, nd, 0, cpdist, cpdext, &td, &bd)) != 0)
  {
    if (i == 1) {
      fprintf(stderr, " incomplete distance tree\n");
      huft_free(td);
    }
    huft_free(tl);
    return i;
  }
  if (inflate_codes(tl, td, bl, bd))
    return 1;
  huft_free(tl);
  huft_free(td);
  return 0;
}
int inflate_block(e)
int *e;
{
  unsigned t;
  register ulg b;
  register unsigned k;
  b = bb;
  k = bk;
  {while(k<(1)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
  *e = (int)b & 1;
  {b>>=(1);k-=(1);}
  {while(k<(2)){b|=((ulg)(uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<k;k+=8;}}
  t = (unsigned)b & 3;
  {b>>=(2);k-=(2);}
  bb = b;
  bk = k;
  if (t == 2)
    return inflate_dynamic();
  if (t == 0)
    return inflate_stored();
  if (t == 1)
    return inflate_fixed();
  return 2;
}
int inflate()
{
  int e;
  int r;
  unsigned h;
  outcnt = 0;
  bk = 0;
  bb = 0;
  h = 0;
  do {
    hufts = 0;
    if ((r = inflate_block(&e)) != 0)
      return r;
    if (hufts > h)
      h = hufts;
  } while (!e);
  while (bk >= 8) {
    bk -= 8;
    inptr--;
  }
  (outcnt=(outcnt),flush_window());
  return 0;
}
static int msg_done = 0;
int lzw(in, out)
    int in, out;
{
    if (msg_done) return 1;
    msg_done = 1;
    fprintf(stderr,"output in compress .Z format not supported\n");
    if (in != out) {
        exit_code = 1;
    }
    return 1;
}
static int extra_lbits[29]
   = {0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0};
static int extra_dbits[30]
   = {0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13};
static int extra_blbits[19]
   = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,7};
typedef struct ct_data {
    union {
        ush freq;
        ush code;
    } fc;
    union {
        ush dad;
        ush len;
    } dl;
} ct_data;
static ct_data dyn_ltree[(2*(256 +1+29)+1)];
static ct_data dyn_dtree[2*30 +1];
static ct_data static_ltree[(256 +1+29)+2];
static ct_data static_dtree[30];
static ct_data bl_tree[2*19 +1];
typedef struct tree_desc {
    ct_data *dyn_tree;
    ct_data *static_tree;
    int *extra_bits;
    int extra_base;
    int elems;
    int max_length;
    int max_code;
} tree_desc;
static tree_desc l_desc =
{dyn_ltree, static_ltree, extra_lbits, 256 +1, (256 +1+29), 15, 0};
static tree_desc d_desc =
{dyn_dtree, static_dtree, extra_dbits, 0, 30, 15, 0};
static tree_desc bl_desc =
{bl_tree, (ct_data *)0, extra_blbits, 0, 19, 7, 0};
static ush bl_count[15 +1];
static uch bl_order[19]
   = {16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15};
static int heap[2*(256 +1+29)+1];
static int heap_len;
static int heap_max;
static uch depth[2*(256 +1+29)+1];
static uch length_code[258 -3 +1];
static uch dist_code[512];
static int base_length[29];
static int base_dist[30];
static uch flag_buf[(0x8000/8)];
static unsigned last_lit;
static unsigned last_dist;
static unsigned last_flags;
static uch flags;
static uch flag_bit;
static ulg opt_len;
static ulg static_len;
static ulg compressed_len;
static ulg input_len;
ush *file_type;
int *file_method;
extern long block_start;
extern unsigned strstart;
static void init_block (void);
static void pqdownheap (ct_data *tree, int k);
static void gen_bitlen (tree_desc *desc);
static void gen_codes (ct_data *tree, int max_code);
static void build_tree (tree_desc *desc);
static void scan_tree (ct_data *tree, int max_code);
static void send_tree (ct_data *tree, int max_code);
static int build_bl_tree (void);
static void send_all_trees (int lcodes, int dcodes, int blcodes);
static void compress_block (ct_data *ltree, ct_data *dtree);
static void set_file_type (void);
void ct_init(attr, methodp)
    ush *attr;
    int *methodp;
{
    int n;
    int bits;
    int length;
    int code;
    int dist;
    file_type = attr;
    file_method = methodp;
    compressed_len = input_len = 0L;
    if (static_dtree[0].dl.len != 0) return;
    length = 0;
    for (code = 0; code < 29 -1; code++) {
        base_length[code] = length;
        for (n = 0; n < (1<<extra_lbits[code]); n++) {
            length_code[length++] = (uch)code;
        }
    }
    ;
    length_code[length-1] = (uch)code;
    dist = 0;
    for (code = 0 ; code < 16; code++) {
        base_dist[code] = dist;
        for (n = 0; n < (1<<extra_dbits[code]); n++) {
            dist_code[dist++] = (uch)code;
        }
    }
    ;
    dist >>= 7;
    for ( ; code < 30; code++) {
        base_dist[code] = dist << 7;
        for (n = 0; n < (1<<(extra_dbits[code]-7)); n++) {
            dist_code[256 + dist++] = (uch)code;
        }
    }
    ;
    for (bits = 0; bits <= 15; bits++) bl_count[bits] = 0;
    n = 0;
    while (n <= 143) static_ltree[n++].dl.len = 8, bl_count[8]++;
    while (n <= 255) static_ltree[n++].dl.len = 9, bl_count[9]++;
    while (n <= 279) static_ltree[n++].dl.len = 7, bl_count[7]++;
    while (n <= 287) static_ltree[n++].dl.len = 8, bl_count[8]++;
    gen_codes((ct_data *)static_ltree, (256 +1+29)+1);
    for (n = 0; n < 30; n++) {
        static_dtree[n].dl.len = 5;
        static_dtree[n].fc.code = bi_reverse(n, 5);
    }
    init_block();
}
static void init_block()
{
    int n;
    for (n = 0; n < (256 +1+29); n++) dyn_ltree[n].fc.freq = 0;
    for (n = 0; n < 30; n++) dyn_dtree[n].fc.freq = 0;
    for (n = 0; n < 19; n++) bl_tree[n].fc.freq = 0;
    dyn_ltree[256].fc.freq = 1;
    opt_len = static_len = 0L;
    last_lit = last_dist = last_flags = 0;
    flags = 0; flag_bit = 1;
}
static void pqdownheap(tree, k)
    ct_data *tree;
    int k;
{
    int v = heap[k];
    int j = k << 1;
    while (j <= heap_len) {
        if (j < heap_len && (tree[heap[j+1]].fc.freq < tree[heap[j]].fc.freq || (tree[heap[j+1]].fc.freq == tree[heap[j]].fc.freq && depth[heap[j+1]] <= depth[heap[j]]))) j++;
        if ((tree[v].fc.freq < tree[heap[j]].fc.freq || (tree[v].fc.freq == tree[heap[j]].fc.freq && depth[v] <= depth[heap[j]]))) break;
        heap[k] = heap[j]; k = j;
        j <<= 1;
    }
    heap[k] = v;
}
static void gen_bitlen(desc)
    tree_desc *desc;
{
    ct_data *tree = desc->dyn_tree;
    int *extra = desc->extra_bits;
    int base = desc->extra_base;
    int max_code = desc->max_code;
    int max_length = desc->max_length;
    ct_data *stree = desc->static_tree;
    int h;
    int n, m;
    int bits;
    int xbits;
    ush f;
    int overflow = 0;
    for (bits = 0; bits <= 15; bits++) bl_count[bits] = 0;
    tree[heap[heap_max]].dl.len = 0;
    for (h = heap_max+1; h < (2*(256 +1+29)+1); h++) {
        n = heap[h];
        bits = tree[tree[n].dl.dad].dl.len + 1;
        if (bits > max_length) bits = max_length, overflow++;
        tree[n].dl.len = (ush)bits;
        if (n > max_code) continue;
        bl_count[bits]++;
        xbits = 0;
        if (n >= base) xbits = extra[n-base];
        f = tree[n].fc.freq;
        opt_len += (ulg)f * (bits + xbits);
        if (stree) static_len += (ulg)f * (stree[n].dl.len + xbits);
    }
    if (overflow == 0) return;
    ;
    do {
        bits = max_length-1;
        while (bl_count[bits] == 0) bits--;
        bl_count[bits]--;
        bl_count[bits+1] += 2;
        bl_count[max_length]--;
        overflow -= 2;
    } while (overflow > 0);
    for (bits = max_length; bits != 0; bits--) {
        n = bl_count[bits];
        while (n != 0) {
            m = heap[--h];
            if (m > max_code) continue;
            if (tree[m].dl.len != (unsigned) bits) {
                ;
                opt_len += ((long)bits-(long)tree[m].dl.len)*(long)tree[m].fc.freq;
                tree[m].dl.len = (ush)bits;
            }
            n--;
        }
    }
}
static void gen_codes (tree, max_code)
    ct_data *tree;
    int max_code;
{
    ush next_code[15 +1];
    ush code = 0;
    int bits;
    int n;
    for (bits = 1; bits <= 15; bits++) {
        next_code[bits] = code = (code + bl_count[bits-1]) << 1;
    }
    ;
    ;
    for (n = 0; n <= max_code; n++) {
        int len = tree[n].dl.len;
        if (len == 0) continue;
        tree[n].fc.code = bi_reverse(next_code[len]++, len);
        ;
    }
}

static void build_tree(desc)
    tree_desc *desc;
{
    ct_data *tree = desc->dyn_tree;
    ct_data *stree = desc->static_tree;
    int elems = desc->elems;
    int n, m;
    int max_code = -1;
    int node = elems;





    heap_len = 0, heap_max = (2*(256 +1+29)+1);

    for (n = 0; n < elems; n++) {
        if (tree[n].fc.freq != 0) {
            heap[++heap_len] = max_code = n;
            depth[n] = 0;
        } else {
            tree[n].dl.len = 0;
        }
    }






    while (heap_len < 2) {
        int new = heap[++heap_len] = (max_code < 2 ? ++max_code : 0);
        tree[new].fc.freq = 1;
        depth[new] = 0;
        opt_len--; if (stree) static_len -= stree[new].dl.len;

    }
    desc->max_code = max_code;




    for (n = heap_len/2; n >= 1; n--) pqdownheap(tree, n);




    do {
        { n = heap[1]; heap[1] = heap[heap_len--]; pqdownheap(tree, 1); };
        m = heap[1];

        heap[--heap_max] = n;
        heap[--heap_max] = m;


        tree[node].fc.freq = tree[n].fc.freq + tree[m].fc.freq;
        depth[node] = (uch) ((depth[n] >= depth[m] ? depth[n] : depth[m]) + 1);
        tree[n].dl.dad = tree[m].dl.dad = (ush)node;







        heap[1] = node++;
        pqdownheap(tree, 1);

    } while (heap_len >= 2);

    heap[--heap_max] = heap[1];




    gen_bitlen((tree_desc *)desc);


    gen_codes ((ct_data *)tree, max_code);
}







static void scan_tree (tree, max_code)
    ct_data *tree;
    int max_code;
{
    int n;
    int prevlen = -1;
    int curlen;
    int nextlen = tree[0].dl.len;
    int count = 0;
    int max_count = 7;
    int min_count = 4;

    if (nextlen == 0) max_count = 138, min_count = 3;
    tree[max_code+1].dl.len = (ush)0xffff;

    for (n = 0; n <= max_code; n++) {
        curlen = nextlen; nextlen = tree[n+1].dl.len;
        if (++count < max_count && curlen == nextlen) {
            continue;
        } else if (count < min_count) {
            bl_tree[curlen].fc.freq += count;
        } else if (curlen != 0) {
            if (curlen != prevlen) bl_tree[curlen].fc.freq++;
            bl_tree[16].fc.freq++;
        } else if (count <= 10) {
            bl_tree[17].fc.freq++;
        } else {
            bl_tree[18].fc.freq++;
        }
        count = 0; prevlen = curlen;
        if (nextlen == 0) {
            max_count = 138, min_count = 3;
        } else if (curlen == nextlen) {
            max_count = 6, min_count = 3;
        } else {
            max_count = 7, min_count = 4;
        }
    }
}





static void send_tree (tree, max_code)
    ct_data *tree;
    int max_code;
{
    int n;
    int prevlen = -1;
    int curlen;
    int nextlen = tree[0].dl.len;
    int count = 0;
    int max_count = 7;
    int min_count = 4;


    if (nextlen == 0) max_count = 138, min_count = 3;

    for (n = 0; n <= max_code; n++) {
        curlen = nextlen; nextlen = tree[n+1].dl.len;
        if (++count < max_count && curlen == nextlen) {
            continue;
        } else if (count < min_count) {
            do { send_bits(bl_tree[curlen].fc.code, bl_tree[curlen].dl.len); } while (--count != 0);

        } else if (curlen != 0) {
            if (curlen != prevlen) {
                send_bits(bl_tree[curlen].fc.code, bl_tree[curlen].dl.len); count--;
            }
            ;
            send_bits(bl_tree[16].fc.code, bl_tree[16].dl.len); send_bits(count-3, 2);

        } else if (count <= 10) {
            send_bits(bl_tree[17].fc.code, bl_tree[17].dl.len); send_bits(count-3, 3);

        } else {
            send_bits(bl_tree[18].fc.code, bl_tree[18].dl.len); send_bits(count-11, 7);
        }
        count = 0; prevlen = curlen;
        if (nextlen == 0) {
            max_count = 138, min_count = 3;
        } else if (curlen == nextlen) {
            max_count = 6, min_count = 3;
        } else {
            max_count = 7, min_count = 4;
        }
    }
}





static int build_bl_tree()
{
    int max_blindex;


    scan_tree((ct_data *)dyn_ltree, l_desc.max_code);
    scan_tree((ct_data *)dyn_dtree, d_desc.max_code);


    build_tree((tree_desc *)(&bl_desc));
    for (max_blindex = 19 -1; max_blindex >= 3; max_blindex--) {
        if (bl_tree[bl_order[max_blindex]].dl.len != 0) break;
    }
    opt_len += 3*(max_blindex+1) + 5+5+4;
    ;
    return max_blindex;
}
static void send_all_trees(lcodes, dcodes, blcodes)
    int lcodes, dcodes, blcodes;
{
    int rank;
    ;
    ;
    ;
    send_bits(lcodes-257, 5);
    send_bits(dcodes-1, 5);
    send_bits(blcodes-4, 4);
    for (rank = 0; rank < blcodes; rank++) {
        ;
        send_bits(bl_tree[bl_order[rank]].dl.len, 3);
    }
    ;
    send_tree((ct_data *)dyn_ltree, lcodes-1);
    ;
    send_tree((ct_data *)dyn_dtree, dcodes-1);
    ;
}
ulg flush_block(buf, stored_len, eof)
    char *buf;
    ulg stored_len;
    int eof;
{
    ulg opt_lenb, static_lenb;
    int max_blindex;
    flag_buf[last_flags] = flags;
    if (*file_type == (ush)0xffff) set_file_type();
    build_tree((tree_desc *)(&l_desc));
    ;
    build_tree((tree_desc *)(&d_desc));
    ;
    max_blindex = build_bl_tree();
    opt_lenb = (opt_len+3+7)>>3;
    static_lenb = (static_len+3+7)>>3;
    input_len += stored_len;
    ;
    if (static_lenb <= opt_lenb) opt_lenb = static_lenb;
    if (stored_len <= opt_lenb && eof && compressed_len == 0L && 0) {
        if (buf == (char*)0) error ("block vanished");
        copy_block(buf, (unsigned)stored_len, 0);
        compressed_len = stored_len << 3;
        *file_method = 0;
    } else if (stored_len+4 <= opt_lenb && buf != (char*)0) {
        send_bits((0<<1)+eof, 3);
        compressed_len = (compressed_len + 3 + 7) & ~7L;
        compressed_len += (stored_len + 4) << 3;
        copy_block(buf, (unsigned)stored_len, 1);
    } else if (static_lenb == opt_lenb) {
        send_bits((1<<1)+eof, 3);
        compress_block((ct_data *)static_ltree, (ct_data *)static_dtree);
        compressed_len += 3 + static_len;
    } else {
        send_bits((2<<1)+eof, 3);
        send_all_trees(l_desc.max_code+1, d_desc.max_code+1, max_blindex+1);
        compress_block((ct_data *)dyn_ltree, (ct_data *)dyn_dtree);
        compressed_len += 3 + opt_len;
    }
    ;
    init_block();
    if (eof) {
        ;
        bi_windup();
        compressed_len += 7;
    }
    ;
    return compressed_len >> 3;
}
int ct_tally (dist, lc)
    int dist;
    int lc;
{
    inbuf[last_lit++] = (uch)lc;
    if (dist == 0) {
        dyn_ltree[lc].fc.freq++;
    } else {
        dist--;
        ;
        dyn_ltree[length_code[lc]+256 +1].fc.freq++;
        dyn_dtree[((dist) < 256 ? dist_code[dist] : dist_code[256+((dist)>>7)])].fc.freq++;
        d_buf[last_dist++] = (ush)dist;
        flags |= flag_bit;
    }
    flag_bit <<= 1;
    if ((last_lit & 7) == 0) {
        flag_buf[last_flags++] = flags;
        flags = 0, flag_bit = 1;
    }
    if (level > 2 && (last_lit & 0xfff) == 0) {
        ulg out_length = (ulg)last_lit*8L;
        ulg in_length = (ulg)strstart-block_start;
        int dcode;
        for (dcode = 0; dcode < 30; dcode++) {
            out_length += (ulg)dyn_dtree[dcode].fc.freq*(5L+extra_dbits[dcode]);
        }
        out_length >>= 3;
        ;
        if (last_dist < last_lit/2 && out_length < in_length/2) return 1;
    }
    return (last_lit == 0x8000 -1 || last_dist == 0x8000);
}
static void compress_block(ltree, dtree)
    ct_data *ltree;
    ct_data *dtree;
{
    unsigned dist;
    int lc;
    unsigned lx = 0;
    unsigned dx = 0;
    unsigned fx = 0;
    uch flag = 0;
    unsigned code;
    int extra;
    if (last_lit != 0) do {
        if ((lx & 7) == 0) flag = flag_buf[fx++];
        lc = inbuf[lx++];
        if ((flag & 1) == 0) {
            send_bits(ltree[lc].fc.code, ltree[lc].dl.len);
            ;
        } else {
            code = length_code[lc];
            send_bits(ltree[code+256 +1].fc.code, ltree[code+256 +1].dl.len);
            extra = extra_lbits[code];
            if (extra != 0) {
                lc -= base_length[code];
                send_bits(lc, extra);
            }
            dist = d_buf[dx++];
            code = ((dist) < 256 ? dist_code[dist] : dist_code[256+((dist)>>7)]);
            ;
            send_bits(dtree[code].fc.code, dtree[code].dl.len);
            extra = extra_dbits[code];
            if (extra != 0) {
                dist -= base_dist[code];
                send_bits(dist, extra);
            }
        }
        flag >>= 1;
    } while (lx < last_lit);
    send_bits(ltree[256].fc.code, ltree[256].dl.len);
}
static void set_file_type()
{
    int n = 0;
    unsigned ascii_freq = 0;
    unsigned bin_freq = 0;
    while (n < 7) bin_freq += dyn_ltree[n++].fc.freq;
    while (n < 128) ascii_freq += dyn_ltree[n++].fc.freq;
    while (n < 256) bin_freq += dyn_ltree[n++].fc.freq;
    *file_type = bin_freq > (ascii_freq >> 2) ? 0 : 1;
    if (*file_type == 0 && 0) {
        warn("-l used on binary file", "");
    }
}
static unsigned decode (unsigned count, uch buffer[]);
static void decode_start (void);
static void huf_decode_start (void);
static unsigned decode_c (void);
static unsigned decode_p (void);
static void read_pt_len (int nn, int nbit, int i_special);
static void read_c_len (void);
static void fillbuf (int n);
static unsigned getbits (int n);
static void init_getbits (void);
static void make_table (int nchar, uch bitlen[], int tablebits, ush table[]);
static uch pt_len[(16 + 3)];
static unsigned blocksize;
static ush pt_table[256];
static ush bitbuf;
static unsigned subbitbuf;
static int bitcount;
static void fillbuf(n)
    int n;
{
    bitbuf <<= n;
    while (n > bitcount) {
 bitbuf |= subbitbuf << (n -= bitcount);
 subbitbuf = (unsigned)(inptr < insize ? inbuf[inptr++] : fill_inbuf(1));
 if ((int)subbitbuf == (-1)) subbitbuf = 0;
 bitcount = 8;
    }
    bitbuf |= subbitbuf >> (bitcount -= n);
}
static unsigned getbits(n)
    int n;
{
    unsigned x;
    x = bitbuf >> ((8 * 2 * sizeof(char)) - n); fillbuf(n);
    return x;
}
static void init_getbits()
{
    bitbuf = 0; subbitbuf = 0; bitcount = 0;
    fillbuf((8 * 2 * sizeof(char)));
}
static void make_table(nchar, bitlen, tablebits, table)
    int nchar;
    uch bitlen[];
    int tablebits;
    ush table[];
{
    ush count[17], weight[17], start[18], *p;
    unsigned i, k, len, ch, jutbits, avail, nextcode, mask;
    for (i = 1; i <= 16; i++) count[i] = 0;
    for (i = 0; i < (unsigned)nchar; i++) count[bitlen[i]]++;
    start[1] = 0;
    for (i = 1; i <= 16; i++)
 start[i + 1] = start[i] + (count[i] << (16 - i));
    if ((start[17] & 0xffff) != 0)
 error("Bad table\n");
    jutbits = 16 - tablebits;
    for (i = 1; i <= (unsigned)tablebits; i++) {
 start[i] >>= jutbits;
 weight[i] = (unsigned) 1 << (tablebits - i);
    }
    while (i <= 16) {
 weight[i] = (unsigned) 1 << (16 - i);
 i++;
    }
    i = start[tablebits + 1] >> jutbits;
    if (i != 0) {
 k = 1 << tablebits;
 while (i != k) table[i++] = 0;
    }
    avail = nchar;
    mask = (unsigned) 1 << (15 - tablebits);
    for (ch = 0; ch < (unsigned)nchar; ch++) {
 if ((len = bitlen[ch]) == 0) continue;
 nextcode = start[len] + weight[len];
 if (len <= (unsigned)tablebits) {
     for (i = start[len]; i < nextcode; i++) table[i] = ch;
 } else {
     k = start[len];
     p = &table[k >> jutbits];
     i = len - tablebits;
     while (i != 0) {
  if (*p == 0) {
      (prev+0x8000)[avail] = prev[avail] = 0;
      *p = avail++;
  }
  if (k & mask) p = &(prev+0x8000)[*p];
  else p = &prev[*p];
  k <<= 1; i--;
     }
     *p = ch;
 }
 start[len] = nextcode;
    }
}
static void read_pt_len(nn, nbit, i_special)
    int nn;
    int nbit;
    int i_special;
{
    int i, c, n;
    unsigned mask;
    n = getbits(nbit);
    if (n == 0) {
 c = getbits(nbit);
 for (i = 0; i < nn; i++) pt_len[i] = 0;
 for (i = 0; i < 256; i++) pt_table[i] = c;
    } else {
 i = 0;
 while (i < n) {
     c = bitbuf >> ((8 * 2 * sizeof(char)) - 3);
     if (c == 7) {
  mask = (unsigned) 1 << ((8 * 2 * sizeof(char)) - 1 - 3);
  while (mask & bitbuf) { mask >>= 1; c++; }
     }
     fillbuf((c < 7) ? 3 : c - 3);
     pt_len[i++] = c;
     if (i == i_special) {
  c = getbits(2);
  while (--c >= 0) pt_len[i++] = 0;
     }
 }
 while (i < nn) pt_len[i++] = 0;
 make_table(nn, pt_len, 8, pt_table);
    }
}
static void read_c_len()
{
    int i, c, n;
    unsigned mask;
    n = getbits(9);
    if (n == 0) {
 c = getbits(9);
 for (i = 0; i < (255 + 256 + 2 - 3); i++) outbuf[i] = 0;
 for (i = 0; i < 4096; i++) d_buf[i] = c;
    } else {
 i = 0;
 while (i < n) {
     c = pt_table[bitbuf >> ((8 * 2 * sizeof(char)) - 8)];
     if (c >= (16 + 3)) {
  mask = (unsigned) 1 << ((8 * 2 * sizeof(char)) - 1 - 8);
  do {
      if (bitbuf & mask) c = (prev+0x8000)[c];
      else c = prev [c];
      mask >>= 1;
  } while (c >= (16 + 3));
     }
     fillbuf((int) pt_len[c]);
     if (c <= 2) {
  if (c == 0) c = 1;
  else if (c == 1) c = getbits(4) + 3;
  else c = getbits(9) + 20;
  while (--c >= 0) outbuf[i++] = 0;
     } else outbuf[i++] = c - 2;
 }
 while (i < (255 + 256 + 2 - 3)) outbuf[i++] = 0;
 make_table((255 + 256 + 2 - 3), outbuf, 12, d_buf);
    }
}
static unsigned decode_c()
{
    unsigned j, mask;
    if (blocksize == 0) {
 blocksize = getbits(16);
 if (blocksize == 0) {
     return (255 + 256 + 2 - 3);
 }
 read_pt_len((16 + 3), 5, 3);
 read_c_len();
 read_pt_len((13 + 1), 4, -1);
    }
    blocksize--;
    j = d_buf[bitbuf >> ((8 * 2 * sizeof(char)) - 12)];
    if (j >= (255 + 256 + 2 - 3)) {
 mask = (unsigned) 1 << ((8 * 2 * sizeof(char)) - 1 - 12);
 do {
     if (bitbuf & mask) j = (prev+0x8000)[j];
     else j = prev [j];
     mask >>= 1;
 } while (j >= (255 + 256 + 2 - 3));
    }
    fillbuf((int) outbuf[j]);
    return j;
}
static unsigned decode_p()
{
    unsigned j, mask;
    j = pt_table[bitbuf >> ((8 * 2 * sizeof(char)) - 8)];
    if (j >= (13 + 1)) {
 mask = (unsigned) 1 << ((8 * 2 * sizeof(char)) - 1 - 8);
 do {
     if (bitbuf & mask) j = (prev+0x8000)[j];
     else j = prev [j];
     mask >>= 1;
 } while (j >= (13 + 1));
    }
    fillbuf((int) pt_len[j]);
    if (j != 0) j = ((unsigned) 1 << (j - 1)) + getbits((int) (j - 1));
    return j;
}
static void huf_decode_start()
{
    init_getbits(); blocksize = 0;
}
static int j;
static int done;
static void decode_start()
{
    huf_decode_start();
    j = 0;
    done = 0;
}
static unsigned decode(count, buffer)
    unsigned count;
    uch buffer[];
{
    static unsigned i;
    unsigned r, c;
    r = 0;
    while (--j >= 0) {
 buffer[r] = buffer[i];
 i = (i + 1) & (((unsigned) 1 << 13) - 1);
 if (++r == count) return r;
    }
    for ( ; ; ) {
 c = decode_c();
 if (c == (255 + 256 + 2 - 3)) {
     done = 1;
     return r;
 }
 if (c <= 255) {
     buffer[r] = c;
     if (++r == count) return r;
 } else {
     j = c - (255 + 1 - 3);
     i = (r - decode_p() - 1) & (((unsigned) 1 << 13) - 1);
     while (--j >= 0) {
  buffer[r] = buffer[i];
  i = (i + 1) & (((unsigned) 1 << 13) - 1);
  if (++r == count) return r;
     }
 }
    }
}
int unlzh(in, out)
    int in;
    int out;
{
    unsigned n;
    ifd = in;
    ofd = out;
    decode_start();
    while (!done) {
 n = decode((unsigned) ((unsigned) 1 << 13), window);
 if (!test && n > 0) {
     write_buf(out, (char*)window, n);
 }
    }
    return 0;
}

typedef __useconds_t useconds_t;
typedef __intptr_t intptr_t;
typedef __socklen_t socklen_t;
extern int access (__const char *__name, int __type) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int faccessat (int __fd, __const char *__file, int __type, int __flag)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2))) ;
extern __off_t lseek (int __fd, __off_t __offset, int __whence) __attribute__ ((__nothrow__ , __leaf__));
extern int close (int __fd);
extern ssize_t read (int __fd, void *__buf, size_t __nbytes) ;
extern ssize_t write (int __fd, __const void *__buf, size_t __n) ;
extern ssize_t pread (int __fd, void *__buf, size_t __nbytes,
        __off_t __offset) ;
extern ssize_t pwrite (int __fd, __const void *__buf, size_t __n,
         __off_t __offset) ;
extern int pipe (int __pipedes[2]) __attribute__ ((__nothrow__ , __leaf__)) ;
extern unsigned int alarm (unsigned int __seconds) __attribute__ ((__nothrow__ , __leaf__));
extern unsigned int sleep (unsigned int __seconds);
extern __useconds_t ualarm (__useconds_t __value, __useconds_t __interval)
     __attribute__ ((__nothrow__ , __leaf__));
extern int usleep (__useconds_t __useconds);
extern int pause (void);
extern int chown (__const char *__file, __uid_t __owner, __gid_t __group)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int fchown (int __fd, __uid_t __owner, __gid_t __group) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int lchown (__const char *__file, __uid_t __owner, __gid_t __group)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int fchownat (int __fd, __const char *__file, __uid_t __owner,
       __gid_t __group, int __flag)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2))) ;
extern int chdir (__const char *__path) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int fchdir (int __fd) __attribute__ ((__nothrow__ , __leaf__)) ;
extern char *getcwd (char *__buf, size_t __size) __attribute__ ((__nothrow__ , __leaf__)) ;
extern char *getwd (char *__buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) __attribute__ ((__deprecated__)) ;
extern int dup (int __fd) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int dup2 (int __fd, int __fd2) __attribute__ ((__nothrow__ , __leaf__));
extern char **__environ;
extern int execve (__const char *__path, char *__const __argv[],
     char *__const __envp[]) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int fexecve (int __fd, char *__const __argv[], char *__const __envp[])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int execv (__const char *__path, char *__const __argv[])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int execle (__const char *__path, __const char *__arg, ...)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int execl (__const char *__path, __const char *__arg, ...)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int execvp (__const char *__file, char *__const __argv[])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int execlp (__const char *__file, __const char *__arg, ...)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int nice (int __inc) __attribute__ ((__nothrow__ , __leaf__)) ;
extern void _exit (int __status) __attribute__ ((__noreturn__));
enum
  {
    _PC_LINK_MAX,
    _PC_MAX_CANON,
    _PC_MAX_INPUT,
    _PC_NAME_MAX,
    _PC_PATH_MAX,
    _PC_PIPE_BUF,
    _PC_CHOWN_RESTRICTED,
    _PC_NO_TRUNC,
    _PC_VDISABLE,
    _PC_SYNC_IO,
    _PC_ASYNC_IO,
    _PC_PRIO_IO,
    _PC_SOCK_MAXBUF,
    _PC_FILESIZEBITS,
    _PC_REC_INCR_XFER_SIZE,
    _PC_REC_MAX_XFER_SIZE,
    _PC_REC_MIN_XFER_SIZE,
    _PC_REC_XFER_ALIGN,
    _PC_ALLOC_SIZE_MIN,
    _PC_SYMLINK_MAX,
    _PC_2_SYMLINKS
  };
enum
  {
    _SC_ARG_MAX,
    _SC_CHILD_MAX,
    _SC_CLK_TCK,
    _SC_NGROUPS_MAX,
    _SC_OPEN_MAX,
    _SC_STREAM_MAX,
    _SC_TZNAME_MAX,
    _SC_JOB_CONTROL,
    _SC_SAVED_IDS,
    _SC_REALTIME_SIGNALS,
    _SC_PRIORITY_SCHEDULING,
    _SC_TIMERS,
    _SC_ASYNCHRONOUS_IO,
    _SC_PRIORITIZED_IO,
    _SC_SYNCHRONIZED_IO,
    _SC_FSYNC,
    _SC_MAPPED_FILES,
    _SC_MEMLOCK,
    _SC_MEMLOCK_RANGE,
    _SC_MEMORY_PROTECTION,
    _SC_MESSAGE_PASSING,
    _SC_SEMAPHORES,
    _SC_SHARED_MEMORY_OBJECTS,
    _SC_AIO_LISTIO_MAX,
    _SC_AIO_MAX,
    _SC_AIO_PRIO_DELTA_MAX,
    _SC_DELAYTIMER_MAX,
    _SC_MQ_OPEN_MAX,
    _SC_MQ_PRIO_MAX,
    _SC_VERSION,
    _SC_PAGESIZE,
    _SC_RTSIG_MAX,
    _SC_SEM_NSEMS_MAX,
    _SC_SEM_VALUE_MAX,
    _SC_SIGQUEUE_MAX,
    _SC_TIMER_MAX,
    _SC_BC_BASE_MAX,
    _SC_BC_DIM_MAX,
    _SC_BC_SCALE_MAX,
    _SC_BC_STRING_MAX,
    _SC_COLL_WEIGHTS_MAX,
    _SC_EQUIV_CLASS_MAX,
    _SC_EXPR_NEST_MAX,
    _SC_LINE_MAX,
    _SC_RE_DUP_MAX,
    _SC_CHARCLASS_NAME_MAX,
    _SC_2_VERSION,
    _SC_2_C_BIND,
    _SC_2_C_DEV,
    _SC_2_FORT_DEV,
    _SC_2_FORT_RUN,
    _SC_2_SW_DEV,
    _SC_2_LOCALEDEF,
    _SC_PII,
    _SC_PII_XTI,
    _SC_PII_SOCKET,
    _SC_PII_INTERNET,
    _SC_PII_OSI,
    _SC_POLL,
    _SC_SELECT,
    _SC_UIO_MAXIOV,
    _SC_IOV_MAX = _SC_UIO_MAXIOV,
    _SC_PII_INTERNET_STREAM,
    _SC_PII_INTERNET_DGRAM,
    _SC_PII_OSI_COTS,
    _SC_PII_OSI_CLTS,
    _SC_PII_OSI_M,
    _SC_T_IOV_MAX,
    _SC_THREADS,
    _SC_THREAD_SAFE_FUNCTIONS,
    _SC_GETGR_R_SIZE_MAX,
    _SC_GETPW_R_SIZE_MAX,
    _SC_LOGIN_NAME_MAX,
    _SC_TTY_NAME_MAX,
    _SC_THREAD_DESTRUCTOR_ITERATIONS,
    _SC_THREAD_KEYS_MAX,
    _SC_THREAD_STACK_MIN,
    _SC_THREAD_THREADS_MAX,
    _SC_THREAD_ATTR_STACKADDR,
    _SC_THREAD_ATTR_STACKSIZE,
    _SC_THREAD_PRIORITY_SCHEDULING,
    _SC_THREAD_PRIO_INHERIT,
    _SC_THREAD_PRIO_PROTECT,
    _SC_THREAD_PROCESS_SHARED,
    _SC_NPROCESSORS_CONF,
    _SC_NPROCESSORS_ONLN,
    _SC_PHYS_PAGES,
    _SC_AVPHYS_PAGES,
    _SC_ATEXIT_MAX,
    _SC_PASS_MAX,
    _SC_XOPEN_VERSION,
    _SC_XOPEN_XCU_VERSION,
    _SC_XOPEN_UNIX,
    _SC_XOPEN_CRYPT,
    _SC_XOPEN_ENH_I18N,
    _SC_XOPEN_SHM,
    _SC_2_CHAR_TERM,
    _SC_2_C_VERSION,
    _SC_2_UPE,
    _SC_XOPEN_XPG2,
    _SC_XOPEN_XPG3,
    _SC_XOPEN_XPG4,
    _SC_CHAR_BIT,
    _SC_CHAR_MAX,
    _SC_CHAR_MIN,
    _SC_INT_MAX,
    _SC_INT_MIN,
    _SC_LONG_BIT,
    _SC_WORD_BIT,
    _SC_MB_LEN_MAX,
    _SC_NZERO,
    _SC_SSIZE_MAX,
    _SC_SCHAR_MAX,
    _SC_SCHAR_MIN,
    _SC_SHRT_MAX,
    _SC_SHRT_MIN,
    _SC_UCHAR_MAX,
    _SC_UINT_MAX,
    _SC_ULONG_MAX,
    _SC_USHRT_MAX,
    _SC_NL_ARGMAX,
    _SC_NL_LANGMAX,
    _SC_NL_MSGMAX,
    _SC_NL_NMAX,
    _SC_NL_SETMAX,
    _SC_NL_TEXTMAX,
    _SC_XBS5_ILP32_OFF32,
    _SC_XBS5_ILP32_OFFBIG,
    _SC_XBS5_LP64_OFF64,
    _SC_XBS5_LPBIG_OFFBIG,
    _SC_XOPEN_LEGACY,
    _SC_XOPEN_REALTIME,
    _SC_XOPEN_REALTIME_THREADS,
    _SC_ADVISORY_INFO,
    _SC_BARRIERS,
    _SC_BASE,
    _SC_C_LANG_SUPPORT,
    _SC_C_LANG_SUPPORT_R,
    _SC_CLOCK_SELECTION,
    _SC_CPUTIME,
    _SC_THREAD_CPUTIME,
    _SC_DEVICE_IO,
    _SC_DEVICE_SPECIFIC,
    _SC_DEVICE_SPECIFIC_R,
    _SC_FD_MGMT,
    _SC_FIFO,
    _SC_PIPE,
    _SC_FILE_ATTRIBUTES,
    _SC_FILE_LOCKING,
    _SC_FILE_SYSTEM,
    _SC_MONOTONIC_CLOCK,
    _SC_MULTI_PROCESS,
    _SC_SINGLE_PROCESS,
    _SC_NETWORKING,
    _SC_READER_WRITER_LOCKS,
    _SC_SPIN_LOCKS,
    _SC_REGEXP,
    _SC_REGEX_VERSION,
    _SC_SHELL,
    _SC_SIGNALS,
    _SC_SPAWN,
    _SC_SPORADIC_SERVER,
    _SC_THREAD_SPORADIC_SERVER,
    _SC_SYSTEM_DATABASE,
    _SC_SYSTEM_DATABASE_R,
    _SC_TIMEOUTS,
    _SC_TYPED_MEMORY_OBJECTS,
    _SC_USER_GROUPS,
    _SC_USER_GROUPS_R,
    _SC_2_PBS,
    _SC_2_PBS_ACCOUNTING,
    _SC_2_PBS_LOCATE,
    _SC_2_PBS_MESSAGE,
    _SC_2_PBS_TRACK,
    _SC_SYMLOOP_MAX,
    _SC_STREAMS,
    _SC_2_PBS_CHECKPOINT,
    _SC_V6_ILP32_OFF32,
    _SC_V6_ILP32_OFFBIG,
    _SC_V6_LP64_OFF64,
    _SC_V6_LPBIG_OFFBIG,
    _SC_HOST_NAME_MAX,
    _SC_TRACE,
    _SC_TRACE_EVENT_FILTER,
    _SC_TRACE_INHERIT,
    _SC_TRACE_LOG,
    _SC_LEVEL1_ICACHE_SIZE,
    _SC_LEVEL1_ICACHE_ASSOC,
    _SC_LEVEL1_ICACHE_LINESIZE,
    _SC_LEVEL1_DCACHE_SIZE,
    _SC_LEVEL1_DCACHE_ASSOC,
    _SC_LEVEL1_DCACHE_LINESIZE,
    _SC_LEVEL2_CACHE_SIZE,
    _SC_LEVEL2_CACHE_ASSOC,
    _SC_LEVEL2_CACHE_LINESIZE,
    _SC_LEVEL3_CACHE_SIZE,
    _SC_LEVEL3_CACHE_ASSOC,
    _SC_LEVEL3_CACHE_LINESIZE,
    _SC_LEVEL4_CACHE_SIZE,
    _SC_LEVEL4_CACHE_ASSOC,
    _SC_LEVEL4_CACHE_LINESIZE,
    _SC_IPV6 = _SC_LEVEL1_ICACHE_SIZE + 50,
    _SC_RAW_SOCKETS,
    _SC_V7_ILP32_OFF32,
    _SC_V7_ILP32_OFFBIG,
    _SC_V7_LP64_OFF64,
    _SC_V7_LPBIG_OFFBIG,
    _SC_SS_REPL_MAX,
    _SC_TRACE_EVENT_NAME_MAX,
    _SC_TRACE_NAME_MAX,
    _SC_TRACE_SYS_MAX,
    _SC_TRACE_USER_EVENT_MAX,
    _SC_XOPEN_STREAMS,
    _SC_THREAD_ROBUST_PRIO_INHERIT,
    _SC_THREAD_ROBUST_PRIO_PROTECT
  };
enum
  {
    _CS_PATH,
    _CS_V6_WIDTH_RESTRICTED_ENVS,
    _CS_GNU_LIBC_VERSION,
    _CS_GNU_LIBPTHREAD_VERSION,
    _CS_V5_WIDTH_RESTRICTED_ENVS,
    _CS_V7_WIDTH_RESTRICTED_ENVS,
    _CS_LFS_CFLAGS = 1000,
    _CS_LFS_LDFLAGS,
    _CS_LFS_LIBS,
    _CS_LFS_LINTFLAGS,
    _CS_LFS64_CFLAGS,
    _CS_LFS64_LDFLAGS,
    _CS_LFS64_LIBS,
    _CS_LFS64_LINTFLAGS,
    _CS_XBS5_ILP32_OFF32_CFLAGS = 1100,
    _CS_XBS5_ILP32_OFF32_LDFLAGS,
    _CS_XBS5_ILP32_OFF32_LIBS,
    _CS_XBS5_ILP32_OFF32_LINTFLAGS,
    _CS_XBS5_ILP32_OFFBIG_CFLAGS,
    _CS_XBS5_ILP32_OFFBIG_LDFLAGS,
    _CS_XBS5_ILP32_OFFBIG_LIBS,
    _CS_XBS5_ILP32_OFFBIG_LINTFLAGS,
    _CS_XBS5_LP64_OFF64_CFLAGS,
    _CS_XBS5_LP64_OFF64_LDFLAGS,
    _CS_XBS5_LP64_OFF64_LIBS,
    _CS_XBS5_LP64_OFF64_LINTFLAGS,
    _CS_XBS5_LPBIG_OFFBIG_CFLAGS,
    _CS_XBS5_LPBIG_OFFBIG_LDFLAGS,
    _CS_XBS5_LPBIG_OFFBIG_LIBS,
    _CS_XBS5_LPBIG_OFFBIG_LINTFLAGS,
    _CS_POSIX_V6_ILP32_OFF32_CFLAGS,
    _CS_POSIX_V6_ILP32_OFF32_LDFLAGS,
    _CS_POSIX_V6_ILP32_OFF32_LIBS,
    _CS_POSIX_V6_ILP32_OFF32_LINTFLAGS,
    _CS_POSIX_V6_ILP32_OFFBIG_CFLAGS,
    _CS_POSIX_V6_ILP32_OFFBIG_LDFLAGS,
    _CS_POSIX_V6_ILP32_OFFBIG_LIBS,
    _CS_POSIX_V6_ILP32_OFFBIG_LINTFLAGS,
    _CS_POSIX_V6_LP64_OFF64_CFLAGS,
    _CS_POSIX_V6_LP64_OFF64_LDFLAGS,
    _CS_POSIX_V6_LP64_OFF64_LIBS,
    _CS_POSIX_V6_LP64_OFF64_LINTFLAGS,
    _CS_POSIX_V6_LPBIG_OFFBIG_CFLAGS,
    _CS_POSIX_V6_LPBIG_OFFBIG_LDFLAGS,
    _CS_POSIX_V6_LPBIG_OFFBIG_LIBS,
    _CS_POSIX_V6_LPBIG_OFFBIG_LINTFLAGS,
    _CS_POSIX_V7_ILP32_OFF32_CFLAGS,
    _CS_POSIX_V7_ILP32_OFF32_LDFLAGS,
    _CS_POSIX_V7_ILP32_OFF32_LIBS,
    _CS_POSIX_V7_ILP32_OFF32_LINTFLAGS,
    _CS_POSIX_V7_ILP32_OFFBIG_CFLAGS,
    _CS_POSIX_V7_ILP32_OFFBIG_LDFLAGS,
    _CS_POSIX_V7_ILP32_OFFBIG_LIBS,
    _CS_POSIX_V7_ILP32_OFFBIG_LINTFLAGS,
    _CS_POSIX_V7_LP64_OFF64_CFLAGS,
    _CS_POSIX_V7_LP64_OFF64_LDFLAGS,
    _CS_POSIX_V7_LP64_OFF64_LIBS,
    _CS_POSIX_V7_LP64_OFF64_LINTFLAGS,
    _CS_POSIX_V7_LPBIG_OFFBIG_CFLAGS,
    _CS_POSIX_V7_LPBIG_OFFBIG_LDFLAGS,
    _CS_POSIX_V7_LPBIG_OFFBIG_LIBS,
    _CS_POSIX_V7_LPBIG_OFFBIG_LINTFLAGS,
    _CS_V6_ENV,
    _CS_V7_ENV
  };
extern long int pathconf (__const char *__path, int __name)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern long int fpathconf (int __fd, int __name) __attribute__ ((__nothrow__ , __leaf__));
extern long int sysconf (int __name) __attribute__ ((__nothrow__ , __leaf__));
extern size_t confstr (int __name, char *__buf, size_t __len) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t getpid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t getppid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t getpgrp (void) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t __getpgid (__pid_t __pid) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t getpgid (__pid_t __pid) __attribute__ ((__nothrow__ , __leaf__));
extern int setpgid (__pid_t __pid, __pid_t __pgid) __attribute__ ((__nothrow__ , __leaf__));
extern int setpgrp (void) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t setsid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t getsid (__pid_t __pid) __attribute__ ((__nothrow__ , __leaf__));
extern __uid_t getuid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __uid_t geteuid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __gid_t getgid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __gid_t getegid (void) __attribute__ ((__nothrow__ , __leaf__));
extern int getgroups (int __size, __gid_t __list[]) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int setuid (__uid_t __uid) __attribute__ ((__nothrow__ , __leaf__));
extern int setreuid (__uid_t __ruid, __uid_t __euid) __attribute__ ((__nothrow__ , __leaf__));
extern int seteuid (__uid_t __uid) __attribute__ ((__nothrow__ , __leaf__));
extern int setgid (__gid_t __gid) __attribute__ ((__nothrow__ , __leaf__));
extern int setregid (__gid_t __rgid, __gid_t __egid) __attribute__ ((__nothrow__ , __leaf__));
extern int setegid (__gid_t __gid) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t fork (void) __attribute__ ((__nothrow__));
extern __pid_t vfork (void) __attribute__ ((__nothrow__ , __leaf__));
extern char *ttyname (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern int ttyname_r (int __fd, char *__buf, size_t __buflen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2))) ;
extern int isatty (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern int ttyslot (void) __attribute__ ((__nothrow__ , __leaf__));
extern int link (__const char *__from, __const char *__to)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2))) ;
extern int linkat (int __fromfd, __const char *__from, int __tofd,
     __const char *__to, int __flags)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4))) ;
extern int symlink (__const char *__from, __const char *__to)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2))) ;
extern ssize_t readlink (__const char *__restrict __path,
    char *__restrict __buf, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2))) ;
extern int symlinkat (__const char *__from, int __tofd,
        __const char *__to) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3))) ;
extern ssize_t readlinkat (int __fd, __const char *__restrict __path,
      char *__restrict __buf, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3))) ;
extern int unlink (__const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int unlinkat (int __fd, __const char *__name, int __flag)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int rmdir (__const char *__path) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern __pid_t tcgetpgrp (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern int tcsetpgrp (int __fd, __pid_t __pgrp_id) __attribute__ ((__nothrow__ , __leaf__));
extern char *getlogin (void);
extern int getlogin_r (char *__name, size_t __name_len) __attribute__ ((__nonnull__ (1)));
extern int setlogin (__const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int gethostname (char *__name, size_t __len) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sethostname (__const char *__name, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int sethostid (long int __id) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int getdomainname (char *__name, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int setdomainname (__const char *__name, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int vhangup (void) __attribute__ ((__nothrow__ , __leaf__));
extern int revoke (__const char *__file) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int profil (unsigned short int *__sample_buffer, size_t __size,
     size_t __offset, unsigned int __scale)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int acct (__const char *__name) __attribute__ ((__nothrow__ , __leaf__));
extern char *getusershell (void) __attribute__ ((__nothrow__ , __leaf__));
extern void endusershell (void) __attribute__ ((__nothrow__ , __leaf__));
extern void setusershell (void) __attribute__ ((__nothrow__ , __leaf__));
extern int daemon (int __nochdir, int __noclose) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int chroot (__const char *__path) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern char *getpass (__const char *__prompt) __attribute__ ((__nonnull__ (1)));
extern int fsync (int __fd);
extern long int gethostid (void);
extern void sync (void) __attribute__ ((__nothrow__ , __leaf__));
extern int getpagesize (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int getdtablesize (void) __attribute__ ((__nothrow__ , __leaf__));
extern int truncate (__const char *__file, __off_t __length)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int ftruncate (int __fd, __off_t __length) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int brk (void *__addr) __attribute__ ((__nothrow__ , __leaf__)) ;
extern void *sbrk (intptr_t __delta) __attribute__ ((__nothrow__ , __leaf__));
extern long int syscall (long int __sysno, ...) __attribute__ ((__nothrow__ , __leaf__));
extern int lockf (int __fd, int __cmd, __off_t __len) ;
extern int fdatasync (int __fildes);
extern char *ctermid (char *__s) __attribute__ ((__nothrow__ , __leaf__));


struct flock
  {
    short int l_type;
    short int l_whence;
    __off_t l_start;
    __off_t l_len;
    __pid_t l_pid;
  };


extern int fcntl (int __fd, int __cmd, ...);
extern int open (__const char *__file, int __oflag, ...) __attribute__ ((__nonnull__ (1)));
extern int openat (int __fd, __const char *__file, int __oflag, ...)
     __attribute__ ((__nonnull__ (2)));
extern int creat (__const char *__file, __mode_t __mode) __attribute__ ((__nonnull__ (1)));
extern int posix_fadvise (int __fd, __off_t __offset, __off_t __len,
     int __advise) __attribute__ ((__nothrow__ , __leaf__));
extern int posix_fallocate (int __fd, __off_t __offset, __off_t __len);

typedef unsigned char char_type;
typedef long code_int;
typedef unsigned long count_int;
typedef unsigned short count_short;
typedef unsigned long cmp_code_int;
union bytes {
    long word;
    struct {
 int dummy;
    } bytes;
};
int block_mode = 0x80;
int unlzw(in, out)
    int in, out;
{
    register char_type *stackp;
    code_int code;
    int finchar;
    code_int oldcode;
    code_int incode;
    long inbits;
    long posbits;
    int outpos;
    unsigned bitmask;
    code_int free_ent;
    code_int maxcode;
    code_int maxmaxcode;
    int n_bits;
    int rsize;
    maxbits = (inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
    block_mode = maxbits & 0x80;
    if ((maxbits & 0x60) != 0) {
 {if (!quiet) fprintf (stderr, "\n%s: %s: warning, unknown flags 0x%x\n", progname, ifname, maxbits & 0x60) ; if (exit_code == 0) exit_code = 2;};
    }
    maxbits &= 0x1f;
    maxmaxcode = (1L << (maxbits));
    if (maxbits > 16) {
 fprintf(stderr,
  "\n%s: %s: compressed with %d bits, can only handle %d bits\n",
  progname, ifname, maxbits, 16);
 exit_code = 1;
 return 1;
    }
    rsize = insize;
    maxcode = (1L << (n_bits = 9))-1;
    bitmask = (1<<n_bits)-1;
    oldcode = -1;
    finchar = 0;
    outpos = 0;
    posbits = inptr<<3;
    free_ent = ((block_mode) ? (256 +1) : 256);
    memset ((voidp)(prev), 0, (256));;
    for (code = 255 ; code >= 0 ; --code) {
 window[code] = (char_type)code;
    }
    do {
 register int i;
 int e;
 int o;
    resetbuf:
 e = insize-(o = (posbits>>3));
 for (i = 0 ; i < e ; ++i) {
     inbuf[i] = inbuf[i+o];
 }
 insize = e;
 posbits = 0;
 if (insize < 64) {
     if ((rsize = read(in, (char*)inbuf+insize, 0x8000)) == (-1)) {
  read_error();
     }
     insize += rsize;
     bytes_in += (ulg)rsize;
 }
 inbits = ((rsize != 0) ? ((long)insize - insize%n_bits)<<3 :
    ((long)insize<<3)-(n_bits-1));
 while (inbits > posbits) {
     if (free_ent > maxcode) {
  posbits = ((posbits-1) +
      ((n_bits<<3)-(posbits-1+(n_bits<<3))%(n_bits<<3)));
  ++n_bits;
  if (n_bits == maxbits) {
      maxcode = maxmaxcode;
  } else {
      maxcode = (1L << (n_bits))-1;
  }
  bitmask = (1<<n_bits)-1;
  goto resetbuf;
     }
     { register char_type *p = &(inbuf)[(posbits)>>3]; (code) = ((((long)(p[0]))|((long)(p[1])<<8)| ((long)(p[2])<<16))>>((posbits)&0x7))&(bitmask); (posbits) += (n_bits); };
     ;
     if (oldcode == -1) {
  if (code <= 256) error("corrupt input.");
  outbuf[outpos++] = (char_type)(finchar = (int)(oldcode=code));
  continue;
     }
     if (code == 256 && block_mode) {
  memset ((voidp)(prev), 0, (256));;
  free_ent = (256 +1) - 1;
  posbits = ((posbits-1) +
      ((n_bits<<3)-(posbits-1+(n_bits<<3))%(n_bits<<3)));
  maxcode = (1L << (n_bits = 9))-1;
  bitmask = (1<<n_bits)-1;
  goto resetbuf;
     }
     incode = code;
     stackp = ((char_type *)(&d_buf[0x8000 -1]));
     if (code >= free_ent) {
  if (code > free_ent) {
      if (!test && outpos > 0) {
   write_buf(out, (char*)outbuf, outpos);
   bytes_out += (ulg)outpos;
      }
      error(to_stdout ? "corrupt input." :
     "corrupt input. Use zcat to recover some data.");
  }
  *--stackp = (char_type)finchar;
  code = oldcode;
     }
     while ((cmp_code_int)code >= (cmp_code_int)256) {
  *--stackp = window[code];
  code = prev[code];
     }
     *--stackp = (char_type)(finchar = window[code]);
     {
  register int i;
  if (outpos+(i = (((char_type *)(&d_buf[0x8000 -1]))-stackp)) >= 16384) {
      do {
   if (i > 16384 -outpos) i = 16384 -outpos;
   if (i > 0) {
       memcpy(outbuf+outpos, stackp, i);
       outpos += i;
   }
   if (outpos >= 16384) {
       if (!test) {
    write_buf(out, (char*)outbuf, outpos);
    bytes_out += (ulg)outpos;
       }
       outpos = 0;
   }
   stackp+= i;
      } while ((i = (((char_type *)(&d_buf[0x8000 -1]))-stackp)) > 0);
  } else {
      memcpy(outbuf+outpos, stackp, i);
      outpos += i;
  }
     }
     if ((code = free_ent) < maxmaxcode) {
  prev[code] = (unsigned short)oldcode;
  window[code] = (char_type)finchar;
  free_ent = code+1;
     }
     oldcode = incode;
 }
    } while (rsize != 0);
    if (!test && outpos > 0) {
 write_buf(out, (char*)outbuf, outpos);
 bytes_out += (ulg)outpos;
    }
    return 0;
}
static ulg orig_len;
static int max_len;
static uch literal[256];
static int lit_base[25 +1];
static int leaves [25 +1];
static int parents[25 +1];
static int peek_bits;
static ulg un_bitbuf;
static int valid;
static void read_tree (void);
static void un_build_tree (void);
static void read_tree()
{
    int len;
    int base;
    int n;
    orig_len = 0;
    for (n = 1; n <= 4; n++) orig_len = (orig_len << 8) | (ulg)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
    max_len = (int)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
    if (max_len > 25) {
 error("invalid compressed data -- Huffman code > 32 bits");
    }
    n = 0;
    for (len = 1; len <= max_len; len++) {
 leaves[len] = (int)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
 n += leaves[len];
    }
    if (n > 256) {
 error("too many leaves in Huffman tree");
    }
    ;
    leaves[max_len]++;
    base = 0;
    for (len = 1; len <= max_len; len++) {
 lit_base[len] = base;
 for (n = leaves[len]; n > 0; n--) {
     literal[base++] = (uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
 }
    }
    leaves[max_len]++;
}
static void un_build_tree()
{
    int nodes = 0;
    int len;
    uch *prefixp;
    for (len = max_len; len >= 1; len--) {
 nodes >>= 1;
 parents[len] = nodes;
 lit_base[len] -= nodes;
 nodes += leaves[len];
    }
    peek_bits = ((max_len) <= (12) ? (max_len) : (12));
    prefixp = &outbuf[1<<peek_bits];
    for (len = 1; len <= peek_bits; len++) {
 int prefixes = leaves[len] << (peek_bits-len);
 while (prefixes--) *--prefixp = (uch)len;
    }
    while (prefixp > outbuf) *--prefixp = 0;
}
int unpack(in, out)
    int in, out;
{
    int len;
    unsigned eob;
    register unsigned peek;
    unsigned peek_mask;
    ifd = in;
    ofd = out;
    read_tree();
    un_build_tree();
    (valid = 0, un_bitbuf = 0);
    peek_mask = (1<<peek_bits)-1;
    eob = leaves[max_len]-1;
    ;
    for (;;) {
 { while (valid < (peek_bits)) un_bitbuf = (un_bitbuf<<8) | (ulg)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)), valid += 8; peek = (un_bitbuf >> (valid-(peek_bits))) & (peek_mask); };
 len = outbuf[peek];
 if (len > 0) {
     peek >>= peek_bits - len;
 } else {
     ulg mask = peek_mask;
     len = peek_bits;
     do {
                len++, mask = (mask<<1)+1;
  { while (valid < (len)) un_bitbuf = (un_bitbuf<<8) | (ulg)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)), valid += 8; peek = (un_bitbuf >> (valid-(len))) & (mask); };
     } while (peek < (unsigned)parents[len]);
 }
 if (peek == eob && len == max_len) break;
 {window[outcnt++]=(uch)(literal[peek+lit_base[len]]); if (outcnt==0x8000) flush_window();};
 ;
 (valid -= (len));
    }
    flush_window();
    ;
    if (orig_len != (ulg)bytes_out) {
 error("invalid compressed data--length error");
    }
    return 0;
}
int decrypt;
char *key;
int pkzip = 0;
int ext_header = 0;
int check_zipfile(in)
    int in;
{
    uch *h = inbuf + inptr;
    ifd = in;
    inptr += 30 + ((ush)(uch)((h + 26)[0]) | ((ush)(uch)((h + 26)[1]) << 8)) + ((ush)(uch)((h + 28)[0]) | ((ush)(uch)((h + 28)[1]) << 8));
    if (inptr > insize || ((ulg)(((ush)(uch)((h)[0]) | ((ush)(uch)((h)[1]) << 8))) | ((ulg)(((ush)(uch)(((h)+2)[0]) | ((ush)(uch)(((h)+2)[1]) << 8))) << 16)) != 0x04034b50L) {
 fprintf(stderr, "\n%s: %s: not a valid zip file\n",
  progname, ifname);
 exit_code = 1;
 return 1;
    }
    method = h[8];
    if (method != 0 && method != 8) {
 fprintf(stderr,
  "\n%s: %s: first entry not deflated or stored -- use unzip\n",
  progname, ifname);
 exit_code = 1;
 return 1;
    }
    if ((decrypt = h[6] & 1) != 0) {
 fprintf(stderr, "\n%s: %s: encrypted file -- use unzip\n",
  progname, ifname);
 exit_code = 1;
 return 1;
    }
    ext_header = (h[6] & 8) != 0;
    pkzip = 1;
    return 0;
}
int unzip(in, out)
    int in, out;
{
    ulg orig_crc = 0;
    ulg orig_len = 0;
    int n;
    uch buf[16];
    ifd = in;
    ofd = out;
    updcrc(((void *)0), 0);
    if (pkzip && !ext_header) {
 orig_crc = ((ulg)(((ush)(uch)((inbuf + 14)[0]) | ((ush)(uch)((inbuf + 14)[1]) << 8))) | ((ulg)(((ush)(uch)(((inbuf + 14)+2)[0]) | ((ush)(uch)(((inbuf + 14)+2)[1]) << 8))) << 16));
 orig_len = ((ulg)(((ush)(uch)((inbuf + 22)[0]) | ((ush)(uch)((inbuf + 22)[1]) << 8))) | ((ulg)(((ush)(uch)(((inbuf + 22)+2)[0]) | ((ush)(uch)(((inbuf + 22)+2)[1]) << 8))) << 16));
    }
    if (method == 8) {
 int res = inflate();
 if (res == 3) {
     error("out of memory");
 } else if (res != 0) {
     error("invalid compressed data--format violated");
 }
    } else if (pkzip && method == 0) {
 register ulg n = ((ulg)(((ush)(uch)((inbuf + 22)[0]) | ((ush)(uch)((inbuf + 22)[1]) << 8))) | ((ulg)(((ush)(uch)(((inbuf + 22)+2)[0]) | ((ush)(uch)(((inbuf + 22)+2)[1]) << 8))) << 16));
 if (n != ((ulg)(((ush)(uch)((inbuf + 18)[0]) | ((ush)(uch)((inbuf + 18)[1]) << 8))) | ((ulg)(((ush)(uch)(((inbuf + 18)+2)[0]) | ((ush)(uch)(((inbuf + 18)+2)[1]) << 8))) << 16)) - (decrypt ? 12 : 0)) {
     fprintf(stderr, "len %ld, siz %ld\n", n, ((ulg)(((ush)(uch)((inbuf + 18)[0]) | ((ush)(uch)((inbuf + 18)[1]) << 8))) | ((ulg)(((ush)(uch)(((inbuf + 18)+2)[0]) | ((ush)(uch)(((inbuf + 18)+2)[1]) << 8))) << 16)));
     error("invalid compressed data--length mismatch");
 }
 while (n--) {
     uch c = (uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
     {window[outcnt++]=(uch)(c); if (outcnt==0x8000) flush_window();};
 }
 flush_window();
    } else {
 error("internal error, invalid method");
    }
    if (!pkzip) {
 for (n = 0; n < 8; n++) {
     buf[n] = (uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
 }
 orig_crc = ((ulg)(((ush)(uch)((buf)[0]) | ((ush)(uch)((buf)[1]) << 8))) | ((ulg)(((ush)(uch)(((buf)+2)[0]) | ((ush)(uch)(((buf)+2)[1]) << 8))) << 16));
 orig_len = ((ulg)(((ush)(uch)((buf+4)[0]) | ((ush)(uch)((buf+4)[1]) << 8))) | ((ulg)(((ush)(uch)(((buf+4)+2)[0]) | ((ush)(uch)(((buf+4)+2)[1]) << 8))) << 16));
    } else if (ext_header) {
 for (n = 0; n < 16; n++) {
     buf[n] = (uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
 }
 orig_crc = ((ulg)(((ush)(uch)((buf+4)[0]) | ((ush)(uch)((buf+4)[1]) << 8))) | ((ulg)(((ush)(uch)(((buf+4)+2)[0]) | ((ush)(uch)(((buf+4)+2)[1]) << 8))) << 16));
 orig_len = ((ulg)(((ush)(uch)((buf+12)[0]) | ((ush)(uch)((buf+12)[1]) << 8))) | ((ulg)(((ush)(uch)(((buf+12)+2)[0]) | ((ush)(uch)(((buf+12)+2)[1]) << 8))) << 16));
    }
    if (orig_crc != updcrc(outbuf, 0)) {
 error("invalid compressed data--crc error");
    }
    if (orig_len != (ulg)bytes_out) {
 error("invalid compressed data--length error");
    }
    if (pkzip && inptr + 4 < insize && ((ulg)(((ush)(uch)((inbuf+inptr)[0]) | ((ush)(uch)((inbuf+inptr)[1]) << 8))) | ((ulg)(((ush)(uch)(((inbuf+inptr)+2)[0]) | ((ush)(uch)(((inbuf+inptr)+2)[1]) << 8))) << 16)) == 0x04034b50L) {
 if (to_stdout) {
     {if (!quiet) fprintf (stderr, "%s: %s has more than one entry--rest ignored\n", progname, ifname) ; if (exit_code == 0) exit_code = 2;};
 } else {
     fprintf(stderr,
      "%s: %s has more than one entry -- unchanged\n",
      progname, ifname);
     exit_code = 1;
     ext_header = pkzip = 0;
     return 1;
 }
    }
    ext_header = pkzip = 0;
    return 0;
}
extern ulg crc_32_tab[];
int copy(in, out)
    int in, out;
{
    (*__errno_location ()) = 0;
    while (insize != 0 && (int)insize != (-1)) {
 write_buf(out, (char*)inbuf, insize);
 bytes_out += insize;
 insize = read(in, (char*)inbuf, 0x8000);
    }
    if ((int)insize == (-1) && (*__errno_location ()) != 0) {
 read_error();
    }
    bytes_in = bytes_out;
    return 0;
}
ulg updcrc(s, n)
    uch *s;
    unsigned n;
{
    register ulg c;
    static ulg crc = (ulg)0xffffffffL;
    if (s == ((void *)0)) {
 c = 0xffffffffL;
    } else {
 c = crc;
        if (n) do {
            c = crc_32_tab[((int)c ^ (*s++)) & 0xff] ^ (c >> 8);
        } while (--n);
    }
    crc = c;
    return c ^ 0xffffffffL;
}
void clear_bufs()
{
    outcnt = 0;
    insize = inptr = 0;
    bytes_in = bytes_out = 0L;
}
int fill_inbuf(eof_ok)
    int eof_ok;
{
    int len;
    insize = 0;
    (*__errno_location ()) = 0;
    do {
 len = read(ifd, (char*)inbuf+insize, 0x8000 -insize);
        if (len == 0 || len == (-1)) break;
 insize += len;
    } while (insize < 0x8000);
    if (insize == 0) {
 if (eof_ok) return (-1);
 read_error();
    }
    bytes_in += (ulg)insize;
    inptr = 1;
    return inbuf[0];
}
void flush_outbuf()
{
    if (outcnt == 0) return;
    write_buf(ofd, (char *)outbuf, outcnt);
    bytes_out += (ulg)outcnt;
    outcnt = 0;
}
void flush_window()
{
    if (outcnt == 0) return;
    updcrc(window, outcnt);
    if (!test) {
 write_buf(ofd, (char *)window, outcnt);
    }
    bytes_out += (ulg)outcnt;
    outcnt = 0;
}
void write_buf(fd, buf, cnt)
    int fd;
    voidp buf;
    unsigned cnt;
{
    unsigned n;
    while ((n = write(fd, buf, cnt)) != cnt) {
 if (n == (unsigned)(-1)) {
     write_error();
 }
 cnt -= n;
 buf = (voidp)((char*)buf+n);
    }
}
char *strlwr(s)
    char *s;
{
    char *t;
    for (t = s; *t; t++) *t = (((*__ctype_b_loc ())[(int) ((*t))] & (unsigned short int) _ISupper) ? (*t)-'A'+'a' : (*t));
    return s;
}
char *basename(fname)
    char *fname;
{
    char *p;
    if ((p = strrchr(fname, '/')) != ((void *)0)) fname = p+1;
    if (('A') == 'a') strlwr(fname);
    return fname;
}
void make_simple_name(name)
    char *name;
{
    char *p = strrchr(name, '.');
    if (p == ((void *)0)) return;
    if (p == name) p++;
    do {
        if (*--p == '.') *p = '_';
    } while (p != name);
}
char *add_envopt(argcp, argvp, env)
    int *argcp;
    char ***argvp;
    char *env;
{
    char *p;
    char **oargv;
    char **nargv;
    int oargc = *argcp;
    int nargc = 0;
    env = (char*)getenv(env);
    if (env == ((void *)0)) return ((void *)0);
    p = (char*)xmalloc(strlen(env)+1);
    env = strcpy(p, env);
    for (p = env; *p; nargc++ ) {
 p += strspn(p, " \t");
 if (*p == '\0') break;
 p += strcspn(p, " \t");
 if (*p) *p++ = '\0';
    }
    if (nargc == 0) {
 free(env);
 return ((void *)0);
    }
    *argcp += nargc;
    nargv = (char**)calloc(*argcp+1, sizeof(char *));
    if (nargv == ((void *)0)) error("out of memory");
    oargv = *argvp;
    *argvp = nargv;
    if (oargc-- < 0) error("argc<=0");
    *(nargv++) = *(oargv++);
    for (p = env; nargc > 0; nargc--) {
 p += strspn(p, " \t");
 *(nargv++) = p;
 while (*p++) ;
    }
    while (oargc--) *(nargv++) = *(oargv++);
    *nargv = ((void *)0);
    return env;
}
void error(m)
    char *m;
{
    fprintf(stderr, "\n%s: %s: %s\n", progname, ifname, m);
    abort_gzip();
}
void warn(a, b)
    char *a, *b;
{
    {if (!quiet) fprintf (stderr, "%s: %s: warning: %s%s\n", progname, ifname, a, b) ; if (exit_code == 0) exit_code = 2;};
}
void read_error()
{
    fprintf(stderr, "\n%s: ", progname);
    if ((*__errno_location ()) != 0) {
 perror(ifname);
    } else {
 fprintf(stderr, "%s: unexpected end of file\n", ifname);
    }
    abort_gzip();
}
void write_error()
{
    fprintf(stderr, "\n%s: ", progname);
    perror(ofname);
    abort_gzip();
}
void display_ratio(num, den, file)
    long num;
    long den;
    FILE *file;
{
    long ratio;
    if (den == 0)
 {
 ratio = 0;
    } else if (den < 2147483L) {
 ratio = 1000L*num/den;
    } else {
 ratio = num/(den/1000L);
    }
    if (ratio < 0) {
 _IO_putc ('-', file);
 ratio = -ratio;
    } else {
 _IO_putc (' ', file);
    }
    fprintf(file, "%2ld.%1ld%%", ratio / 10L, ratio % 10L);
}
voidp xmalloc (size)
    unsigned size;
{
    voidp cp = (voidp)malloc (size);
    if (cp == ((void *)0)) error("out of memory");
    return cp;
}
ulg crc_32_tab[] = {
  0x00000000L, 0x77073096L, 0xee0e612cL, 0x990951baL, 0x076dc419L,
  0x706af48fL, 0xe963a535L, 0x9e6495a3L, 0x0edb8832L, 0x79dcb8a4L,
  0xe0d5e91eL, 0x97d2d988L, 0x09b64c2bL, 0x7eb17cbdL, 0xe7b82d07L,
  0x90bf1d91L, 0x1db71064L, 0x6ab020f2L, 0xf3b97148L, 0x84be41deL,
  0x1adad47dL, 0x6ddde4ebL, 0xf4d4b551L, 0x83d385c7L, 0x136c9856L,
  0x646ba8c0L, 0xfd62f97aL, 0x8a65c9ecL, 0x14015c4fL, 0x63066cd9L,
  0xfa0f3d63L, 0x8d080df5L, 0x3b6e20c8L, 0x4c69105eL, 0xd56041e4L,
  0xa2677172L, 0x3c03e4d1L, 0x4b04d447L, 0xd20d85fdL, 0xa50ab56bL,
  0x35b5a8faL, 0x42b2986cL, 0xdbbbc9d6L, 0xacbcf940L, 0x32d86ce3L,
  0x45df5c75L, 0xdcd60dcfL, 0xabd13d59L, 0x26d930acL, 0x51de003aL,
  0xc8d75180L, 0xbfd06116L, 0x21b4f4b5L, 0x56b3c423L, 0xcfba9599L,
  0xb8bda50fL, 0x2802b89eL, 0x5f058808L, 0xc60cd9b2L, 0xb10be924L,
  0x2f6f7c87L, 0x58684c11L, 0xc1611dabL, 0xb6662d3dL, 0x76dc4190L,
  0x01db7106L, 0x98d220bcL, 0xefd5102aL, 0x71b18589L, 0x06b6b51fL,
  0x9fbfe4a5L, 0xe8b8d433L, 0x7807c9a2L, 0x0f00f934L, 0x9609a88eL,
  0xe10e9818L, 0x7f6a0dbbL, 0x086d3d2dL, 0x91646c97L, 0xe6635c01L,
  0x6b6b51f4L, 0x1c6c6162L, 0x856530d8L, 0xf262004eL, 0x6c0695edL,
  0x1b01a57bL, 0x8208f4c1L, 0xf50fc457L, 0x65b0d9c6L, 0x12b7e950L,
  0x8bbeb8eaL, 0xfcb9887cL, 0x62dd1ddfL, 0x15da2d49L, 0x8cd37cf3L,
  0xfbd44c65L, 0x4db26158L, 0x3ab551ceL, 0xa3bc0074L, 0xd4bb30e2L,
  0x4adfa541L, 0x3dd895d7L, 0xa4d1c46dL, 0xd3d6f4fbL, 0x4369e96aL,
  0x346ed9fcL, 0xad678846L, 0xda60b8d0L, 0x44042d73L, 0x33031de5L,
  0xaa0a4c5fL, 0xdd0d7cc9L, 0x5005713cL, 0x270241aaL, 0xbe0b1010L,
  0xc90c2086L, 0x5768b525L, 0x206f85b3L, 0xb966d409L, 0xce61e49fL,
  0x5edef90eL, 0x29d9c998L, 0xb0d09822L, 0xc7d7a8b4L, 0x59b33d17L,
  0x2eb40d81L, 0xb7bd5c3bL, 0xc0ba6cadL, 0xedb88320L, 0x9abfb3b6L,
  0x03b6e20cL, 0x74b1d29aL, 0xead54739L, 0x9dd277afL, 0x04db2615L,
  0x73dc1683L, 0xe3630b12L, 0x94643b84L, 0x0d6d6a3eL, 0x7a6a5aa8L,
  0xe40ecf0bL, 0x9309ff9dL, 0x0a00ae27L, 0x7d079eb1L, 0xf00f9344L,
  0x8708a3d2L, 0x1e01f268L, 0x6906c2feL, 0xf762575dL, 0x806567cbL,
  0x196c3671L, 0x6e6b06e7L, 0xfed41b76L, 0x89d32be0L, 0x10da7a5aL,
  0x67dd4accL, 0xf9b9df6fL, 0x8ebeeff9L, 0x17b7be43L, 0x60b08ed5L,
  0xd6d6a3e8L, 0xa1d1937eL, 0x38d8c2c4L, 0x4fdff252L, 0xd1bb67f1L,
  0xa6bc5767L, 0x3fb506ddL, 0x48b2364bL, 0xd80d2bdaL, 0xaf0a1b4cL,
  0x36034af6L, 0x41047a60L, 0xdf60efc3L, 0xa867df55L, 0x316e8eefL,
  0x4669be79L, 0xcb61b38cL, 0xbc66831aL, 0x256fd2a0L, 0x5268e236L,
  0xcc0c7795L, 0xbb0b4703L, 0x220216b9L, 0x5505262fL, 0xc5ba3bbeL,
  0xb2bd0b28L, 0x2bb45a92L, 0x5cb36a04L, 0xc2d7ffa7L, 0xb5d0cf31L,
  0x2cd99e8bL, 0x5bdeae1dL, 0x9b64c2b0L, 0xec63f226L, 0x756aa39cL,
  0x026d930aL, 0x9c0906a9L, 0xeb0e363fL, 0x72076785L, 0x05005713L,
  0x95bf4a82L, 0xe2b87a14L, 0x7bb12baeL, 0x0cb61b38L, 0x92d28e9bL,
  0xe5d5be0dL, 0x7cdcefb7L, 0x0bdbdf21L, 0x86d3d2d4L, 0xf1d4e242L,
  0x68ddb3f8L, 0x1fda836eL, 0x81be16cdL, 0xf6b9265bL, 0x6fb077e1L,
  0x18b74777L, 0x88085ae6L, 0xff0f6a70L, 0x66063bcaL, 0x11010b5cL,
  0x8f659effL, 0xf862ae69L, 0x616bffd3L, 0x166ccf45L, 0xa00ae278L,
  0xd70dd2eeL, 0x4e048354L, 0x3903b3c2L, 0xa7672661L, 0xd06016f7L,
  0x4969474dL, 0x3e6e77dbL, 0xaed16a4aL, 0xd9d65adcL, 0x40df0b66L,
  0x37d83bf0L, 0xa9bcae53L, 0xdebb9ec5L, 0x47b2cf7fL, 0x30b5ffe9L,
  0xbdbdf21cL, 0xcabac28aL, 0x53b39330L, 0x24b4a3a6L, 0xbad03605L,
  0xcdd70693L, 0x54de5729L, 0x23d967bfL, 0xb3667a2eL, 0xc4614ab8L,
  0x5d681b02L, 0x2a6f2b94L, 0xb40bbe37L, 0xc30c8ea1L, 0x5a05df1bL,
  0x2d02ef8dL
};
static ulg crc;
long header_bytes;
int zip(in, out)
    int in, out;
{
    uch flags = 0;
    ush attr = 0;
    ush deflate_flags = 0;
    ifd = in;
    ofd = out;
    outcnt = 0;
    method = 8;
    {outbuf[outcnt++]=(uch)("\037\213"[0]); if (outcnt==16384) flush_outbuf();};
    {outbuf[outcnt++]=(uch)("\037\213"[1]); if (outcnt==16384) flush_outbuf();};
    {outbuf[outcnt++]=(uch)(8); if (outcnt==16384) flush_outbuf();};
    if (save_orig_name) {
 flags |= 0x08;
    }
    {outbuf[outcnt++]=(uch)(flags); if (outcnt==16384) flush_outbuf();};
    { { if (outcnt < 16384 -2) { outbuf[outcnt++] = (uch) (((time_stamp) & 0xffff) & 0xff); outbuf[outcnt++] = (uch) ((ush)((time_stamp) & 0xffff) >> 8); } else { {outbuf[outcnt++]=(uch)((uch)(((time_stamp) & 0xffff) & 0xff)); if (outcnt==16384) flush_outbuf();}; {outbuf[outcnt++]=(uch)((uch)((ush)((time_stamp) & 0xffff) >> 8)); if (outcnt==16384) flush_outbuf();}; } }; { if (outcnt < 16384 -2) { outbuf[outcnt++] = (uch) ((((ulg)(time_stamp)) >> 16) & 0xff); outbuf[outcnt++] = (uch) ((ush)(((ulg)(time_stamp)) >> 16) >> 8); } else { {outbuf[outcnt++]=(uch)((uch)((((ulg)(time_stamp)) >> 16) & 0xff)); if (outcnt==16384) flush_outbuf();}; {outbuf[outcnt++]=(uch)((uch)((ush)(((ulg)(time_stamp)) >> 16) >> 8)); if (outcnt==16384) flush_outbuf();}; } }; };
    crc = updcrc(0, 0);
    bi_init(out);
    ct_init(&attr, &method);
    lm_init(level, &deflate_flags);
    {outbuf[outcnt++]=(uch)((uch)deflate_flags); if (outcnt==16384) flush_outbuf();};
    {outbuf[outcnt++]=(uch)(0x03); if (outcnt==16384) flush_outbuf();};
    if (save_orig_name) {
 char *p = basename(ifname);
 do {
     {outbuf[outcnt++]=(uch)(*p); if (outcnt==16384) flush_outbuf();};
 } while (*p++);
    }
    header_bytes = (long)outcnt;
    (void)deflate();
    { { if (outcnt < 16384 -2) { outbuf[outcnt++] = (uch) (((crc) & 0xffff) & 0xff); outbuf[outcnt++] = (uch) ((ush)((crc) & 0xffff) >> 8); } else { {outbuf[outcnt++]=(uch)((uch)(((crc) & 0xffff) & 0xff)); if (outcnt==16384) flush_outbuf();}; {outbuf[outcnt++]=(uch)((uch)((ush)((crc) & 0xffff) >> 8)); if (outcnt==16384) flush_outbuf();}; } }; { if (outcnt < 16384 -2) { outbuf[outcnt++] = (uch) ((((ulg)(crc)) >> 16) & 0xff); outbuf[outcnt++] = (uch) ((ush)(((ulg)(crc)) >> 16) >> 8); } else { {outbuf[outcnt++]=(uch)((uch)((((ulg)(crc)) >> 16) & 0xff)); if (outcnt==16384) flush_outbuf();}; {outbuf[outcnt++]=(uch)((uch)((ush)(((ulg)(crc)) >> 16) >> 8)); if (outcnt==16384) flush_outbuf();}; } }; };
    { { if (outcnt < 16384 -2) { outbuf[outcnt++] = (uch) (((bytes_in) & 0xffff) & 0xff); outbuf[outcnt++] = (uch) ((ush)((bytes_in) & 0xffff) >> 8); } else { {outbuf[outcnt++]=(uch)((uch)(((bytes_in) & 0xffff) & 0xff)); if (outcnt==16384) flush_outbuf();}; {outbuf[outcnt++]=(uch)((uch)((ush)((bytes_in) & 0xffff) >> 8)); if (outcnt==16384) flush_outbuf();}; } }; { if (outcnt < 16384 -2) { outbuf[outcnt++] = (uch) ((((ulg)(bytes_in)) >> 16) & 0xff); outbuf[outcnt++] = (uch) ((ush)(((ulg)(bytes_in)) >> 16) >> 8); } else { {outbuf[outcnt++]=(uch)((uch)((((ulg)(bytes_in)) >> 16) & 0xff)); if (outcnt==16384) flush_outbuf();}; {outbuf[outcnt++]=(uch)((uch)((ush)(((ulg)(bytes_in)) >> 16) >> 8)); if (outcnt==16384) flush_outbuf();}; } }; };
    header_bytes += 2*sizeof(long);
    flush_outbuf();
    return 0;
}
int file_read(buf, size)
    char *buf;
    unsigned size;
{
    unsigned len;
    ;
    len = read(ifd, buf, size);
    if (len == (unsigned)(-1) || len == 0) return (int)len;
    crc = updcrc((uch*)buf, len);
    bytes_in += (ulg)len;
    return (int)len;
}
static char *license_msg[] = {
"   Copyright (C) 1992-1993 Jean-loup Gailly",
"   This program is free software; you can redistribute it and/or modify",
"   it under the terms of the GNU General Public License as published by",
"   the Free Software Foundation; either version 2, or (at your option)",
"   any later version.",
"",
"   This program is distributed in the hope that it will be useful,",
"   but WITHOUT ANY WARRANTY; without even the implied warranty of",
"   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the",
"   GNU General Public License for more details.",
"",
"   You should have received a copy of the GNU General Public License",
"   along with this program; if not, write to the Free Software",
"   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.",
0};


struct tm
{
  int tm_sec;
  int tm_min;
  int tm_hour;
  int tm_mday;
  int tm_mon;
  int tm_year;
  int tm_wday;
  int tm_yday;
  int tm_isdst;
  long int tm_gmtoff;
  __const char *tm_zone;
};


struct itimerspec
  {
    struct timespec it_interval;
    struct timespec it_value;
  };
struct sigevent;

extern clock_t clock (void) __attribute__ ((__nothrow__ , __leaf__));
extern time_t time (time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));
extern double difftime (time_t __time1, time_t __time0)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern time_t mktime (struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));
extern size_t strftime (char *__restrict __s, size_t __maxsize,
   __const char *__restrict __format,
   __const struct tm *__restrict __tp) __attribute__ ((__nothrow__ , __leaf__));

extern size_t strftime_l (char *__restrict __s, size_t __maxsize,
     __const char *__restrict __format,
     __const struct tm *__restrict __tp,
     __locale_t __loc) __attribute__ ((__nothrow__ , __leaf__));

extern struct tm *gmtime (__const time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));
extern struct tm *localtime (__const time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));

extern struct tm *gmtime_r (__const time_t *__restrict __timer,
       struct tm *__restrict __tp) __attribute__ ((__nothrow__ , __leaf__));
extern struct tm *localtime_r (__const time_t *__restrict __timer,
          struct tm *__restrict __tp) __attribute__ ((__nothrow__ , __leaf__));

extern char *asctime (__const struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));
extern char *ctime (__const time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));

extern char *asctime_r (__const struct tm *__restrict __tp,
   char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__));
extern char *ctime_r (__const time_t *__restrict __timer,
        char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__));
extern char *__tzname[2];
extern int __daylight;
extern long int __timezone;
extern char *tzname[2];
extern void tzset (void) __attribute__ ((__nothrow__ , __leaf__));
extern int daylight;
extern long int timezone;
extern int stime (__const time_t *__when) __attribute__ ((__nothrow__ , __leaf__));
extern time_t timegm (struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));
extern time_t timelocal (struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));
extern int dysize (int __year) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int nanosleep (__const struct timespec *__requested_time,
        struct timespec *__remaining);
extern int clock_getres (clockid_t __clock_id, struct timespec *__res) __attribute__ ((__nothrow__ , __leaf__));
extern int clock_gettime (clockid_t __clock_id, struct timespec *__tp) __attribute__ ((__nothrow__ , __leaf__));
extern int clock_settime (clockid_t __clock_id, __const struct timespec *__tp)
     __attribute__ ((__nothrow__ , __leaf__));
extern int clock_nanosleep (clockid_t __clock_id, int __flags,
       __const struct timespec *__req,
       struct timespec *__rem);
extern int clock_getcpuclockid (pid_t __pid, clockid_t *__clock_id) __attribute__ ((__nothrow__ , __leaf__));
extern int timer_create (clockid_t __clock_id,
    struct sigevent *__restrict __evp,
    timer_t *__restrict __timerid) __attribute__ ((__nothrow__ , __leaf__));
extern int timer_delete (timer_t __timerid) __attribute__ ((__nothrow__ , __leaf__));
extern int timer_settime (timer_t __timerid, int __flags,
     __const struct itimerspec *__restrict __value,
     struct itimerspec *__restrict __ovalue) __attribute__ ((__nothrow__ , __leaf__));
extern int timer_gettime (timer_t __timerid, struct itimerspec *__value)
     __attribute__ ((__nothrow__ , __leaf__));
extern int timer_getoverrun (timer_t __timerid) __attribute__ ((__nothrow__ , __leaf__));


struct dirent
  {
    __ino_t d_ino;
    __off_t d_off;
    unsigned short int d_reclen;
    unsigned char d_type;
    char d_name[256];
  };
enum
  {
    DT_UNKNOWN = 0,
    DT_FIFO = 1,
    DT_CHR = 2,
    DT_DIR = 4,
    DT_BLK = 6,
    DT_REG = 8,
    DT_LNK = 10,
    DT_SOCK = 12,
    DT_WHT = 14
  };
typedef struct __dirstream DIR;
extern DIR *opendir (__const char *__name) __attribute__ ((__nonnull__ (1)));
extern DIR *fdopendir (int __fd);
extern int closedir (DIR *__dirp) __attribute__ ((__nonnull__ (1)));
extern struct dirent *readdir (DIR *__dirp) __attribute__ ((__nonnull__ (1)));
extern int readdir_r (DIR *__restrict __dirp,
        struct dirent *__restrict __entry,
        struct dirent **__restrict __result)
     __attribute__ ((__nonnull__ (1, 2, 3)));
extern void rewinddir (DIR *__dirp) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void seekdir (DIR *__dirp, long int __pos) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern long int telldir (DIR *__dirp) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int dirfd (DIR *__dirp) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int scandir (__const char *__restrict __dir,
      struct dirent ***__restrict __namelist,
      int (*__selector) (__const struct dirent *),
      int (*__cmp) (__const struct dirent **,
      __const struct dirent **))
     __attribute__ ((__nonnull__ (1, 2)));
extern int alphasort (__const struct dirent **__e1,
        __const struct dirent **__e2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern __ssize_t getdirentries (int __fd, char *__restrict __buf,
    size_t __nbytes,
    __off_t *__restrict __basep)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)));

   typedef struct dirent dir_type;

struct utimbuf
  {
    __time_t actime;
    __time_t modtime;
  };
extern int utime (__const char *__file,
    __const struct utimbuf *__file_times)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

typedef void (*sig_type) (int);
uch inbuf[0x8000 +64];
uch outbuf[16384 +2048];
ush d_buf[0x8000];
uch window[2L*0x8000];
    ush prev[1L<<16];
int ascii = 0;
int to_stdout = 0;
int decompress = 0;
int force = 0;
int no_name = -1;
int no_time = -1;
int recursive = 0;
int list = 0;
int verbose = 0;
int quiet = 0;
int do_lzw = 0;
int test = 0;
int foreground;
char *progname;
int maxbits = 16;
int method = 8;
int level = 6;
int exit_code = 0;
int save_orig_name;
int last_member;
int part_nb;
long time_stamp;
long ifile_size;
char *env;
char **args = ((void *)0);
char z_suffix[30 +1];
int z_len;
long bytes_in;
long bytes_out;
long total_in = 0;
long total_out = 0;
char ifname[1024];
char ofname[1024];
int remove_ofname = 0;
struct stat istat;
int ifd;
int ofd;
unsigned insize;
unsigned inptr;
unsigned outcnt;
struct option longopts[] =
{
    {"ascii", 0, 0, 'a'},
    {"to-stdout", 0, 0, 'c'},
    {"stdout", 0, 0, 'c'},
    {"decompress", 0, 0, 'd'},
    {"uncompress", 0, 0, 'd'},
    {"force", 0, 0, 'f'},
    {"help", 0, 0, 'h'},
    {"list", 0, 0, 'l'},
    {"license", 0, 0, 'L'},
    {"no-name", 0, 0, 'n'},
    {"name", 0, 0, 'N'},
    {"quiet", 0, 0, 'q'},
    {"silent", 0, 0, 'q'},
    {"recursive", 0, 0, 'r'},
    {"suffix", 1, 0, 'S'},
    {"test", 0, 0, 't'},
    {"no-time", 0, 0, 'T'},
    {"verbose", 0, 0, 'v'},
    {"version", 0, 0, 'V'},
    {"fast", 0, 0, '1'},
    {"best", 0, 0, '9'},
    {"lzw", 0, 0, 'Z'},
    {"bits", 1, 0, 'b'},
    { 0, 0, 0, 0 }
};
static void usage (void);
static void help (void);
static void license (void);
static void version (void);
static void treat_stdin (void);
static void treat_file (char *iname);
static int create_outfile (void);
static int do_stat (char *name, struct stat *sbuf);
static char *get_suffix (char *name);
static int get_istat (char *iname, struct stat *sbuf);
static int make_ofname (void);
static int same_file (struct stat *stat1, struct stat *stat2);
static int name_too_long (char *name, struct stat *statb);
static void shorten_name (char *name);
static int get_method (int in);
static void do_list (int ifd, int method);
static int check_ofname (void);
static void copy_stat (struct stat *ifstat);
static void do_exit (int exitcode);
      int main (int argc, char **argv);
int (*work) (int infile, int outfile) = zip;
static void treat_dir (char *dir);
static void reset_times (char *name, struct stat *statb);
static void usage()
{
    fprintf(stderr, "usage: %s [-%scdfhlLnN%stvV19] [-S suffix] [file ...]\n",
     progname,
     "",
     "r"
     );
}
static void help()
{
    static char *help_msg[] = {
 " -c --stdout      write on standard output, keep original files unchanged",
 " -d --decompress  decompress",
 " -f --force       force overwrite of output file and compress links",
 " -h --help        give this help",
 " -l --list        list compressed file contents",
 " -L --license     display software license",
 " -n --no-name     do not save or restore the original name and time stamp",
 " -N --name        save or restore the original name and time stamp",
 " -q --quiet       suppress all warnings",
 " -r --recursive   operate recursively on directories",
 " -S .suf  --suffix .suf     use suffix .suf on compressed files",
 " -t --test        test compressed file integrity",
 " -v --verbose     verbose mode",
 " -V --version     display version number",
 " -1 --fast        compress faster",
 " -9 --best        compress better",
 " file...          files to (de)compress. If none given, use standard input.",
  0};
    char **p = help_msg;
    fprintf(stderr,"%s %s (%s)\n", progname, "1.2.4", "18 Aug 93");
    usage();
    while (*p) fprintf(stderr, "%s\n", *p++);
}
static void license()
{
    char **p = license_msg;
    fprintf(stderr,"%s %s (%s)\n", progname, "1.2.4", "18 Aug 93");
    while (*p) fprintf(stderr, "%s\n", *p++);
}
static void version()
{
    fprintf(stderr,"%s %s (%s)\n", progname, "1.2.4", "18 Aug 93");
    fprintf(stderr, "Compilation options:\n%s %s ", "DIRENT", "UTIME");
    fprintf(stderr, "STDC_HEADERS ");
    fprintf(stderr, "HAVE_UNISTD_H ");
    fprintf(stderr, "\n");
}
int main (argc, argv)
    int argc;
    char **argv;
{
    int file_count;
    int proglen;
    int optc;
    ;
    progname = basename(argv[0]);
    proglen = strlen(progname);
    if (proglen > 4 && (strcmp((progname+proglen-4),(".exe")) == 0)) {
        progname[proglen-4] = '\0';
    }
    env = add_envopt(&argc, &argv, "GZIP");
    if (env != ((void *)0)) args = argv;
    foreground = signal(2, ((__sighandler_t) 1)) != ((__sighandler_t) 1);
    if (foreground) {
 (void) signal (2, (sig_type)abort_gzip);
    }
    if (signal(15, ((__sighandler_t) 1)) != ((__sighandler_t) 1)) {
 (void) signal(15, (sig_type)abort_gzip);
    }
    if (signal(1, ((__sighandler_t) 1)) != ((__sighandler_t) 1)) {
 (void) signal(1, (sig_type)abort_gzip);
    }
    if ( strncmp(progname, "un", 2) == 0
       || strncmp(progname, "gun", 3) == 0) {
 decompress = 1;
    } else if ((strcmp((progname+1),("cat")) == 0)
     || (strcmp((progname),("gzcat")) == 0)) {
 decompress = to_stdout = 1;
    }
    strncpy(z_suffix, ".gz", sizeof(z_suffix)-1);
    z_len = strlen(z_suffix);
    while ((optc = getopt_long (argc, argv, "ab:cdfhH?lLmMnNqrS:tvVZ123456789",
    longopts, (int *)0)) != (-1)) {
 switch (optc) {
        case 'a':
            ascii = 1; break;
 case 'b':
     maxbits = atoi(optarg);
     break;
 case 'c':
     to_stdout = 1; break;
 case 'd':
     decompress = 1; break;
 case 'f':
     force++; break;
 case 'h': case 'H': case '?':
     help(); do_exit(0); break;
 case 'l':
     list = decompress = to_stdout = 1; break;
 case 'L':
     license(); do_exit(0); break;
 case 'm':
     no_time = 1; break;
 case 'M':
     no_time = 0; break;
 case 'n':
     no_name = no_time = 1; break;
 case 'N':
     no_name = no_time = 0; break;
 case 'q':
     quiet = 1; verbose = 0; break;
 case 'r':
     recursive = 1; break;
 case 'S':
            z_len = strlen(optarg);
            strcpy(z_suffix, optarg);
            break;
 case 't':
     test = decompress = to_stdout = 1;
     break;
 case 'v':
     verbose++; quiet = 0; break;
 case 'V':
     version(); do_exit(0); break;
 case 'Z':
     fprintf(stderr, "%s: -Z not supported in this version\n",
      progname);
     usage();
     do_exit(1); break;
 case '1': case '2': case '3': case '4':
 case '5': case '6': case '7': case '8': case '9':
     level = optc - '0';
     break;
 default:
     usage();
     do_exit(1);
 }
    }
    if (no_time < 0) no_time = decompress;
    if (no_name < 0) no_name = decompress;
    file_count = argc - optind;
    if (ascii && !quiet) {
 fprintf(stderr, "%s: option --ascii ignored on this system\n",
  progname);
    }
    if ((z_len == 0 && !decompress) || z_len > 30) {
        fprintf(stderr, "%s: incorrect suffix '%s'\n",
                progname, optarg);
        do_exit(1);
    }
    if (do_lzw && !decompress) work = lzw;
    ;
    ;
    ;
    ;
    ;
    if (file_count != 0) {
 if (to_stdout && !test && !list && (!decompress || !ascii)) {
     ;
 }
        while (optind < argc) {
     treat_file(argv[optind++]);
 }
    } else {
 treat_stdin();
    }
    if (list && !quiet && file_count > 1) {
 do_list(-1, -1);
    }
    do_exit(exit_code);
    return exit_code;
}
static void treat_stdin()
{
    if (!force && !list &&
 isatty(fileno((FILE *)(decompress ? stdin : stdout))))
    {
 fprintf(stderr,
    "%s: compressed data not %s a terminal. Use -f to force %scompression.\n",
  progname, decompress ? "read from" : "written to",
  decompress ? "de" : "");
 fprintf(stderr,"For help, type: %s -h\n", progname);
 do_exit(1);
    }
    if (decompress || !ascii) {
 ;
    }
    if (!test && !list && (!decompress || !ascii)) {
 ;
    }
    strcpy(ifname, "stdin");
    strcpy(ofname, "stdout");
    time_stamp = 0;
    if (list || !no_time) {
 if (fstat(fileno(stdin), &istat) != 0) {
     error("fstat(stdin)");
 }
     time_stamp = 0;
    }
    ifile_size = -1L;
    clear_bufs();
    to_stdout = 1;
    part_nb = 0;
    if (decompress) {
 method = get_method(ifd);
 if (method < 0) {
     do_exit(exit_code);
 }
    }
    if (list) {
        do_list(ifd, method);
        return;
    }
    for (;;) {
 if ((*work)(fileno(stdin), fileno(stdout)) != 0) return;
 if (!decompress || last_member || inptr == insize) break;
 method = get_method(ifd);
 if (method < 0) return;
 bytes_out = 0;
    }
    if (verbose) {
 if (test) {
     fprintf(stderr, " OK\n");
 } else if (!decompress) {
     display_ratio(bytes_in-(bytes_out-header_bytes), bytes_in, stderr);
     fprintf(stderr, "\n");
 }
    }
}
static void treat_file(iname)
    char *iname;
{
    if ((strcmp((iname),("-")) == 0)) {
 int cflag = to_stdout;
 treat_stdin();
 to_stdout = cflag;
 return;
    }
    if (get_istat(iname, &istat) != 0) return;
    if (((((istat.st_mode)) & 0170000) == (0040000))) {
 if (recursive) {
     struct stat st;
     st = istat;
     treat_dir(iname);
     reset_times (iname, &st);
 } else
 {if (!quiet) fprintf (stderr,"%s: %s is a directory -- ignored\n", progname, ifname) ; if (exit_code == 0) exit_code = 2;};
 return;
    }
    if (!((((istat.st_mode)) & 0170000) == (0100000))) {
 {if (!quiet) fprintf (stderr, "%s: %s is not a directory or a regular file - ignored\n", progname, ifname) ; if (exit_code == 0) exit_code = 2;};
 return;
    }
    if (istat.st_nlink > 1 && !to_stdout && !force) {
 {if (!quiet) fprintf (stderr, "%s: %s has %d other link%c -- unchanged\n", progname, ifname, (int)istat.st_nlink - 1, istat.st_nlink > 2 ? 's' : ' ') ; if (exit_code == 0) exit_code = 2;};
 return;
    }
    ifile_size = istat.st_size;
    time_stamp = 0;
    if (to_stdout && !list && !test) {
 strcpy(ofname, "stdout");
    } else if (make_ofname() != 0) {
 return;
    }
    ifd = open(ifname, ascii && !decompress ? 00 : 00 | 0, (0400 | 0200));
    if (ifd == -1) {
 fprintf(stderr, "%s: ", progname);
 perror(ifname);
 exit_code = 1;
 return;
    }
    clear_bufs();
    part_nb = 0;
    if (decompress) {
 method = get_method(ifd);
 if (method < 0) {
     close(ifd);
     return;
 }
    }
    if (list) {
        do_list(ifd, method);
        close(ifd);
        return;
    }
    if (to_stdout) {
 ofd = fileno(stdout);
    } else {
 if (create_outfile() != 0) return;
 if (!decompress && save_orig_name && !verbose && !quiet) {
     fprintf(stderr, "%s: %s compressed to %s\n",
      progname, ifname, ofname);
 }
    }
    if (!save_orig_name) save_orig_name = !no_name;
    if (verbose) {
 fprintf(stderr, "%s:\t%s", ifname, (int)strlen(ifname) >= 15 ?
  "" : ((int)strlen(ifname) >= 7 ? "\t" : "\t\t"));
    }
    for (;;) {
 if ((*work)(ifd, ofd) != 0) {
     method = -1;
     break;
 }
 if (!decompress || last_member || inptr == insize) break;
 method = get_method(ifd);
 if (method < 0) break;
 bytes_out = 0;
    }
    close(ifd);
    if (!to_stdout && close(ofd)) {
 write_error();
    }
    if (method == -1) {
 if (!to_stdout) unlink (ofname);
 return;
    }
    if(verbose) {
 if (test) {
     fprintf(stderr, " OK");
 } else if (decompress) {
     display_ratio(bytes_out-(bytes_in-header_bytes), bytes_out,stderr);
 } else {
     display_ratio(bytes_in-(bytes_out-header_bytes), bytes_in, stderr);
 }
 if (!test && !to_stdout) {
     fprintf(stderr, " -- replaced with %s", ofname);
 }
 fprintf(stderr, "\n");
    }
    if (!to_stdout) {
 copy_stat(&istat);
    }
}
static int create_outfile()
{
    struct stat ostat;
    int flags = 01 | 0100 | 0200 | 0;
    if (ascii && decompress) {
 flags &= ~0;
    }
    for (;;) {
 if (check_ofname() != 0) {
     close(ifd);
     return 1;
 }
 remove_ofname = 1;
 ofd = open(ofname, flags, (0400 | 0200));
 if (ofd == -1) {
     perror(ofname);
     close(ifd);
     exit_code = 1;
     return 1;
 }
 if (fstat(ofd, &ostat) != 0) {
     fprintf(stderr, "%s: ", progname);
     perror(ofname);
     close(ifd); close(ofd);
     unlink(ofname);
     exit_code = 1;
     return 1;
 }
 if (!name_too_long(ofname, &ostat)) return 0;
 if (decompress) {
     {if (!quiet) fprintf (stderr, "%s: %s: warning, name truncated\n", progname, ofname) ; if (exit_code == 0) exit_code = 2;};
     return 0;
 }
 close(ofd);
 unlink(ofname);
 shorten_name(ofname);
    }
}
static int do_stat(name, sbuf)
    char *name;
    struct stat *sbuf;
{
    (*__errno_location ()) = 0;
    if (!to_stdout && !force) {
 return lstat(name, sbuf);
    }
    return stat(name, sbuf);
}
static char *get_suffix(name)
    char *name;
{
    int nlen, slen;
    char suffix[30 +3];
    static char *known_suffixes[] =
       {z_suffix, ".gz", ".z", ".taz", ".tgz", "-gz", "-z", "_z",
          ((void *)0)};
    char **suf = known_suffixes;
    if ((strcmp((z_suffix),("z")) == 0)) suf++;
    nlen = strlen(name);
    if (nlen <= 30 +2) {
        strcpy(suffix, name);
    } else {
        strcpy(suffix, name+nlen-30 -2);
    }
    strlwr(suffix);
    slen = strlen(suffix);
    do {
       int s = strlen(*suf);
       if (slen > s && suffix[slen-s-1] != '/'
           && (strcmp((suffix + slen - s),(*suf)) == 0)) {
           return name+nlen-s;
       }
    } while (*++suf != ((void *)0));
    return ((void *)0);
}
static int get_istat(iname, sbuf)
    char *iname;
    struct stat *sbuf;
{
    int ilen;
    static char *suffixes[] = {z_suffix, ".gz", ".z", "-z", ".Z", ((void *)0)};
    char **suf = suffixes;
    char *s;
    strcpy(ifname, iname);
    if (do_stat(ifname, sbuf) == 0) return 0;
    if (!decompress || (*__errno_location ()) != 2) {
 perror(ifname);
 exit_code = 1;
 return 1;
    }
    s = get_suffix(ifname);
    if (s != ((void *)0)) {
 perror(ifname);
 exit_code = 1;
 return 1;
    }
    ilen = strlen(ifname);
    if ((strcmp((z_suffix),(".gz")) == 0)) suf++;
    do {
        s = *suf;
        strcat(ifname, s);
        if (do_stat(ifname, sbuf) == 0) return 0;
 ifname[ilen] = '\0';
    } while (*++suf != ((void *)0));
    strcat(ifname, z_suffix);
    perror(ifname);
    exit_code = 1;
    return 1;
}
static int make_ofname()
{
    char *suff;
    strcpy(ofname, ifname);
    suff = get_suffix(ofname);
    if (decompress) {
 if (suff == ((void *)0)) {
            if (!recursive && (list || test)) return 0;
     if (verbose || (!recursive && !quiet)) {
  {if (!quiet) fprintf (stderr,"%s: %s: unknown suffix -- ignored\n", progname, ifname) ; if (exit_code == 0) exit_code = 2;};
     }
     return 2;
 }
 strlwr(suff);
 if ((strcmp((suff),(".tgz")) == 0) || (strcmp((suff),(".taz")) == 0)) {
     strcpy(suff, ".tar");
 } else {
     *suff = '\0';
 }
    } else if (suff != ((void *)0)) {
 if (verbose || (!recursive && !quiet)) {
     fprintf(stderr, "%s: %s already has %s suffix -- unchanged\n",
      progname, ifname, suff);
 }
 if (exit_code == 0) exit_code = 2;
 return 2;
    } else {
        save_orig_name = 0;
 strcat(ofname, z_suffix);
    }
    return 0;
}
static int get_method(in)
    int in;
{
    uch flags;
    char magic[2];
    ulg stamp;
    if (force && to_stdout) {
 magic[0] = (char)(inptr < insize ? inbuf[inptr++] : fill_inbuf(1));
 magic[1] = (char)(inptr < insize ? inbuf[inptr++] : fill_inbuf(1));
    } else {
 magic[0] = (char)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
 magic[1] = (char)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
    }
    method = -1;
    part_nb++;
    header_bytes = 0;
    last_member = 0;
    if (memcmp(magic, "\037\213", 2) == 0
        || memcmp(magic, "\037\236", 2) == 0) {
 method = (int)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
 if (method != 8) {
     fprintf(stderr,
      "%s: %s: unknown method %d -- get newer version of gzip\n",
      progname, ifname, method);
     exit_code = 1;
     return -1;
 }
 work = unzip;
 flags = (uch)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
 if ((flags & 0x20) != 0) {
     fprintf(stderr,
      "%s: %s is encrypted -- get newer version of gzip\n",
      progname, ifname);
     exit_code = 1;
     return -1;
 }
 if ((flags & 0x02) != 0) {
     fprintf(stderr,
    "%s: %s is a a multi-part gzip file -- get newer version of gzip\n",
      progname, ifname);
     exit_code = 1;
     if (force <= 1) return -1;
 }
 if ((flags & 0xC0) != 0) {
     fprintf(stderr,
      "%s: %s has flags 0x%x -- get newer version of gzip\n",
      progname, ifname, flags);
     exit_code = 1;
     if (force <= 1) return -1;
 }
 stamp = (ulg)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
 stamp |= ((ulg)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0))) << 8;
 stamp |= ((ulg)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0))) << 16;
 stamp |= ((ulg)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0))) << 24;
 if (stamp != 0 && !no_time) time_stamp = stamp;
 time_stamp = 0;
 (void)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
 (void)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
 if ((flags & 0x02) != 0) {
     unsigned part = (unsigned)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
     part |= ((unsigned)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<8;
     if (verbose) {
  fprintf(stderr,"%s: %s: part number %u\n",
   progname, ifname, part);
     }
 }
 if ((flags & 0x04) != 0) {
     unsigned len = (unsigned)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
     len |= ((unsigned)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0)))<<8;
     if (verbose) {
  fprintf(stderr,"%s: %s: extra field of %u bytes ignored\n",
   progname, ifname, len);
     }
     while (len--) (void)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
 }
 if ((flags & 0x08) != 0) {
     if (no_name || (to_stdout && !list) || part_nb > 1) {
  char c;
  do {c=(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));} while (c != 0);
     } else {
                char *p = basename(ofname);
                char *base = p;
  for (;;) {
      *p = (char)(inptr < insize ? inbuf[inptr++] : fill_inbuf(0));
      if (*p++ == '\0') break;
      if (p >= ofname+sizeof(ofname)) {
   error("corrupted input -- file name too large");
      }
  }
                if (!list) {
                   ;
     if (base) list=0;
                }
     }
 }
 if ((flags & 0x10) != 0) {
     while ((inptr < insize ? inbuf[inptr++] : fill_inbuf(0)) != 0) ;
 }
 if (part_nb == 1) {
     header_bytes = inptr + 2*sizeof(long);
 }
    } else if (memcmp(magic, "\120\113\003\004", 2) == 0 && inptr == 2
     && memcmp((char*)inbuf, "\120\113\003\004", 4) == 0) {
        inptr = 0;
 work = unzip;
 if (check_zipfile(in) != 0) return -1;
 last_member = 1;
    } else if (memcmp(magic, "\037\036", 2) == 0) {
 work = unpack;
 method = 2;
    } else if (memcmp(magic, "\037\235", 2) == 0) {
 work = unlzw;
 method = 1;
 last_member = 1;
    } else if (memcmp(magic, "\037\240", 2) == 0) {
 work = unlzh;
 method = 3;
 last_member = 1;
    } else if (force && to_stdout && !list) {
 method = 0;
 work = copy;
        inptr = 0;
 last_member = 1;
    }
    if (method >= 0) return method;
    if (part_nb == 1) {
 fprintf(stderr, "\n%s: %s: not in gzip format\n", progname, ifname);
 exit_code = 1;
 return -1;
    } else {
 {if (!quiet) fprintf (stderr, "\n%s: %s: decompression OK, trailing garbage ignored\n", progname, ifname) ; if (exit_code == 0) exit_code = 2;};
 return -2;
    }
}
static void do_list(ifd, method)
    int ifd;
    int method;
{
    ulg crc;
    static int first_time = 1;
    static char* methods[9] = {
        "store",
        "compr",
        "pack ",
        "lzh  ",
        "", "", "", "",
        "defla"};
    char *date;
    if (first_time && method >= 0) {
 first_time = 0;
 if (verbose) {
     printf("method  crc     date  time  ");
 }
 if (!quiet) {
     printf("compressed  uncompr. ratio uncompressed_name\n");
 }
    } else if (method < 0) {
 if (total_in <= 0 || total_out <= 0) return;
 if (verbose) {
     printf("                            %9lu %9lu ",
     total_in, total_out);
 } else if (!quiet) {
     printf("%9ld %9ld ", total_in, total_out);
 }
 display_ratio(total_out-(total_in-header_bytes), total_out, stdout);
 printf(" (totals)\n");
 return;
    }
    crc = (ulg)~0;
    bytes_out = -1L;
    bytes_in = ifile_size;
    if (method == 8 && !last_member) {
        bytes_in = (long)lseek(ifd, (off_t)(-8), 2);
        if (bytes_in != -1L) {
            uch buf[8];
            bytes_in += 8L;
            if (read(ifd, (char*)buf, sizeof(buf)) != sizeof(buf)) {
                read_error();
            }
            crc = ((ulg)(((ush)(uch)((buf)[0]) | ((ush)(uch)((buf)[1]) << 8))) | ((ulg)(((ush)(uch)(((buf)+2)[0]) | ((ush)(uch)(((buf)+2)[1]) << 8))) << 16));
     bytes_out = ((ulg)(((ush)(uch)((buf+4)[0]) | ((ush)(uch)((buf+4)[1]) << 8))) | ((ulg)(((ush)(uch)(((buf+4)+2)[0]) | ((ush)(uch)(((buf+4)+2)[1]) << 8))) << 16));
 }
    }
    date = ctime((time_t*)&time_stamp) + 4;
    date[12] = '\0';
    if (verbose) {
        printf("%5s %08lx %11s ", methods[method], crc, date);
    }
    printf("%9ld %9ld ", bytes_in, bytes_out);
    if (bytes_in == -1L) {
 total_in = -1L;
 bytes_in = bytes_out = header_bytes = 0;
    } else if (total_in >= 0) {
 total_in += bytes_in;
    }
    if (bytes_out == -1L) {
 total_out = -1L;
 bytes_in = bytes_out = header_bytes = 0;
    } else if (total_out >= 0) {
 total_out += bytes_out;
    }
    display_ratio(bytes_out-(bytes_in-header_bytes), bytes_out, stdout);
    printf(" %s\n", ofname);
}
static int same_file(stat1, stat2)
    struct stat *stat1;
    struct stat *stat2;
{
    return stat1->st_ino == stat2->st_ino
 && stat1->st_dev == stat2->st_dev
     ;
}
static int name_too_long(name, statb)
    char *name;
    struct stat *statb;
{
    int s = strlen(name);
    char c = name[s-1];
    struct stat tstat;
    int res;
    tstat = *statb;
    name[s-1] = '\0';
    res = stat(name, &tstat) == 0 && same_file(statb, &tstat);
    name[s-1] = c;
    ;
    return res;
}
static void shorten_name(name)
    char *name;
{
    int len;
    char *trunc = ((void *)0);
    int plen;
    int min_part = 3;
    char *p;
    len = strlen(name);
    if (decompress) {
 if (len <= 1) error("name too short");
 name[len-1] = '\0';
 return;
    }
    p = get_suffix(name);
    if (p == ((void *)0)) error("can't recover suffix\n");
    *p = '\0';
    save_orig_name = 1;
    if (len > 4 && (strcmp((p-4),(".tar")) == 0)) {
 strcpy(p-4, ".tgz");
 return;
    }
    do {
 p = strrchr(name, '/');
 p = p ? p+1 : name;
 while (*p) {
     plen = strcspn(p, ".");
     p += plen;
     if (plen > min_part) trunc = p-1;
     if (*p) p++;
 }
    } while (trunc == ((void *)0) && --min_part != 0);
    if (trunc != ((void *)0)) {
 do {
     trunc[0] = trunc[1];
 } while (*trunc++);
 trunc--;
    } else {
 trunc = strrchr(name, "."[0]);
 if (trunc == ((void *)0)) error("internal error in shorten_name");
 if (trunc[1] == '\0') trunc--;
    }
    strcpy(trunc, z_suffix);
}
static int check_ofname()
{
    struct stat ostat;
    (*__errno_location ()) = 0;
    while (stat(ofname, &ostat) != 0) {
        if ((*__errno_location ()) != 36) return 0;
 shorten_name(ofname);
    }
    if (!decompress && name_too_long(ofname, &ostat)) {
 shorten_name(ofname);
 if (stat(ofname, &ostat) != 0) return 0;
    }
    if (same_file(&istat, &ostat)) {
 if ((strcmp((ifname),(ofname)) == 0)) {
     fprintf(stderr, "%s: %s: cannot %scompress onto itself\n",
      progname, ifname, decompress ? "de" : "");
 } else {
     fprintf(stderr, "%s: %s and %s are the same file\n",
      progname, ifname, ofname);
 }
 exit_code = 1;
 return 1;
    }
    if (!force) {
 char response[80];
 strcpy(response,"n");
 fprintf(stderr, "%s: %s already exists;", progname, ofname);
 if (foreground && isatty(fileno(stdin))) {
     fprintf(stderr, " do you wish to overwrite (y or n)? ");
     fflush(stderr);
     (void)fgets(response, sizeof(response)-1, stdin);
 }
 if ((((*__ctype_b_loc ())[(int) ((*response))] & (unsigned short int) _ISupper) ? (*response)-'A'+'a' : (*response)) != 'y') {
     fprintf(stderr, "\tnot overwritten\n");
     if (exit_code == 0) exit_code = 2;
     return 1;
 }
    }
    (void) chmod(ofname, 0777);
    if (unlink(ofname)) {
 fprintf(stderr, "%s: ", progname);
 perror(ofname);
 exit_code = 1;
 return 1;
    }
    return 0;
}
static void reset_times (name, statb)
    char *name;
    struct stat *statb;
{
    struct utimbuf timep;
    timep.actime = statb->st_atim.tv_sec;
    timep.modtime = statb->st_mtim.tv_sec;
    if (utime(name, &timep) && !((((statb->st_mode)) & 0170000) == (0040000))) {
 {if (!quiet) fprintf (stderr, "%s: ", progname) ; if (exit_code == 0) exit_code = 2;};
 if (!quiet) perror(ofname);
    }
}
static void copy_stat(ifstat)
    struct stat *ifstat;
{
    if (decompress && time_stamp != 0 && ifstat->st_mtim.tv_sec != time_stamp) {
 ifstat->st_mtim.tv_sec = time_stamp;
 if (verbose > 1) {
     fprintf(stderr, "%s: time stamp restored\n", ofname);
 }
    }
    reset_times(ofname, ifstat);
    if (chmod(ofname, ifstat->st_mode & 07777)) {
 {if (!quiet) fprintf (stderr, "%s: ", progname) ; if (exit_code == 0) exit_code = 2;};
 if (!quiet) perror(ofname);
    }
    chown(ofname, ifstat->st_uid, ifstat->st_gid);
    remove_ofname = 0;
    (void) chmod(ifname, 0777);
    if (unlink(ifname)) {
 {if (!quiet) fprintf (stderr, "%s: ", progname) ; if (exit_code == 0) exit_code = 2;};
 if (!quiet) perror(ifname);
    }
}
static void treat_dir(dir)
    char *dir;
{
    dir_type *dp;
    DIR *dirp;
    char nbuf[1024];
    int len;
    dirp = opendir(dir);
    if (dirp == ((void *)0)) {
 fprintf(stderr, "%s: %s unreadable\n", progname, dir);
 exit_code = 1;
 return ;
    }
    while ((dp = readdir(dirp)) != ((void *)0)) {
 if ((strcmp((dp->d_name),(".")) == 0) || (strcmp((dp->d_name),("..")) == 0)) {
     continue;
 }
 len = strlen(dir);
 if (len + ((int)strlen((dp)->d_name)) + 1 < 1024 - 1) {
     strcpy(nbuf,dir);
     if (len != 0
     ) {
  nbuf[len++] = '/';
     }
     strcpy(nbuf+len, dp->d_name);
     treat_file(nbuf);
 } else {
     fprintf(stderr,"%s: %s/%s: pathname too long\n",
      progname, dir, dp->d_name);
     exit_code = 1;
 }
    }
    closedir(dirp);
}
static void do_exit(exitcode)
    int exitcode;
{
    static int in_exit = 0;
    if (in_exit) exit(exitcode);
    in_exit = 1;
    if (env != ((void *)0)) free(env), env = ((void *)0);
    if (args != ((void *)0)) free((char*)args), args = ((void *)0);
    ;
    ;
    ;
    ;
    ;
    exit(exitcode);
}
void abort_gzip()
{
   if (remove_ofname) {
       close(ofd);
       unlink (ofname);
   }
   do_exit(1);
}
