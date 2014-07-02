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

extern int isctype (int __c, int __mask) __attribute__ ((__nothrow__ , __leaf__));
extern int isascii (int __c) __attribute__ ((__nothrow__ , __leaf__));
extern int toascii (int __c) __attribute__ ((__nothrow__ , __leaf__));
extern int _toupper (int) __attribute__ ((__nothrow__ , __leaf__));
extern int _tolower (int) __attribute__ ((__nothrow__ , __leaf__));
typedef struct __locale_struct
{
  struct __locale_data *__locales[13];
  const unsigned short int *__ctype_b;
  const int *__ctype_tolower;
  const int *__ctype_toupper;
  const char *__names[13];
} *__locale_t;
typedef __locale_t locale_t;
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


typedef long unsigned int size_t;
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
typedef __io_read_fn cookie_read_function_t;
typedef __io_write_fn cookie_write_function_t;
typedef __io_seek_fn cookie_seek_function_t;
typedef __io_close_fn cookie_close_function_t;
typedef struct
{
  __io_read_fn *read;
  __io_write_fn *write;
  __io_seek_fn *seek;
  __io_close_fn *close;
} _IO_cookie_io_functions_t;
typedef _IO_cookie_io_functions_t cookie_io_functions_t;
struct _IO_cookie_file;
extern void _IO_cookie_init (struct _IO_cookie_file *__cfile, int __read_write,
        void *__cookie, _IO_cookie_io_functions_t __fns);
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
typedef __off64_t off64_t;
typedef __ssize_t ssize_t;

typedef _G_fpos_t fpos_t;

typedef _G_fpos64_t fpos64_t;
extern struct _IO_FILE *stdin;
extern struct _IO_FILE *stdout;
extern struct _IO_FILE *stderr;

extern int remove (__const char *__filename) __attribute__ ((__nothrow__ , __leaf__));
extern int rename (__const char *__old, __const char *__new) __attribute__ ((__nothrow__ , __leaf__));

extern int renameat (int __oldfd, __const char *__old, int __newfd,
       __const char *__new) __attribute__ ((__nothrow__ , __leaf__));

extern FILE *tmpfile (void) ;
extern FILE *tmpfile64 (void) ;
extern char *tmpnam (char *__s) __attribute__ ((__nothrow__ , __leaf__)) ;

extern char *tmpnam_r (char *__s) __attribute__ ((__nothrow__ , __leaf__)) ;
extern char *tempnam (__const char *__dir, __const char *__pfx)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

extern int fclose (FILE *__stream);
extern int fflush (FILE *__stream);

extern int fflush_unlocked (FILE *__stream);
extern int fcloseall (void);

extern FILE *fopen (__const char *__restrict __filename,
      __const char *__restrict __modes) ;

extern FILE *freopen (__const char *__restrict __filename,
        __const char *__restrict __modes,
        FILE *__restrict __stream) ;

extern FILE *fopen64 (__const char *__restrict __filename,
        __const char *__restrict __modes) ;
extern FILE *freopen64 (__const char *__restrict __filename,
   __const char *__restrict __modes,
   FILE *__restrict __stream) ;
extern FILE *fdopen (int __fd, __const char *__modes) __attribute__ ((__nothrow__ , __leaf__)) ;
extern FILE *fopencookie (void *__restrict __magic_cookie,
     __const char *__restrict __modes,
     _IO_cookie_io_functions_t __io_funcs) __attribute__ ((__nothrow__ , __leaf__)) ;
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

extern int vasprintf (char **__restrict __ptr, __const char *__restrict __f,
        __gnuc_va_list __arg)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 2, 0))) ;
extern int __asprintf (char **__restrict __ptr,
         __const char *__restrict __fmt, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 2, 3))) ;
extern int asprintf (char **__restrict __ptr,
       __const char *__restrict __fmt, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 2, 3))) ;
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


extern int vfscanf (FILE *__restrict __s, __const char *__restrict __format,
      __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 2, 0))) ;
extern int vscanf (__const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (__const char *__restrict __s,
      __const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__format__ (__scanf__, 2, 0)));


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

extern char *fgets_unlocked (char *__restrict __s, int __n,
        FILE *__restrict __stream) ;
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

extern int fputs_unlocked (__const char *__restrict __s,
      FILE *__restrict __stream);
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

extern int fseeko64 (FILE *__stream, __off64_t __off, int __whence);
extern __off64_t ftello64 (FILE *__stream) ;
extern int fgetpos64 (FILE *__restrict __stream, fpos64_t *__restrict __pos);
extern int fsetpos64 (FILE *__stream, __const fpos64_t *__pos);

extern void clearerr (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int feof (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ferror (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;

extern void clearerr_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int feof_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ferror_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;

extern void perror (__const char *__s);

extern int sys_nerr;
extern __const char *__const sys_errlist[];
extern int _sys_nerr;
extern __const char *__const _sys_errlist[];
extern int fileno (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int fileno_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern FILE *popen (__const char *__command, __const char *__modes) ;
extern int pclose (FILE *__stream);
extern char *ctermid (char *__s) __attribute__ ((__nothrow__ , __leaf__));
extern char *cuserid (char *__s);
struct obstack;
extern int obstack_printf (struct obstack *__restrict __obstack,
      __const char *__restrict __format, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 2, 3)));
extern int obstack_vprintf (struct obstack *__restrict __obstack,
       __const char *__restrict __format,
       __gnuc_va_list __args)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 2, 0)));
extern void flockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int ftrylockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern void funlockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));


typedef __u_char u_char;
typedef __u_short u_short;
typedef __u_int u_int;
typedef __u_long u_long;
typedef __quad_t quad_t;
typedef __u_quad_t u_quad_t;
typedef __fsid_t fsid_t;
typedef __loff_t loff_t;
typedef __ino_t ino_t;
typedef __ino64_t ino64_t;
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
typedef __useconds_t useconds_t;
typedef __suseconds_t suseconds_t;
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
typedef long int __fd_mask;
typedef struct
  {
    __fd_mask fds_bits[1024 / (8 * (int) sizeof (__fd_mask))];
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
typedef __blkcnt64_t blkcnt64_t;
typedef __fsblkcnt64_t fsblkcnt64_t;
typedef __fsfilcnt64_t fsfilcnt64_t;
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

typedef unsigned int RX_subset;
typedef RX_subset * rx_Bitset;
typedef void (*rx_bitset_iterator) (void *, int member_index);
typedef int (*rx_sp_comparer) (void * a, void * b);
struct rx_sp_node
{
  void * key;
  void * data;
  struct rx_sp_node * kids[2];
};
typedef void (*rx_sp_key_data_freer) (struct rx_sp_node *);
struct rx_hash_item
{
  struct rx_hash_item * next_same_hash;
  struct rx_hash * table;
  unsigned long hash;
  void * data;
  void * binding;
};
struct rx_hash
{
  struct rx_hash * parent;
  int refs;
  struct rx_hash * children[13];
  struct rx_hash_item * buckets [13];
  int bucket_size [13];
};
struct rx_hash_rules;
typedef int (*rx_hash_eq)(void *, void *);
typedef struct rx_hash * (*rx_alloc_hash)(struct rx_hash_rules *);
typedef void (*rx_free_hash)(struct rx_hash *,
       struct rx_hash_rules *);
typedef struct rx_hash_item * (*rx_alloc_hash_item)(struct rx_hash_rules *,
          void *);
typedef void (*rx_free_hash_item)(struct rx_hash_item *,
     struct rx_hash_rules *);
struct rx_hash_rules
{
  rx_hash_eq eq;
  rx_alloc_hash hash_alloc;
  rx_free_hash free_hash;
  rx_alloc_hash_item hash_item_alloc;
  rx_free_hash_item free_hash_item;
};
struct rx_inx
{
  void * inx;
  void * data;
  void * data_2;
  void * fnord;
};
struct rx_cache;
struct rx_se_list;
struct rx;
typedef int (*rx_se_list_order) (struct rx *,
     struct rx_se_list *, struct rx_se_list *);
struct rx_superset;
struct rx
{
  int rx_id;
  struct rx_cache * cache;
  int local_cset_size;
  void * buffer;
  unsigned long allocated;
  unsigned long reserved;
  int nodec;
  int epsnodec;
  struct rx_hash se_list_memo;
  struct rx_hash set_list_memo;
  void ** instruction_table;
  struct rx_nfa_state *nfa_states;
  struct rx_nfa_state *start;
  rx_se_list_order se_list_cmp;
  struct rx_superset * start_set;
};
typedef void * rx_side_effect;
struct rx_se_list
{
  rx_side_effect car;
  struct rx_se_list * cdr;
};
enum rexp_node_type
{
  r_cset,
  r_concat,
  r_alternate,
  r_opt,
  r_star,
  r_2phase_star,
  r_side_effect,
  r_data
};
struct rexp_node
{
  enum rexp_node_type type;
  union
  {
    rx_Bitset cset;
    rx_side_effect side_effect;
    struct
      {
 struct rexp_node *left;
 struct rexp_node *right;
      } pair;
    void * data;
  } params;
};
struct rx_nfa_state
{
  int id;
  struct rx_nfa_edge *edges;
  struct rx_possible_future *futures;
  unsigned int is_final:1;
  unsigned int is_start:1;
  unsigned int eclosure_needed:1;
  struct rx_nfa_state *next;
  unsigned int mark:1;
};
enum rx_nfa_etype
{
  ne_cset,
  ne_epsilon,
  ne_side_effect
};
struct rx_nfa_edge
{
  struct rx_nfa_edge *next;
  enum rx_nfa_etype type;
  struct rx_nfa_state *dest;
  union
  {
    rx_Bitset cset;
    rx_side_effect side_effect;
  } params;
};
struct rx_nfa_state_set
{
  struct rx_nfa_state * car;
  struct rx_nfa_state_set * cdr;
};
struct rx_possible_future
{
  struct rx_possible_future *next;
  struct rx_se_list * effects;
  struct rx_nfa_state_set * destset;
};
enum rx_opcode
{
  rx_backtrack_point = 0,
  rx_do_side_effects = rx_backtrack_point + 1,
  rx_cache_miss = rx_do_side_effects + 1,
  rx_next_char = rx_cache_miss + 1,
  rx_backtrack = rx_next_char + 1,
  rx_error_inx = rx_backtrack + 1,
  rx_num_instructions = rx_error_inx + 1
};
extern void * rx_id_instruction_table[rx_num_instructions];
struct rx_superset
{
  int refs;
  struct rx_nfa_state * car;
  int id;
  struct rx_superset * cdr;
  struct rx_superstate * superstate;
  struct rx * starts_for;
  struct rx_hash_item hash_item;
};
struct rx_super_edge
{
  struct rx_super_edge *next;
  struct rx_inx rx_backtrack_frame;
  int cset_size;
  rx_Bitset cset;
  struct rx_distinct_future *options;
};
struct rx_superstate
{
  int rx_id;
  int locks;
  struct rx_superstate * next_recyclable;
  struct rx_superstate * prev_recyclable;
  struct rx_distinct_future * transition_refs;
  struct rx_superset * contents;
  struct rx_super_edge * edges;
  int is_semifree;
  int trans_size;
  struct rx_inx transitions[1];
};
struct rx_distinct_future
{
  struct rx_distinct_future * next_same_super_edge[2];
  struct rx_distinct_future * next_same_dest;
  struct rx_distinct_future * prev_same_dest;
  struct rx_superstate * present;
  struct rx_superstate * future;
  struct rx_super_edge * edge;
  struct rx_inx future_frame;
  struct rx_inx side_effects_frame;
  struct rx_se_list * effects;
};
struct rx_blocklist
{
  struct rx_blocklist * next;
  int bytes;
};
struct rx_freelist
{
  struct rx_freelist * next;
};
struct rx_cache;
typedef void (*rx_morecore_fn)(struct rx_cache *);
struct rx_cache
{
  struct rx_hash_rules superset_hash_rules;
  struct rx_blocklist * memory;
  struct rx_blocklist * memory_pos;
  int bytes_left;
  char * memory_addr;
  rx_morecore_fn morecore;
  struct rx_freelist * free_superstates;
  struct rx_freelist * free_transition_classes;
  struct rx_freelist * free_discernable_futures;
  struct rx_freelist * free_supersets;
  struct rx_freelist * free_hash;
  struct rx_superstate * lru_superstate;
  struct rx_superstate * semifree_superstate;
  struct rx_superset * empty_superset;
  int superstates;
  int semifree_superstates;
  int hits;
  int misses;
  int superstates_allowed;
  int local_cset_size;
  void ** instruction_table;
  struct rx_hash superset_table;
};
extern const char *re_error_msg[];
typedef enum
{
  REG_NOERROR = 0,
  REG_NOMATCH,
  REG_BADPAT,
  REG_ECOLLATE,
  REG_ECTYPE,
  REG_EESCAPE,
  REG_ESUBREG,
  REG_EBRACK,
  REG_EPAREN,
  REG_EBRACE,
  REG_BADBR,
  REG_ERANGE,
  REG_ESPACE,
  REG_BADRPT,
  REG_EEND,
  REG_ESIZE,
  REG_ERPAREN
} reg_errcode_t;
enum re_side_effects
{
  re_se_try = -1,
  re_se_pushback = re_se_try - 1,
  re_se_push0 = re_se_pushback -1,
  re_se_pushpos = re_se_push0 - 1,
  re_se_chkpos = re_se_pushpos -1,
  re_se_poppos = re_se_chkpos - 1,
  re_se_at_dot = re_se_poppos - 1,
  re_se_syntax = re_se_at_dot - 1,
  re_se_not_syntax = re_se_syntax - 1,
  re_se_begbuf = re_se_not_syntax - 1,
  re_se_hat = re_se_begbuf - 1,
  re_se_wordbeg = re_se_hat - 1,
  re_se_wordbound = re_se_wordbeg - 1,
  re_se_notwordbound = re_se_wordbound - 1,
  re_se_wordend = re_se_notwordbound - 1,
  re_se_endbuf = re_se_wordend - 1,
  re_se_dollar = re_se_endbuf - 1,
  re_se_fail = re_se_dollar - 1,
  re_se_win = 0,
  re_se_lparen = re_se_win + 1,
  re_se_rparen = re_se_lparen + 1,
  re_se_backref = re_se_rparen + 1,
  re_se_iter = re_se_backref + 1,
  re_se_end_iter = re_se_iter + 1,
  re_se_tv = re_se_end_iter + 1,
   re_floogle_flap = 65533
};
struct re_se_params
{
  enum re_side_effects se;
  int op1;
  int op2;
};
typedef unsigned reg_syntax_t;
struct re_pattern_buffer
{
  struct rx rx;
  reg_syntax_t syntax;
  unsigned int no_sub:1;
  unsigned int not_bol:1;
  unsigned int not_eol:1;
  unsigned int newline_anchor:1;
  unsigned int least_subs:1;
  unsigned int match_regs_on_stack:1;
  unsigned int search_regs_on_stack:1;
  unsigned int is_anchored:1;
  unsigned int begbuf_only:1;
  unsigned int regs_allocated:2;
  char * translate;
  char * syntax_parens;
  size_t re_nsub;
  void * buffer;
  unsigned long allocated;
  char *fastmap;
  unsigned int fastmap_accurate:1;
  unsigned int can_match_empty:1;
  struct rx_nfa_state * start;
  struct re_se_params *se_params;
  rx_Bitset fastset;
};
typedef int regoff_t;
struct re_registers
{
  unsigned num_regs;
  regoff_t *start;
  regoff_t *end;
};
typedef struct re_pattern_buffer regex_t;
typedef struct
{
  regoff_t rm_so;
  regoff_t rm_eo;
} regmatch_t;
extern reg_syntax_t re_syntax_options;
extern int rx_cache_bound;
extern reg_errcode_t rx_compile (const char *pattern, int size,
     reg_syntax_t syntax,
     struct re_pattern_buffer * rxb) ;
extern int re_search_2 (struct re_pattern_buffer *rxb,
      const char * string1, int size1,
      const char * string2, int size2,
      int startpos, int range,
      struct re_registers *regs,
      int stop);
extern int re_search (struct re_pattern_buffer * rxb, const char *string,
    int size, int startpos, int range,
    struct re_registers *regs);
extern int re_match_2 (struct re_pattern_buffer * rxb,
     const char * string1, int size1,
     const char * string2, int size2,
     int pos, struct re_registers *regs, int stop);
extern int re_match (struct re_pattern_buffer * rxb,
   const char * string,
   int size, int pos,
   struct re_registers *regs);
extern reg_syntax_t re_set_syntax (reg_syntax_t syntax);
extern void re_set_registers (struct re_pattern_buffer *bufp,
    struct re_registers *regs,
    unsigned num_regs,
    regoff_t * starts, regoff_t * ends);
extern const char * re_compile_pattern (const char *pattern,
      int length,
      struct re_pattern_buffer * rxb);
extern int re_compile_fastmap (struct re_pattern_buffer * rxb);
extern char * re_comp (const char *s);
extern int rx_exec (const char *s);
extern int regcomp (regex_t * preg, const char * pattern, int cflags);
extern int regexec (const regex_t *preg, const char *string,
  size_t nmatch, regmatch_t pmatch[],
  int eflags);
extern size_t regerror (int errcode, const regex_t *preg,
   char *errbuf, size_t errbuf_size);
extern void regfree (regex_t *preg);
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
extern int getopt (int argc, char *const *argv, const char *shortopts);
extern int getopt_long (int argc, char *const *argv, const char *shortopts,
          const struct option *longopts, int *longind);
extern int getopt_long_only (int argc, char *const *argv,
        const char *shortopts,
               const struct option *longopts, int *longind);
extern int _getopt_internal (int argc, char *const *argv,
        const char *shortopts,
               const struct option *longopts, int *longind,
        int long_only);
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

extern long int strtol_l (__const char *__restrict __nptr,
     char **__restrict __endptr, int __base,
     __locale_t __loc) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 4))) ;
extern unsigned long int strtoul_l (__const char *__restrict __nptr,
        char **__restrict __endptr,
        int __base, __locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 4))) ;
__extension__
extern long long int strtoll_l (__const char *__restrict __nptr,
    char **__restrict __endptr, int __base,
    __locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 4))) ;
__extension__
extern unsigned long long int strtoull_l (__const char *__restrict __nptr,
       char **__restrict __endptr,
       int __base, __locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 4))) ;
extern double strtod_l (__const char *__restrict __nptr,
   char **__restrict __endptr, __locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3))) ;
extern float strtof_l (__const char *__restrict __nptr,
         char **__restrict __endptr, __locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3))) ;
extern long double strtold_l (__const char *__restrict __nptr,
         char **__restrict __endptr,
         __locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3))) ;
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
extern int at_quick_exit (void (*__func) (void)) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern int on_exit (void (*__func) (int __status, void *__arg), void *__arg)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern void exit (int __status) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void quick_exit (int __status) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));


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
extern int mkstemp64 (char *__template) __attribute__ ((__nonnull__ (1))) ;
extern int mkstemps (char *__template, int __suffixlen) __attribute__ ((__nonnull__ (1))) ;
extern int mkstemps64 (char *__template, int __suffixlen)
     __attribute__ ((__nonnull__ (1))) ;
extern char *mkdtemp (char *__template) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int mkostemp (char *__template, int __flags) __attribute__ ((__nonnull__ (1))) ;
extern int mkostemp64 (char *__template, int __flags) __attribute__ ((__nonnull__ (1))) ;
extern int mkostemps (char *__template, int __suffixlen, int __flags)
     __attribute__ ((__nonnull__ (1))) ;
extern int mkostemps64 (char *__template, int __suffixlen, int __flags)
     __attribute__ ((__nonnull__ (1))) ;

extern int system (__const char *__command) ;

extern char *canonicalize_file_name (__const char *__name)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern char *realpath (__const char *__restrict __name,
         char *__restrict __resolved) __attribute__ ((__nothrow__ , __leaf__)) ;
typedef int (*__compar_fn_t) (__const void *, __const void *);
typedef __compar_fn_t comparison_fn_t;
typedef int (*__compar_d_fn_t) (__const void *, __const void *, void *);

extern void *bsearch (__const void *__key, __const void *__base,
        size_t __nmemb, size_t __size, __compar_fn_t __compar)
     __attribute__ ((__nonnull__ (1, 2, 5))) ;
extern void qsort (void *__base, size_t __nmemb, size_t __size,
     __compar_fn_t __compar) __attribute__ ((__nonnull__ (1, 4)));
extern void qsort_r (void *__base, size_t __nmemb, size_t __size,
       __compar_d_fn_t __compar, void *__arg)
  __attribute__ ((__nonnull__ (1, 4)));
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
extern void setkey (__const char *__key) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int posix_openpt (int __oflag) ;
extern int grantpt (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern int unlockpt (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern char *ptsname (int __fd) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ptsname_r (int __fd, char *__buf, size_t __buflen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int getpt (void);
extern int getloadavg (double __loadavg[], int __nelem)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



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

extern void *rawmemchr (__const void *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern void *memrchr (__const void *__s, int __c, size_t __n)
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

extern char *strchrnul (__const char *__s, int __c)
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
extern char *strcasestr (__const char *__haystack, __const char *__needle)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern void *memmem (__const void *__haystack, size_t __haystacklen,
       __const void *__needle, size_t __needlelen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 3)));
extern void *__mempcpy (void *__restrict __dest,
   __const void *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern void *mempcpy (void *__restrict __dest,
        __const void *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern size_t strlen (__const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));

extern size_t strnlen (__const char *__string, size_t __maxlen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));

extern char *strerror (int __errnum) __attribute__ ((__nothrow__ , __leaf__));

extern char *strerror_r (int __errnum, char *__buf, size_t __buflen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
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
extern int ffsl (long int __l) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
__extension__ extern int ffsll (long long int __ll)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int strcasecmp (__const char *__s1, __const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int strncasecmp (__const char *__s1, __const char *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int strcasecmp_l (__const char *__s1, __const char *__s2,
    __locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 3)));
extern int strncasecmp_l (__const char *__s1, __const char *__s2,
     size_t __n, __locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 4)));
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
extern int strverscmp (__const char *__s1, __const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strfry (char *__string) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void *memfrob (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern char *basename (__const char *__filename) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int *__errno_location (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern char *program_invocation_name, *program_invocation_short_name;

typedef int error_t;
char *version_string = "GNU sed version 2.05";
struct vector
{
  struct sed_cmd *v;
  int v_length;
  int v_allocated;
  struct vector *return_v;
  int return_i;
};
struct sed_label
{
  struct vector *v;
  int v_index;
  char *name;
  struct sed_label *next;
};
enum addr_types
{
  addr_is_null = 0,
  addr_is_num = 1,
  addr_is_regex = 2,
  addr_is_last = 3,
  addr_is_mod = 4
};
struct addr
{
  int addr_type;
  struct re_pattern_buffer *addr_regex;
  int addr_number;
  int modulo, offset;
};
struct sed_cmd
{
  struct addr a1, a2;
  int aflags;
  char cmd;
  union
    {
      struct
 {
   char *text;
   int text_len;
 }
      cmd_txt;
      struct sed_cmd *label;
      FILE *io_file;
      struct
 {
   struct re_pattern_buffer *regx;
   char *replacement;
   int replace_length;
   int flags;
   int numb;
   FILE *wio_file;
 }
      cmd_regex;
      unsigned char *translate;
      struct vector *sub;
      struct sed_label *jump;
    } x;
};
struct line
{
  char *text;
  int length;
  int alloc;
};
struct
  {
    FILE *for_read;
    FILE *for_write;
    char *name;
  }
file_ptrs[32];
void close_files ();
void panic (char *str,...);
char *__fp_name (FILE * fp);
FILE *ck_fopen (char *name, char *mode);
void ck_fwrite (char *ptr, int size, int nmemb, FILE * stream);
void ck_fclose (FILE * stream);
void *ck_malloc (int size);
void *ck_realloc (void * ptr, int size);
char *ck_strdup (char *str);
void *init_buffer (void);
void flush_buffer (void * bb);
int size_buffer (void * b);
void add_buffer (void * bb, char *p, int n);
void add1_buffer (void * bb, int ch);
char *get_buffer (void * bb);
void compile_string (char *str);
void compile_file (char *str);
struct vector *compile_program (struct vector * vector, int);
void bad_prog (char *why);
int inchar (void);
void savchar (int ch);
int compile_address (struct addr * addr);
char * last_regex_string = 0;
void buffer_regex (int slash);
void compile_regex (void);
struct sed_label *setup_jump (struct sed_label * list, struct sed_cmd * cmd, struct vector * vec);
FILE *compile_filename (int readit);
void read_file (char *name);
void execute_program (struct vector * vec);
int match_address (struct addr * addr);
int read_pattern_space (void);
void append_pattern_space (void);
void line_copy (struct line * from, struct line * to);
void line_append (struct line * from, struct line * to);
void str_append (struct line * to, char *string, int length);
void usage (int);
extern char *myname;
int no_default_output = 0;
int input_line_number = 0;
int last_input_file = 0;
int input_EOF = 0;
int quit_cmd = 0;
int replaced = 0;
int program_depth = 0;
struct vector *the_program = 0;
struct sed_label *jumps = 0;
struct sed_label *labels = 0;
struct line line;
struct line hold;
struct line append;
unsigned char *prog_start;
unsigned char *prog_end;
unsigned char *prog_cur;
char *prog_name;
FILE *prog_file;
int prog_line = 1;
FILE *input_file;
int bad_input = 0;
struct re_pattern_buffer *last_regex;
static char ONE_ADDR[] = "Command only uses one address";
static char NO_ADDR[] = "Command doesn't take any addresses";
static char LINE_JUNK[] = "Extra characters after command";
static char BAD_EOF[] = "Unexpected End-of-file";
static char NO_REGEX[] = "No previous regular expression";
static char NO_COMMAND[] = "Missing command";
static struct option longopts[] =
{
  {"expression", 1, ((void *)0), 'e'},
  {"file", 1, ((void *)0), 'f'},
  {"quiet", 0, ((void *)0), 'n'},
  {"silent", 0, ((void *)0), 'n'},
  {"version", 0, ((void *)0), 'V'},
  {"help", 0, ((void *)0), 'h'},
  {((void *)0), 0, ((void *)0), 0}
};
int
main (argc, argv)
     int argc;
     char **argv;
{
  int opt;
  char *e_strings = ((void *)0);
  int compiled = 0;
  struct sed_label *go, *lbl;
  re_set_syntax ((((((1) << 1) << 1) | (((((((1) << 1) << 1) << 1) << 1) << 1) << 1) | ((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) | ((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) | (((((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)) | ((1) << 1)));
  rx_cache_bound = 4096;
 myname = "Executable";
  while ((opt = getopt_long (argc, argv, "hne:f:V", longopts, (int *) 0))
  != (-1))
    {
      switch (opt)
 {
 case 'n':
   no_default_output = 1;
   break;
 case 'e':
   if (e_strings == ((void *)0))
     {
       e_strings = ck_malloc (strlen (optarg) + 2);
       strcpy (e_strings, optarg);
     }
   else
     {
       e_strings = ck_realloc (e_strings, strlen (e_strings) + strlen (optarg) + 2);
       strcat (e_strings, optarg);
     }
   strcat (e_strings, "\n");
   compiled = 1;
   break;
 case 'f':
   if (e_strings)
     {
       compile_string (e_strings);
       free (e_strings);
       e_strings = 0;
     }
   compile_file (optarg);
   compiled = 1;
   break;
 case 'V':
   fprintf (stdout, "%s\n", version_string);
   exit (0);
   break;
 case 'h':
   usage (0);
   break;
 default:
   usage (4);
   break;
 }
    }
  if (e_strings)
    {
      compile_string (e_strings);
      free (e_strings);
    }
  if (!compiled)
    {
      if (optind == argc)
 usage (4);
      compile_string (argv[optind++]);
    }
  for (go = jumps; go; go = go->next)
    {
      for (lbl = labels; lbl; lbl = lbl->next)
 if (!strcmp (lbl->name, go->name))
   break;
      if (*go->name && !lbl)
 panic ("Can't find label for jump to '%s'", go->name);
      go->v->v[go->v_index].x.jump = lbl;
    }
  line.length = 0;
  line.alloc = 50;
  line.text = ck_malloc (50);
  append.length = 0;
  append.alloc = 50;
  append.text = ck_malloc (50);
  hold.length = 1;
  hold.alloc = 50;
  hold.text = ck_malloc (50);
  hold.text[0] = '\n';
  if (argc <= optind)
    {
      last_input_file++;
      read_file ("-");
    }
  else
    while (optind < argc)
      {
 if (optind == argc - 1)
   last_input_file++;
 read_file (argv[optind]);
 optind++;
 if (quit_cmd)
   break;
      }
  close_files ();
  if (bad_input)
    exit (2);
  exit (0);
}
void
close_files ()
{
  int nf;
  for (nf = 0; nf < 32; nf++)
    {
      if (file_ptrs[nf].for_write)
 fclose (file_ptrs[nf].for_write);
      if (file_ptrs[nf].for_read)
 fclose (file_ptrs[nf].for_read);
    }
}
void
compile_string (str)
     char *str;
{
  prog_file = 0;
  prog_line = 0;
  prog_start = prog_cur = (unsigned char *)str;
  prog_end = (unsigned char *)str + strlen (str);
  the_program = compile_program (the_program, prog_line);
}
void
compile_file (str)
     char *str;
{
  int ch;
  prog_start = prog_cur = prog_end = 0;
  prog_name = str;
  prog_line = 1;
  if (str[0] == '-' && str[1] == '\0')
    prog_file = stdin;
  else
    prog_file = ck_fopen (str, "r");
  ch = _IO_getc (prog_file);
  if (ch == '#')
    {
      ch = _IO_getc (prog_file);
      if (ch == 'n')
 no_default_output++;
      while (ch != (-1) && ch != '\n')
 {
   ch = _IO_getc (prog_file);
   if (ch == '\\')
     ch = _IO_getc (prog_file);
 }
      ++prog_line;
    }
  else if (ch != (-1))
    ungetc (ch, prog_file);
  the_program = compile_program (the_program, prog_line);
}
struct vector *
compile_program (vector, open_line)
     struct vector *vector;
     int open_line;
{
  struct sed_cmd *cur_cmd;
  int ch = 0;
  int pch;
  int slash;
  void *b;
  unsigned char *string;
  int num;
  if (!vector)
    {
      vector = (struct vector *) ck_malloc (sizeof (struct vector));
      vector->v = (struct sed_cmd *) ck_malloc (40 * sizeof (struct sed_cmd));
      vector->v_allocated = 40;
      vector->v_length = 0;
      vector->return_v = 0;
      vector->return_i = 0;
    }
  for (;;)
    {
    skip_comment:
      do
 {
   pch = ch;
   ch = inchar ();
   if ((pch == '\\') && (ch == '\n'))
     ch = inchar ();
 }
      while (ch != (-1) && (((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISblank) || ch == '\n' || ch == ';'));
      if (ch == (-1))
 break;
      savchar (ch);
      if (vector->v_length == vector->v_allocated)
 {
   vector->v = ((struct sed_cmd *)
         ck_realloc ((void *) vector->v,
       ((vector->v_length + 40)
        * sizeof (struct sed_cmd))));
   vector->v_allocated += 40;
 }
      cur_cmd = vector->v + vector->v_length;
      vector->v_length++;
      cur_cmd->a1.addr_type = 0;
      cur_cmd->a2.addr_type = 0;
      cur_cmd->aflags = 0;
      cur_cmd->cmd = 0;
      if (compile_address (&(cur_cmd->a1)))
 {
   ch = inchar ();
   if (ch == ',')
     {
       do
  ch = inchar ();
       while (ch != (-1) && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISblank));
       savchar (ch);
       if (compile_address (&(cur_cmd->a2)))
  ;
       else
  bad_prog ("Unexpected ','");
     }
   else
     savchar (ch);
 }
      if (cur_cmd->a1.addr_type == addr_is_num
   && cur_cmd->a2.addr_type == addr_is_num
   && cur_cmd->a2.addr_number < cur_cmd->a1.addr_number)
 cur_cmd->a2.addr_number = cur_cmd->a1.addr_number;
      ch = inchar ();
      if (ch == (-1))
 bad_prog (NO_COMMAND);
    new_cmd:
      switch (ch)
 {
 case '#':
   if (cur_cmd->a1.addr_type != 0)
     bad_prog (NO_ADDR);
   do
     {
       ch = inchar ();
       if (ch == '\\')
  ch = inchar ();
     }
   while (ch != (-1) && ch != '\n');
   vector->v_length--;
   goto skip_comment;
 case '!':
   if (cur_cmd->aflags & 02)
     bad_prog ("Multiple '!'s");
   cur_cmd->aflags |= 02;
   do
     ch = inchar ();
   while (ch != (-1) && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISblank));
   if (ch == (-1))
     bad_prog (NO_COMMAND);
   goto new_cmd;
 case 'a':
 case 'i':
   if (cur_cmd->a2.addr_type != 0)
     bad_prog (ONE_ADDR);
 case 'c':
   cur_cmd->cmd = ch;
   if (inchar () != '\\' || inchar () != '\n')
     bad_prog (LINE_JUNK);
   b = init_buffer ();
   while ((ch = inchar ()) != (-1) && ch != '\n')
     {
       if (ch == '\\')
  ch = inchar ();
       add1_buffer (b, ch);
     }
   if (ch != (-1))
     add1_buffer (b, ch);
   num = size_buffer (b);
   string = (unsigned char *) ck_malloc (num);
   bcopy (get_buffer (b), string, num);
   flush_buffer (b);
   cur_cmd->x.cmd_txt.text_len = num;
   cur_cmd->x.cmd_txt.text = (char *) string;
   break;
 case '{':
   cur_cmd->cmd = ch;
   program_depth++;
   cur_cmd->x.sub = compile_program ((struct vector *) 0, prog_line);
   cur_cmd->x.sub->return_v = vector;
   cur_cmd->x.sub->return_i = vector->v_length - 1;
   break;
 case '}':
   if (!program_depth)
     bad_prog ("Unexpected '}'");
   --program_depth;
   cur_cmd->cmd = ch;
   if (cur_cmd->a1.addr_type != 0)
     bad_prog ("} doesn't want any addresses");
   while ((ch = inchar ()) != (-1) && ch != '\n' && ch != ';')
     if (!((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISblank))
       bad_prog (LINE_JUNK);
   return vector;
 case ':':
   cur_cmd->cmd = ch;
   if (cur_cmd->a1.addr_type != 0)
     bad_prog (": doesn't want any addresses");
   labels = setup_jump (labels, cur_cmd, vector);
   break;
 case 'b':
 case 't':
   cur_cmd->cmd = ch;
   jumps = setup_jump (jumps, cur_cmd, vector);
   break;
 case 'q':
 case '=':
   if (cur_cmd->a2.addr_type)
     bad_prog (ONE_ADDR);
 case 'd':
 case 'D':
 case 'g':
 case 'G':
 case 'h':
 case 'H':
 case 'l':
 case 'n':
 case 'N':
 case 'p':
 case 'P':
 case 'x':
   cur_cmd->cmd = ch;
   do
     ch = inchar ();
   while (ch != (-1) && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISblank) && ch != '\n' && ch != ';');
   if (ch != '\n' && ch != ';' && ch != (-1))
     bad_prog (LINE_JUNK);
   break;
 case 'r':
   if (cur_cmd->a2.addr_type != 0)
     bad_prog (ONE_ADDR);
 case 'w':
   cur_cmd->cmd = ch;
   cur_cmd->x.io_file = compile_filename (ch == 'r');
   break;
 case 's':
   cur_cmd->cmd = ch;
   slash = inchar ();
   buffer_regex (slash);
   compile_regex ();
   cur_cmd->x.cmd_regex.regx = last_regex;
   b = init_buffer ();
   while (((ch = inchar ()) != (-1)) && (ch != slash) && (ch != '\n'))
     {
       if (ch == '\\')
  {
    int ci;
    ci = inchar ();
    if (ci != (-1))
      {
        if (ci != '\n')
   add1_buffer (b, ch);
        add1_buffer (b, ci);
      }
  }
       else
  add1_buffer (b, ch);
     }
   if (ch != slash)
     {
       if (ch == '\n' && prog_line > 1)
  --prog_line;
       bad_prog ("Unterminated `s' command");
     }
   cur_cmd->x.cmd_regex.replace_length = size_buffer (b);
   cur_cmd->x.cmd_regex.replacement = ck_malloc (cur_cmd->x.cmd_regex.replace_length);
   bcopy (get_buffer (b), cur_cmd->x.cmd_regex.replacement, cur_cmd->x.cmd_regex.replace_length);
   flush_buffer (b);
   cur_cmd->x.cmd_regex.flags = 0;
   cur_cmd->x.cmd_regex.numb = 0;
   if (ch == (-1))
     break;
   do
     {
       ch = inchar ();
       switch (ch)
  {
  case 'p':
    if (cur_cmd->x.cmd_regex.flags & 02)
      bad_prog ("multiple 'p' options to 's' command");
    cur_cmd->x.cmd_regex.flags |= 02;
    break;
  case 'g':
    if (cur_cmd->x.cmd_regex.flags & 010)
      cur_cmd->x.cmd_regex.flags &= ~010;
    if (cur_cmd->x.cmd_regex.flags & 01)
      bad_prog ("multiple 'g' options to 's' command");
    cur_cmd->x.cmd_regex.flags |= 01;
    break;
  case 'w':
    cur_cmd->x.cmd_regex.flags |= 04;
    cur_cmd->x.cmd_regex.wio_file = compile_filename (0);
    ch = '\n';
    break;
  case '0':
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    if (cur_cmd->x.cmd_regex.flags & 010)
      bad_prog ("multiple number options to 's' command");
    if ((cur_cmd->x.cmd_regex.flags & 01) == 0)
      cur_cmd->x.cmd_regex.flags |= 010;
    num = 0;
    while (((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISdigit))
      {
        num = num * 10 + ch - '0';
        ch = inchar ();
      }
    savchar (ch);
    cur_cmd->x.cmd_regex.numb = num;
    break;
  case '\n':
  case ';':
  case (-1):
    break;
  default:
    bad_prog ("Unknown option to 's'");
    break;
  }
     }
   while (ch != (-1) && ch != '\n' && ch != ';');
   if (ch == (-1))
     break;
   break;
 case 'y':
   cur_cmd->cmd = ch;
   string = (unsigned char *) ck_malloc (256);
   for (num = 0; num < 256; num++)
     string[num] = num;
   b = init_buffer ();
   slash = inchar ();
   while ((ch = inchar ()) != (-1) && ch != slash)
     add1_buffer (b, ch);
   cur_cmd->x.translate = string;
   string = (unsigned char *) get_buffer (b);
   for (num = size_buffer (b); num; --num)
     {
       ch = inchar ();
       if (ch == (-1))
  bad_prog (BAD_EOF);
       if (ch == slash)
  bad_prog ("strings for y command are different lengths");
       cur_cmd->x.translate[*string++] = ch;
     }
   flush_buffer (b);
   if (inchar () != slash || ((ch = inchar ()) != (-1) && ch != '\n' && ch != ';'))
     bad_prog (LINE_JUNK);
   break;
 default:
   bad_prog ("Unknown command");
 }
    }
  if (program_depth)
    {
      prog_line = open_line;
      bad_prog ("Unmatched `{'");
    }
  return vector;
}
void
bad_prog (why)
     char *why;
{
  if (prog_line > 0)
    fprintf (stdout, "%s: file %s line %d: %s\n",
      myname, prog_name, prog_line, why);
  else
    fprintf (stdout, "%s: %s\n", myname, why);
  exit (1);
}
int
inchar ()
{
  int ch;
  if (prog_file)
    {
      if (feof (prog_file))
 return (-1);
      else
 ch = _IO_getc (prog_file);
    }
  else
    {
      if (!prog_cur)
 return (-1);
      else if (prog_cur == prog_end)
 {
   ch = (-1);
   prog_cur = 0;
 }
      else
 ch = *prog_cur++;
    }
  if ((ch == '\n') && prog_line)
    prog_line++;
  return ch;
}
void
savchar (ch)
     int ch;
{
  if (ch == (-1))
    return;
  if (ch == '\n' && prog_line > 1)
    --prog_line;
  if (prog_file)
    ungetc (ch, prog_file);
  else
    *--prog_cur = ch;
}
int
compile_address (addr)
     struct addr *addr;
{
  int ch;
  int num;
  ch = inchar ();
  if (((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISdigit))
    {
      num = ch - '0';
      while ((ch = inchar ()) != (-1) && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISdigit))
 num = num * 10 + ch - '0';
      if (ch == '~')
 {
   addr->addr_type = addr_is_mod;
   addr->offset = num;
   ch = inchar();
   num=0;
   if (((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISdigit)) {
     num = ch - '0';
     while ((ch = inchar ()) != (-1) && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISdigit))
       num = num * 10 + ch - '0';
     addr->modulo = num;
   }
   addr->modulo += (addr->modulo==0);
 }
      else
 {
   addr->addr_type = addr_is_num;
   addr->addr_number = num;
 }
      while (ch != (-1) && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISblank))
 ch = inchar ();
      savchar (ch);
      return 1;
    }
  else if (ch == '/' || ch == '\\')
    {
      addr->addr_type = addr_is_regex;
      if (ch == '\\')
 ch = inchar ();
      buffer_regex (ch);
      addr->addr_regex = last_regex;
      do
 ch = inchar ();
      while (ch != (-1) && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISblank));
      savchar (ch);
      return 1;
    }
  else if (ch == '$')
    {
      addr->addr_type = addr_is_last;
      do
 ch = inchar ();
      while (ch != (-1) && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISblank));
      savchar (ch);
      return 1;
    }
  else
    savchar (ch);
  return 0;
}
void
buffer_regex (slash)
     int slash;
{
  void *b;
  int ch;
  int char_class_pos = -1;
  b = init_buffer ();
  while ((ch = inchar ()) != (-1) && (ch != slash || (char_class_pos >= 0)))
    {
      if (ch == '^')
 {
   if (size_buffer (b) == 0)
     {
       add1_buffer (b, '\\');
       add1_buffer (b, '`');
     }
   else
     add1_buffer (b, ch);
   continue;
 }
      else if (ch == '$')
 {
   ch = inchar ();
   savchar (ch);
   if (ch == slash)
     {
       add1_buffer (b, '\\');
       add1_buffer (b, '\'');
     }
   else
     add1_buffer (b, '$');
   continue;
 }
      else if (ch == '[')
 {
   if (char_class_pos < 0)
     char_class_pos = size_buffer (b);
   add1_buffer (b, ch);
   continue;
 }
      else if (ch == ']')
 {
   add1_buffer (b, ch);
   {
     char * regexp = get_buffer (b);
     int pos = size_buffer (b) - 1;
     if (!( (char_class_pos >= 0)
    && ( (pos == char_class_pos + 1)
        || ( (pos == char_class_pos + 2)
     && (regexp[char_class_pos + 1] == '^')))))
       char_class_pos = -1;
     continue;
   }
 }
      else if (ch != '\\' || (char_class_pos >= 0))
 {
   add1_buffer (b, ch);
   continue;
 }
      ch = inchar ();
      switch (ch)
 {
 case 'n':
   add1_buffer (b, '\n');
   break;
 case (-1):
   break;
 default:
   add1_buffer (b, '\\');
   add1_buffer (b, ch);
   break;
 }
    }
  if (ch == (-1))
    bad_prog (BAD_EOF);
  if (size_buffer (b))
    {
      if (last_regex_string)
 last_regex_string = (char *)ck_realloc (last_regex_string,
      size_buffer (b) + 1);
      else
 last_regex_string = (char *)ck_malloc (size_buffer (b) + 1);
      bcopy (get_buffer (b), last_regex_string, size_buffer (b));
      last_regex_string [size_buffer (b)] = 0;
    }
  else if (!last_regex)
    bad_prog (NO_REGEX);
  flush_buffer (b);
}
void
compile_regex ()
{
  const char * error;
  last_regex = ((struct re_pattern_buffer *)
  ck_malloc (sizeof (struct re_pattern_buffer)));
  memset ((last_regex), 0, (sizeof (*last_regex)));
  last_regex->fastmap = ck_malloc (256);
  error = re_compile_pattern (last_regex_string,
         strlen (last_regex_string), last_regex);
  if (error)
    bad_prog ((char *)error);
}
struct sed_label *
setup_jump (list, cmd, vec)
     struct sed_label *list;
     struct sed_cmd *cmd;
     struct vector *vec;
{
  struct sed_label *tmp;
  void *b;
  int ch;
  b = init_buffer ();
  while ((ch = inchar ()) != (-1) && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISblank))
    ;
  while (ch != (-1) && ch != '\n' && (!((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISblank)) && ch != ';' && ch != '}')
    {
      add1_buffer (b, ch);
      ch = inchar ();
    }
  savchar (ch);
  add1_buffer (b, '\0');
  tmp = (struct sed_label *) ck_malloc (sizeof (struct sed_label));
  tmp->v = vec;
  tmp->v_index = cmd - vec->v;
  tmp->name = ck_strdup (get_buffer (b));
  tmp->next = list;
  flush_buffer (b);
  return tmp;
}
FILE *
compile_filename (readit)
     int readit;
{
  char *file_name;
  int n;
  void *b;
  int ch;
  if (inchar () != ' ')
    bad_prog ("missing ' ' before filename");
  b = init_buffer ();
  while ((ch = inchar ()) != (-1) && ch != '\n')
    add1_buffer (b, ch);
  add1_buffer (b, '\0');
  file_name = get_buffer (b);
  for (n = 0; n < 32; n++)
    {
      if (!file_ptrs[n].name)
 break;
    }
  if (n < 32)
    {
      file_ptrs[n].name = ck_strdup (file_name);
      if (!readit)
 {
   if (!file_ptrs[n].for_write)
     file_ptrs[n].for_write = ck_fopen (file_name, "w");
 }
      else
 {
   if (!file_ptrs[n].for_read)
     file_ptrs[n].for_read = fopen (file_name, "r");
 }
      flush_buffer (b);
      return readit ? file_ptrs[n].for_read : file_ptrs[n].for_write;
    }
  else
    {
      bad_prog ("Hopelessely evil compiled in limit on number of open files.  re-compile sed");
      return 0;
    }
}
void
read_file (name)
     char *name;
{
  if (*name == '-' && name[1] == '\0')
    input_file = stdin;
  else
    {
      input_file = fopen (name, "r");
      if (input_file == 0)
 {
   char *ptr = strerror((*__errno_location ()));
   bad_input++;
   fprintf (stdout, "%s: can't read %s: %s\n", myname, name, ptr);
   return;
 }
    }
  while (read_pattern_space ())
    {
      execute_program (the_program);
      if (!no_default_output)
 ck_fwrite (line.text, 1, line.length, stdout);
      if (append.length)
 {
   ck_fwrite (append.text, 1, append.length, stdout);
   append.length = 0;
 }
      if (quit_cmd)
 break;
    }
  ck_fclose (input_file);
}
static char *
eol_pos (str, len)
     char *str;
     int len;
{
  while (len--)
    if (*str++ == '\n')
      return --str;
  return --str;
}
static void
chr_copy (dest, src, len)
     char *dest;
     char *src;
     int len;
{
  while (len--)
    *dest++ = *src++;
}
static struct re_registers regs =
{0, 0, 0};
void
execute_program (vec)
     struct vector *vec;
{
  struct sed_cmd *cur_cmd;
  int n;
  int addr_matched;
  static int end_cycle;
  int start;
  int remain;
  int offset;
  static struct line tmp;
  struct line t;
  char *rep, *rep_end, *rep_next, *rep_cur;
  int count;
  struct vector *restart_vec = vec;
restart:
  vec = restart_vec;
  count = 0;
  end_cycle = 0;
  for (cur_cmd = vec->v, n = vec->v_length; n; cur_cmd++, n--)
    {
    exe_loop:
      addr_matched = 0;
      if (cur_cmd->aflags & 01)
 {
   addr_matched = 1;
   if (match_address (&(cur_cmd->a2)))
     cur_cmd->aflags &= ~01;
 }
      else if (match_address (&(cur_cmd->a1)))
 {
   addr_matched = 1;
   if (cur_cmd->a2.addr_type != addr_is_null)
     if ( (cur_cmd->a2.addr_type == addr_is_regex)
  || !match_address (&(cur_cmd->a2)))
       cur_cmd->aflags |= 01;
 }
      if (cur_cmd->aflags & 02)
 addr_matched = !addr_matched;
      if (!addr_matched)
 continue;
      switch (cur_cmd->cmd)
 {
 case '{':
   if (cur_cmd->x.sub->v_length)
     {
       vec = cur_cmd->x.sub;
       cur_cmd = vec->v;
       n = vec->v_length;
       goto exe_loop;
     }
   break;
 case '}':
   cur_cmd = vec->return_v->v + vec->return_i;
   n = vec->return_v->v_length - vec->return_i;
   vec = vec->return_v;
   break;
 case ':':
   break;
 case '=':
   printf ("%d\n", input_line_number);
   break;
 case 'a':
   while (append.alloc - append.length < cur_cmd->x.cmd_txt.text_len)
     {
       append.alloc *= 2;
       append.text = ck_realloc (append.text, append.alloc);
     }
   bcopy (cur_cmd->x.cmd_txt.text,
   append.text + append.length, cur_cmd->x.cmd_txt.text_len);
   append.length += cur_cmd->x.cmd_txt.text_len;
   break;
 case 'b':
   if (!cur_cmd->x.jump)
     end_cycle++;
   else
     {
       struct sed_label *j = cur_cmd->x.jump;
       n = j->v->v_length - j->v_index;
       cur_cmd = j->v->v + j->v_index;
       vec = j->v;
       goto exe_loop;
     }
   break;
 case 'c':
   line.length = 0;
   if (!((cur_cmd->aflags & 01)))
     ck_fwrite (cur_cmd->x.cmd_txt.text,
         1, cur_cmd->x.cmd_txt.text_len, stdout);
   end_cycle++;
   break;
 case 'd':
   line.length = 0;
   end_cycle++;
   break;
 case 'D':
   {
     char *tmp;
     int newlength;
     tmp = eol_pos (line.text, line.length);
     newlength = line.length - (tmp - line.text) - 1;
     if (newlength)
       {
  chr_copy (line.text, tmp + 1, newlength);
  line.length = newlength;
  goto restart;
       }
     line.length = 0;
     end_cycle++;
   }
   break;
 case 'g':
   line_copy (&hold, &line);
   break;
 case 'G':
   line_append (&hold, &line);
   break;
 case 'h':
   line_copy (&line, &hold);
   break;
 case 'H':
   line_append (&line, &hold);
   break;
 case 'i':
   ck_fwrite (cur_cmd->x.cmd_txt.text, 1,
       cur_cmd->x.cmd_txt.text_len, stdout);
   break;
 case 'l':
   {
     char *tmp;
     int n;
     int width = 0;
     n = line.length;
     tmp = line.text;
     while (n--)
       {
  if (!n && (*tmp == '\n'))
    break;
  if (width > 77)
    {
      width = 0;
      putchar ('\n');
    }
  if (*tmp == '\\')
    {
      printf ("\\\\");
      width += 2;
    }
  else if (((*__ctype_b_loc ())[(int) ((*tmp))] & (unsigned short int) _ISprint))
    {
      putchar (*tmp);
      width++;
    }
  else
    switch (*tmp)
      {
      case 007:
        printf ("\\a");
        width += 2;
        break;
      case '\b':
        printf ("\\b");
        width += 2;
        break;
      case '\f':
        printf ("\\f");
        width += 2;
        break;
      case '\n':
        printf ("\\n");
        width += 2;
        break;
      case '\r':
        printf ("\\r");
        width += 2;
        break;
      case '\t':
        printf ("\\t");
        width += 2;
        break;
      case '\v':
        printf ("\\v");
        width += 2;
        break;
      default:
        printf ("\\%02x", (*tmp) & 0xFF);
        width += 2;
        break;
      }
  tmp++;
       }
     putchar ('\n');
   }
   break;
 case 'n':
   if (feof (input_file))
     goto quit;
   if (!no_default_output)
     ck_fwrite (line.text, 1, line.length, stdout);
   read_pattern_space ();
   break;
 case 'N':
   if (feof (input_file))
     {
       line.length = 0;
       goto quit;
     }
   append_pattern_space ();
   break;
 case 'p':
   ck_fwrite (line.text, 1, line.length, stdout);
   break;
 case 'P':
   {
     char *tmp;
     tmp = eol_pos (line.text, line.length);
     ck_fwrite (line.text, 1,
         tmp ? tmp - line.text + 1
         : line.length, stdout);
   }
   break;
 case 'q':
 quit:
   quit_cmd++;
   end_cycle++;
   break;
 case 'r':
   {
     int n = 0;
     if (cur_cmd->x.io_file)
       {
  rewind (cur_cmd->x.io_file);
  do
    {
      append.length += n;
      if (append.length == append.alloc)
        {
   append.alloc *= 2;
   append.text = ck_realloc (append.text, append.alloc);
        }
      n = fread (append.text + append.length, sizeof (char),
          append.alloc - append.length,
          cur_cmd->x.io_file);
    }
  while (n > 0);
  if (ferror (cur_cmd->x.io_file))
    panic ("Read error on input file to 'r' command");
       }
   }
   break;
 case 's':
   {
     int trail_nl_p = line.text [line.length - 1] == '\n';
     if (!tmp.alloc)
       {
  tmp.alloc = 50;
  tmp.text = ck_malloc (50);
       }
     count = 0;
     start = 0;
     remain = line.length - trail_nl_p;
     tmp.length = 0;
     rep = cur_cmd->x.cmd_regex.replacement;
     rep_end = rep + cur_cmd->x.cmd_regex.replace_length;
     while ((offset = re_search (cur_cmd->x.cmd_regex.regx,
     line.text,
     line.length - trail_nl_p,
     start,
     remain,
     &regs)) >= 0)
       {
  count++;
  if (offset - start)
    str_append (&tmp, line.text + start, offset - start);
  if (cur_cmd->x.cmd_regex.flags & 010)
    {
      if (count != cur_cmd->x.cmd_regex.numb)
        {
   int matched = regs.end[0] - regs.start[0];
   if (!matched) matched = 1;
   str_append (&tmp, line.text + regs.start[0], matched);
   start = (offset == regs.end[0]
     ? offset + 1 : regs.end[0]);
   remain = (line.length - trail_nl_p) - start;
   continue;
        }
    }
  for (rep_next = rep_cur = rep; rep_next < rep_end; rep_next++)
    {
      if (*rep_next == '&')
        {
   if (rep_next - rep_cur)
     str_append (&tmp, rep_cur, rep_next - rep_cur);
   str_append (&tmp, line.text + regs.start[0], regs.end[0] - regs.start[0]);
   rep_cur = rep_next + 1;
        }
      else if (*rep_next == '\\')
        {
   if (rep_next - rep_cur)
     str_append (&tmp, rep_cur, rep_next - rep_cur);
   rep_next++;
   if (rep_next != rep_end)
     {
       int n;
       if (*rep_next >= '0' && *rep_next <= '9')
         {
    n = *rep_next - '0';
    str_append (&tmp, line.text + regs.start[n], regs.end[n] - regs.start[n]);
         }
       else
         str_append (&tmp, rep_next, 1);
     }
   rep_cur = rep_next + 1;
        }
    }
  if (rep_next - rep_cur)
    str_append (&tmp, rep_cur, rep_next - rep_cur);
  if (offset == regs.end[0])
    {
      str_append (&tmp, line.text + offset, 1);
      ++regs.end[0];
    }
  start = regs.end[0];
  remain = (line.length - trail_nl_p) - start;
  if (remain < 0)
    break;
  if (!(cur_cmd->x.cmd_regex.flags & 01))
    break;
       }
     if (!count)
       break;
     replaced = 1;
     str_append (&tmp, line.text + start, remain + trail_nl_p);
     t.text = line.text;
     t.length = line.length;
     t.alloc = line.alloc;
     line.text = tmp.text;
     line.length = tmp.length;
     line.alloc = tmp.alloc;
     tmp.text = t.text;
     tmp.length = t.length;
     tmp.alloc = t.alloc;
     if ((cur_cmd->x.cmd_regex.flags & 04)
  && cur_cmd->x.cmd_regex.wio_file)
       ck_fwrite (line.text, 1, line.length,
    cur_cmd->x.cmd_regex.wio_file);
     if (cur_cmd->x.cmd_regex.flags & 02)
       ck_fwrite (line.text, 1, line.length, stdout);
     break;
   }
 case 't':
   if (replaced)
     {
       replaced = 0;
       if (!cur_cmd->x.jump)
  end_cycle++;
       else
  {
    struct sed_label *j = cur_cmd->x.jump;
    n = j->v->v_length - j->v_index;
    cur_cmd = j->v->v + j->v_index;
    vec = j->v;
    goto exe_loop;
  }
     }
   break;
 case 'w':
   if (cur_cmd->x.io_file)
     {
       ck_fwrite (line.text, 1, line.length, cur_cmd->x.io_file);
       fflush (cur_cmd->x.io_file);
     }
   break;
 case 'x':
   {
     struct line tmp;
     tmp = line;
     line = hold;
     hold = tmp;
   }
   break;
 case 'y':
   {
     unsigned char *p, *e;
     for (p = (unsigned char *) (line.text), e = p + line.length;
   p < e;
   p++)
       *p = cur_cmd->x.translate[*p];
   }
   break;
 default:
   panic ("INTERNAL ERROR: Bad cmd %c", cur_cmd->cmd);
 }
      if (end_cycle)
 break;
    }
}
int
match_address (addr)
     struct addr *addr;
{
  switch (addr->addr_type)
    {
    case addr_is_null:
      return 1;
    case addr_is_num:
      return (input_line_number == addr->addr_number);
    case addr_is_mod:
      return ((input_line_number%addr->modulo) == addr->offset);
    case addr_is_regex:
      {
 int trail_nl_p = line.text [line.length - 1] == '\n';
 return (re_search (addr->addr_regex,
      line.text,
      line.length - trail_nl_p,
      0,
      line.length - trail_nl_p,
      (struct re_registers *) 0) >= 0) ? 1 : 0;
      }
    case addr_is_last:
      return (input_EOF) ? 1 : 0;
    default:
      panic ("INTERNAL ERROR: bad address type");
      break;
    }
  return -1;
}
int
read_pattern_space ()
{
  int n;
  char *p;
  int ch;
  p = line.text;
  n = line.alloc;
  if (feof (input_file))
    return 0;
  input_line_number++;
  replaced = 0;
  for (;;)
    {
      if (n == 0)
 {
   line.text = ck_realloc (line.text, line.alloc * 2);
   p = line.text + line.alloc;
   n = line.alloc;
   line.alloc *= 2;
 }
      ch = _IO_getc (input_file);
      if (ch == (-1))
 {
   if (n == line.alloc)
     return 0;
   line.length = line.alloc - n;
   if (last_input_file)
     input_EOF++;
   return 1;
 }
      *p++ = ch;
      --n;
      if (ch == '\n')
 {
   line.length = line.alloc - n;
   break;
 }
    }
  ch = _IO_getc (input_file);
  if (ch != (-1))
    ungetc (ch, input_file);
  else if (last_input_file)
    input_EOF++;
  return 1;
}
void
append_pattern_space ()
{
  char *p;
  int n;
  int ch;
  p = line.text + line.length;
  n = line.alloc - line.length;
  input_line_number++;
  replaced = 0;
  for (;;)
    {
      ch = _IO_getc (input_file);
      if (ch == (-1))
 {
   if (n == line.alloc)
     return;
   line.length = line.alloc - n;
   if (last_input_file)
     input_EOF++;
   return;
 }
      if (n == 0)
 {
   line.text = ck_realloc (line.text, line.alloc * 2);
   p = line.text + line.alloc;
   n = line.alloc;
   line.alloc *= 2;
 }
      *p++ = ch;
      --n;
      if (ch == '\n')
 {
   line.length = line.alloc - n;
   break;
 }
    }
  ch = _IO_getc (input_file);
  if (ch != (-1))
    ungetc (ch, input_file);
  else if (last_input_file)
    input_EOF++;
}
void
line_copy (from, to)
     struct line *from, *to;
{
  if (from->length > to->alloc)
    {
      to->alloc = from->length;
      to->text = ck_realloc (to->text, to->alloc);
    }
  bcopy (from->text, to->text, from->length);
  to->length = from->length;
}
void
line_append (from, to)
     struct line *from, *to;
{
  if (from->length > (to->alloc - to->length))
    {
      to->alloc += from->length;
      to->text = ck_realloc (to->text, to->alloc);
    }
  bcopy (from->text, to->text + to->length, from->length);
  to->length += from->length;
}
void
str_append (to, string, length)
     struct line *to;
     char *string;
     int length;
{
  if (length > to->alloc - to->length)
    {
      to->alloc += length;
      to->text = ck_realloc (to->text, to->alloc);
    }
  bcopy (string, to->text + to->length, length);
  to->length += length;
}
void
usage (status)
     int status;
{
  fprintf (status ? stdout : stdout, "Usage: %s [-nV] [--quiet] [--silent] [--version] [-e script]\n        [-f script-file] [--expression=script] [--file=script-file] [file...]\n",
    myname);
  exit (status);
}
void *ck_malloc();
char *myname;
void
panic(char *str, ...)
{
 va_list iggy;
 fprintf(stdout,"%s: ",myname);
 __builtin_va_start(iggy,str);
 vfprintf(stdout,str,iggy);
 __builtin_va_end(iggy);
 _IO_putc ('\n', stdout);
 exit(4);
}
struct id {
 FILE *fp;
 char *name;
};
static struct id __id_s[32];
char *
__fp_name(fp)
FILE *fp;
{
 int n;
 for(n=0;n<32;n++) {
  if(__id_s[n].fp==fp)
   return __id_s[n].name;
 }
 return "{Unknown file pointer}";
}
FILE *
ck_fopen(name,mode)
char *name;
char *mode;
{
 FILE *ret;
 int n;
 ret=fopen(name,mode);
 if(ret==(FILE *)0)
  panic("Couldn't open file %s",name);
 for(n=0;n<32;n++) {
  if(ret==__id_s[n].fp) {
   free((void *)__id_s[n].name);
   __id_s[n].name=(char *)ck_malloc(strlen(name)+1);
   strcpy(__id_s[n].name,name);
   break;
  }
 }
 if(n==32) {
  for(n=0;n<32;n++)
   if(__id_s[n].fp==(FILE *)0)
    break;
  if(n==32)
   panic("Internal error: too many files open");
  __id_s[n].fp=ret;
  __id_s[n].name=(char *)ck_malloc(strlen(name)+1);
  strcpy(__id_s[n].name,name);
 }
 return ret;
}
void
ck_fwrite(ptr,size,nmemb,stream)
char *ptr;
int size,nmemb;
FILE *stream;
{
 if(fwrite(ptr,size,nmemb,stream)!=nmemb)
  panic("couldn't write %d items to %s",nmemb,__fp_name(stream));
}
void
ck_fclose(stream)
FILE *stream;
{
 if(fclose(stream)==(-1))
  panic("Couldn't close %s",__fp_name(stream));
}
void *
ck_malloc(size)
int size;
{
 void *ret;
 if(!size)
  size++;
 ret=malloc(size);
 if(ret==(void *)0)
  panic("Couldn't allocate memory");
 return ret;
}
void *
xmalloc(size)
int size;
{
  return ck_malloc (size);
}
void *
ck_realloc(ptr,size)
void *ptr;
int size;
{
 void *ret;
 if (!ptr)
   return ck_malloc (size);
 ret=realloc(ptr,size);
 if(ret==(void *)0)
  panic("Couldn't re-allocate memory");
 return ret;
}
char *
ck_strdup(str)
char *str;
{
 char *ret;
 ret=(char *)ck_malloc(strlen(str)+2);
 strcpy(ret,str);
 return ret;
}
struct buffer {
 int allocated;
 int length;
 char *b;
};
void *
init_buffer()
{
 struct buffer *b;
 b=(struct buffer *)ck_malloc(sizeof(struct buffer));
 b->allocated=50;
 b->b=(char *)ck_malloc(50);
 b->length=0;
 return (void *)b;
}
void
flush_buffer(bb)
void *bb;
{
 struct buffer *b;
 b=(struct buffer *)bb;
 free(b->b);
 b->b=0;
 b->allocated=0;
 b->length=0;
 free(b);
}
int
size_buffer(b)
void *b;
{
 struct buffer *bb;
 bb=(struct buffer *)b;
 return bb->length;
}
void
add_buffer(bb,p,n)
void *bb;
char *p;
int n;
{
 struct buffer *b;
 int x;
 char * cp;
 b=(struct buffer *)bb;
 if(b->length+n>b->allocated) {
  b->allocated = (b->length + n) * 2;
  b->b=(char *)ck_realloc(b->b,b->allocated);
 }
 x = n;
 cp = b->b + b->length;
 while (x--)
   *cp++ = *p++;
 b->length+=n;
}
void
add1_buffer(bb,ch)
void *bb;
int ch;
{
 struct buffer *b;
 b=(struct buffer *)bb;
 if(b->length+1>b->allocated) {
  b->allocated*=2;
  b->b=(char *)ck_realloc(b->b,b->allocated);
 }
 b->b[b->length]=ch;
 b->length++;
}
char *
get_buffer(bb)
void *bb;
{
 struct buffer *b;
 b=(struct buffer *)bb;
 return b->b;
}
static char rx_version_string[] = "GNU Rx version 0.03";
typedef char boolean;
static int rx_bitset_is_subset (int size, rx_Bitset a, rx_Bitset b);
static void rx_bitset_null (int size, rx_Bitset b);
static void rx_bitset_universe (int size, rx_Bitset b);
static void rx_bitset_complement (int size, rx_Bitset b);
static void rx_bitset_assign (int size, rx_Bitset a, rx_Bitset b);
static void rx_bitset_union (int size, rx_Bitset a, rx_Bitset b);
static void rx_bitset_intersection (int size,
         rx_Bitset a, rx_Bitset b);
static void rx_bitset_difference (int size, rx_Bitset a, rx_Bitset b);
static unsigned long rx_bitset_hash (int size, rx_Bitset b);
static struct rx_hash_item * rx_hash_find (struct rx_hash * table,
         unsigned long hash,
         void * value,
         struct rx_hash_rules * rules);
static struct rx_hash_item * rx_hash_store (struct rx_hash * table,
          unsigned long hash,
          void * value,
          struct rx_hash_rules * rules);
static void rx_hash_free (struct rx_hash_item * it,
      struct rx_hash_rules * rules);
static rx_Bitset rx_cset (struct rx *rx);
static rx_Bitset rx_copy_cset (struct rx *rx, rx_Bitset a);
static void rx_free_cset (struct rx * rx, rx_Bitset c);
static struct rexp_node * rexp_node (struct rx *rx,
          enum rexp_node_type type);
static struct rexp_node * rx_mk_r_cset (struct rx * rx,
      rx_Bitset b);
static struct rexp_node * rx_mk_r_concat (struct rx * rx,
        struct rexp_node * a,
        struct rexp_node * b);
static struct rexp_node * rx_mk_r_alternate (struct rx * rx,
           struct rexp_node * a,
           struct rexp_node * b);
static struct rexp_node * rx_mk_r_opt (struct rx * rx,
     struct rexp_node * a);
static struct rexp_node * rx_mk_r_star (struct rx * rx,
      struct rexp_node * a);
static struct rexp_node * rx_mk_r_2phase_star (struct rx * rx,
      struct rexp_node * a,
      struct rexp_node * b);
static struct rexp_node * rx_mk_r_side_effect (struct rx * rx,
      rx_side_effect a);
static struct rexp_node * rx_mk_r_data (struct rx * rx,
       void * a);
static void rx_free_rexp (struct rx * rx, struct rexp_node * node);
static struct rexp_node * rx_copy_rexp (struct rx *rx,
      struct rexp_node *node);
static struct rx_nfa_state * rx_nfa_state (struct rx *rx);
static void rx_free_nfa_state (struct rx_nfa_state * n);
static struct rx_nfa_state * rx_id_to_nfa_state (struct rx * rx,
        int id);
static struct rx_nfa_edge * rx_nfa_edge (struct rx *rx,
       enum rx_nfa_etype type,
       struct rx_nfa_state *start,
       struct rx_nfa_state *dest);
static void rx_free_nfa_edge (struct rx_nfa_edge * e);
static void rx_free_nfa (struct rx *rx);
static int rx_build_nfa (struct rx *rx,
     struct rexp_node *rexp,
     struct rx_nfa_state **start,
     struct rx_nfa_state **end);
static void rx_name_nfa_states (struct rx *rx);
static int rx_eclose_nfa (struct rx *rx);
static void rx_delete_epsilon_transitions (struct rx *rx);
static int rx_compactify_nfa (struct rx *rx,
          void **mem, unsigned long *size);
static struct rx_superset * rx_superstate_eclosure_union
  (struct rx * rx, struct rx_superset *set, struct rx_nfa_state_set *ecl) ;
static void rx_release_superset (struct rx *rx,
      struct rx_superset *set);
static struct rx_superstate * rx_superstate (struct rx *rx,
           struct rx_superset *set);
static struct rx_inx * rx_handle_cache_miss
  (struct rx *rx, struct rx_superstate *super, unsigned char chr, void *data) ;
static char re_syntax_table[(1 << 8)];
static void
init_syntax_once (void)
{
   register int c;
   static int done = 0;
   if (done)
     return;
   memset ((re_syntax_table), 0, (sizeof re_syntax_table));
   for (c = 'a'; c <= 'z'; c++)
     re_syntax_table[c] = 1;
   for (c = 'A'; c <= 'Z'; c++)
     re_syntax_table[c] = 1;
   for (c = '0'; c <= '9'; c++)
     re_syntax_table[c] = 1;
   re_syntax_table['_'] = 1;
   done = 1;
}
static int
rx_bitset_is_subset (int size, rx_Bitset a, rx_Bitset b)
{
  int x = (((size) + (32) - 1) / (32)) - 1;
  while (x-- && (a[x] & b[x]) == a[x]);
  return x == -1;
}
static void
rx_bitset_null (int size, rx_Bitset b)
{
  memset ((b), 0, (((((size) + (32) - 1) / (32)) * sizeof(RX_subset))));
}
static void
rx_bitset_universe (int size, rx_Bitset b)
{
  int x = (((size) + (32) - 1) / (32));
  while (x--)
    *b++ = ~(RX_subset)0;
}
static void
rx_bitset_complement (int size, rx_Bitset b)
{
  int x = (((size) + (32) - 1) / (32));
  while (x--)
    {
      *b = ~*b;
      ++b;
    }
}
static void
rx_bitset_assign (int size, rx_Bitset a, rx_Bitset b)
{
  int x;
  for (x = (((size) + (32) - 1) / (32)) - 1; x >=0; --x)
    a[x] = b[x];
}
static void
rx_bitset_union (int size, rx_Bitset a, rx_Bitset b)
{
  int x;
  for (x = (((size) + (32) - 1) / (32)) - 1; x >=0; --x)
    a[x] |= b[x];
}
static void
rx_bitset_intersection (int size,
   rx_Bitset a, rx_Bitset b)
{
  int x;
  for (x = (((size) + (32) - 1) / (32)) - 1; x >=0; --x)
    a[x] &= b[x];
}
static void
rx_bitset_difference (int size, rx_Bitset a, rx_Bitset b)
{
  int x;
  for (x = (((size) + (32) - 1) / (32)) - 1; x >=0; --x)
    a[x] &= ~ b[x];
}
static unsigned long
rx_bitset_hash (int size, rx_Bitset b)
{
  int x;
  unsigned long hash = (unsigned long)rx_bitset_hash;
  for (x = (((size) + (32) - 1) / (32)) - 1; x >= 0; --x)
    hash ^= ((b)[((x) / (32))]);
  return hash;
}
static RX_subset rx_subset_singletons [(32)] =
{
  0x1,
  0x2,
  0x4,
  0x8,
  0x10,
  0x20,
  0x40,
  0x80,
  0x100,
  0x200,
  0x400,
  0x800,
  0x1000,
  0x2000,
  0x4000,
  0x8000,
  0x10000,
  0x20000,
  0x40000,
  0x80000,
  0x100000,
  0x200000,
  0x400000,
  0x800000,
  0x1000000,
  0x2000000,
  0x4000000,
  0x8000000,
  0x10000000,
  0x20000000,
  0x40000000,
  0x80000000
};
static unsigned long rx_hash_masks[4] =
{
  0x12488421,
  0x96699669,
  0xbe7dd7eb,
  0xffffffff
};
static struct rx_hash_item *
rx_hash_find (struct rx_hash * table,
       unsigned long hash,
       void * value,
       struct rx_hash_rules * rules)
{
  rx_hash_eq eq = rules->eq;
  int maskc = 0;
  int mask = rx_hash_masks [0];
  int bucket = (hash & mask) % 13;
  while (table->children [bucket])
    {
      table = table->children [bucket];
      ++maskc;
      mask = rx_hash_masks[maskc];
      bucket = (hash & mask) % 13;
    }
  {
    struct rx_hash_item * it = table->buckets[bucket];
    while (it)
      if (eq (it->data, value))
 return it;
      else
 it = it->next_same_hash;
  }
  return 0;
}
static struct rx_hash_item *
rx_hash_store (struct rx_hash * table,
        unsigned long hash,
        void * value,
        struct rx_hash_rules * rules)
{
  rx_hash_eq eq = rules->eq;
  int maskc = 0;
  int mask = rx_hash_masks[0];
  int bucket = (hash & mask) % 13;
  int depth = 0;
  while (table->children [bucket])
    {
      table = table->children [bucket];
      ++maskc;
      mask = rx_hash_masks[maskc];
      bucket = (hash & mask) % 13;
      ++depth;
    }
  {
    struct rx_hash_item * it = table->buckets[bucket];
    while (it)
      if (eq (it->data, value))
 return it;
      else
 it = it->next_same_hash;
  }
  {
    if ( (depth < 3)
 && (table->bucket_size [bucket] >= 4))
      {
 struct rx_hash * newtab = ((struct rx_hash *)
       rules->hash_alloc (rules));
 if (!newtab)
   goto add_to_bucket;
 memset ((newtab), 0, (sizeof (*newtab)));
 newtab->parent = table;
 {
   struct rx_hash_item * them = table->buckets[bucket];
   unsigned long newmask = rx_hash_masks[maskc + 1];
   while (them)
     {
       struct rx_hash_item * save = them->next_same_hash;
       int new_buck = (them->hash & newmask) % 13;
       them->next_same_hash = newtab->buckets[new_buck];
       newtab->buckets[new_buck] = them;
       them->table = newtab;
       them = save;
       ++newtab->bucket_size[new_buck];
       ++newtab->refs;
     }
   table->refs = (table->refs - table->bucket_size[bucket] + 1);
   table->bucket_size[bucket] = 0;
   table->buckets[bucket] = 0;
   table->children[bucket] = newtab;
   table = newtab;
   bucket = (hash & newmask) % 13;
 }
      }
  }
 add_to_bucket:
  {
    struct rx_hash_item * it = ((struct rx_hash_item *)
     rules->hash_item_alloc (rules, value));
    if (!it)
      return 0;
    it->hash = hash;
    it->table = table;
    it->next_same_hash = table->buckets [bucket];
    table->buckets[bucket] = it;
    ++table->bucket_size [bucket];
    ++table->refs;
    return it;
  }
}
static void
rx_hash_free (struct rx_hash_item * it, struct rx_hash_rules * rules)
{
  if (it)
    {
      struct rx_hash * table = it->table;
      unsigned long hash = it->hash;
      int depth = (table->parent
     ? (table->parent->parent
        ? (table->parent->parent->parent
    ? 3
    : 2)
        : 1)
     : 0);
      int bucket = (hash & rx_hash_masks [depth]) % 13;
      struct rx_hash_item ** pos = &table->buckets [bucket];
      while (*pos != it)
 pos = &(*pos)->next_same_hash;
      *pos = it->next_same_hash;
                                              free(it);
      --table->bucket_size[bucket];
      --table->refs;
      while (!table->refs && depth)
 {
   struct rx_hash * save = table;
   table = table->parent;
   --depth;
   bucket = (hash & rx_hash_masks [depth]) % 13;
   --table->refs;
   table->children[bucket] = 0;
                                         free(save);
 }
    }
}
typedef void (*rx_hash_freefn) (struct rx_hash_item * it);
static void
rx_free_hash_table (struct rx_hash * tab, rx_hash_freefn freefn,
      struct rx_hash_rules * rules)
{
  int x;
  for (x = 0; x < 13; ++x)
    if (tab->children[x])
      {
 rx_free_hash_table (tab->children[x], freefn, rules);
                                                   free(tab->children[x]);
      }
    else
      {
 struct rx_hash_item * them = tab->buckets[x];
 while (them)
   {
     struct rx_hash_item * that = them;
     them = that->next_same_hash;
     freefn (that);
                                                free(that);
   }
      }
}
static rx_Bitset
rx_cset (struct rx *rx)
{
  rx_Bitset b = (rx_Bitset) malloc (((((rx->local_cset_size) + (32) - 1) / (32)) * sizeof(RX_subset)));
  if (b)
    rx_bitset_null (rx->local_cset_size, b);
  return b;
}
static rx_Bitset
rx_copy_cset (struct rx *rx, rx_Bitset a)
{
  rx_Bitset cs = rx_cset (rx);
  if (cs)
    rx_bitset_union (rx->local_cset_size, cs, a);
  return cs;
}
static void
rx_free_cset (struct rx * rx, rx_Bitset c)
{
  if (c)
    free ((char *)c);
}
struct rx_hash *
compiler_hash_alloc (struct rx_hash_rules * rules)
{
  return (struct rx_hash *)malloc (sizeof (struct rx_hash));
}
struct rx_hash_item *
compiler_hash_item_alloc (struct rx_hash_rules * rules, void * value)
{
  struct rx_hash_item * it;
  it = (struct rx_hash_item *)malloc (sizeof (*it));
  if (it)
    {
      it->data = value;
      it->binding = 0;
    }
  return it;
}
void
compiler_free_hash (struct rx_hash * tab,
      struct rx_hash_rules * rules)
{
  free ((char *)tab);
}
void
compiler_free_hash_item (struct rx_hash_item * item,
    struct rx_hash_rules * rules)
{
  free ((char *)item);
}
static struct rexp_node *
rexp_node (struct rx *rx,
    enum rexp_node_type type)
{
  struct rexp_node *n;
  n = (struct rexp_node *)malloc (sizeof (*n));
  memset ((n), 0, (sizeof (*n)));
  if (n)
    n->type = type;
  return n;
}
static struct rexp_node *
rx_mk_r_cset (struct rx * rx,
       rx_Bitset b)
{
  struct rexp_node * n = rexp_node (rx, r_cset);
  if (n)
    n->params.cset = b;
  return n;
}
static struct rexp_node *
rx_mk_r_concat (struct rx * rx,
  struct rexp_node * a,
  struct rexp_node * b)
{
  struct rexp_node * n = rexp_node (rx, r_concat);
  if (n)
    {
      n->params.pair.left = a;
      n->params.pair.right = b;
    }
  return n;
}
static struct rexp_node *
rx_mk_r_alternate (struct rx * rx,
     struct rexp_node * a,
     struct rexp_node * b)
{
  struct rexp_node * n = rexp_node (rx, r_alternate);
  if (n)
    {
      n->params.pair.left = a;
      n->params.pair.right = b;
    }
  return n;
}
static struct rexp_node *
rx_mk_r_opt (struct rx * rx,
      struct rexp_node * a)
{
  struct rexp_node * n = rexp_node (rx, r_opt);
  if (n)
    {
      n->params.pair.left = a;
      n->params.pair.right = 0;
    }
  return n;
}
static struct rexp_node *
rx_mk_r_star (struct rx * rx,
       struct rexp_node * a)
{
  struct rexp_node * n = rexp_node (rx, r_star);
  if (n)
    {
      n->params.pair.left = a;
      n->params.pair.right = 0;
    }
  return n;
}
static struct rexp_node *
rx_mk_r_2phase_star (struct rx * rx,
       struct rexp_node * a,
       struct rexp_node * b)
{
  struct rexp_node * n = rexp_node (rx, r_2phase_star);
  if (n)
    {
      n->params.pair.left = a;
      n->params.pair.right = b;
    }
  return n;
}
static struct rexp_node *
rx_mk_r_side_effect (struct rx * rx,
       rx_side_effect a)
{
  struct rexp_node * n = rexp_node (rx, r_side_effect);
  if (n)
    {
      n->params.side_effect = a;
      n->params.pair.right = 0;
    }
  return n;
}
static struct rexp_node *
rx_mk_r_data (struct rx * rx,
        void * a)
{
  struct rexp_node * n = rexp_node (rx, r_data);
  if (n)
    {
      n->params.pair.left = a;
      n->params.pair.right = 0;
    }
  return n;
}
static void
rx_free_rexp (struct rx * rx, struct rexp_node * node)
{
  if (node)
    {
      switch (node->type)
 {
 case r_cset:
   if (node->params.cset)
     rx_free_cset (rx, node->params.cset);
 case r_side_effect:
   break;
 case r_concat:
 case r_alternate:
 case r_2phase_star:
 case r_opt:
 case r_star:
   rx_free_rexp (rx, node->params.pair.left);
   rx_free_rexp (rx, node->params.pair.right);
   break;
 case r_data:
   break;
 }
      free ((char *)node);
    }
}
static struct rexp_node *
rx_copy_rexp (struct rx *rx,
    struct rexp_node *node)
{
  if (!node)
    return 0;
  else
    {
      struct rexp_node *n = rexp_node (rx, node->type);
      if (!n)
 return 0;
      switch (node->type)
 {
 case r_cset:
   n->params.cset = rx_copy_cset (rx, node->params.cset);
   if (!n->params.cset)
     {
       rx_free_rexp (rx, n);
       return 0;
     }
   break;

 case r_side_effect:
   n->params.side_effect = node->params.side_effect;
   break;

 case r_concat:
 case r_alternate:
 case r_opt:
 case r_2phase_star:
 case r_star:
   n->params.pair.left =
     rx_copy_rexp (rx, node->params.pair.left);
   n->params.pair.right =
     rx_copy_rexp (rx, node->params.pair.right);
   if ( (node->params.pair.left && !n->params.pair.left)
       || (node->params.pair.right && !n->params.pair.right))
     {
       rx_free_rexp (rx, n);
       return 0;
     }
   break;
 case r_data:

   break;
 }
      return n;
    }
}







static struct rx_nfa_state *
rx_nfa_state (struct rx *rx)





{
  struct rx_nfa_state * n = (struct rx_nfa_state *)malloc (sizeof (*n));
  if (!n)
    return 0;
  memset ((n), 0, (sizeof (*n)));
  n->next = rx->nfa_states;
  rx->nfa_states = n;
  return n;
}



static void
rx_free_nfa_state (struct rx_nfa_state * n)





{
  free ((char *)n);
}






static struct rx_nfa_state *
rx_id_to_nfa_state (struct rx * rx,
      int id)






{
  struct rx_nfa_state * n;
  for (n = rx->nfa_states; n; n = n->next)
    if (n->id == id)
      return n;
  return 0;
}







static struct rx_nfa_edge *
rx_nfa_edge (struct rx *rx,
      enum rx_nfa_etype type,
      struct rx_nfa_state *start,
      struct rx_nfa_state *dest)
{
  struct rx_nfa_edge *e;
  e = (struct rx_nfa_edge *)malloc (sizeof (*e));
  if (!e)
    return 0;
  e->next = start->edges;
  start->edges = e;
  e->type = type;
  e->dest = dest;
  return e;
}
static void
rx_free_nfa_edge (struct rx_nfa_edge * e)
{
  free ((char *)e);
}
static struct rx_possible_future *
rx_possible_future (struct rx * rx,
   struct rx_se_list * effects)
{
  struct rx_possible_future *ec;
  ec = (struct rx_possible_future *) malloc (sizeof (*ec));
  if (!ec)
    return 0;
  ec->destset = 0;
  ec->next = 0;
  ec->effects = effects;
  return ec;
}
static void
rx_free_possible_future (struct rx_possible_future * pf)
{
  free ((char *)pf);
}
static void
rx_free_nfa (struct rx *rx)
{
  while (rx->nfa_states)
    {
      while (rx->nfa_states->edges)
 {
   switch (rx->nfa_states->edges->type)
     {
     case ne_cset:
       rx_free_cset (rx, rx->nfa_states->edges->params.cset);
       break;
     default:
       break;
     }
   {
     struct rx_nfa_edge * e;
     e = rx->nfa_states->edges;
     rx->nfa_states->edges = rx->nfa_states->edges->next;
     rx_free_nfa_edge (e);
   }
 }
      {
 struct rx_possible_future * pf = rx->nfa_states->futures;
 while (pf)
   {
     struct rx_possible_future * pft = pf;
     pf = pf->next;
     rx_free_possible_future (pft);
   }
      }
      {
 struct rx_nfa_state *n;
 n = rx->nfa_states;
 rx->nfa_states = rx->nfa_states->next;
 rx_free_nfa_state (n);
      }
    }
}
static int
rx_build_nfa (struct rx *rx,
       struct rexp_node *rexp,
       struct rx_nfa_state **start,
       struct rx_nfa_state **end)
{
  struct rx_nfa_edge *edge;
  *start = *start ? *start : rx_nfa_state (rx);
  if (!*start)
    return 0;
  if (!rexp)
    {
      *end = *start;
      return 1;
    }
  *end = *end ? *end : rx_nfa_state (rx);
  if (!*end)
    {
      rx_free_nfa_state (*start);
      return 0;
    }
  switch (rexp->type)
    {
    case r_data:
      return 0;
    case r_cset:
      edge = rx_nfa_edge (rx, ne_cset, *start, *end);
      if (!edge)
 return 0;
      edge->params.cset = rx_copy_cset (rx, rexp->params.cset);
      if (!edge->params.cset)
 {
   rx_free_nfa_edge (edge);
   return 0;
 }
      return 1;
    case r_opt:
      return (rx_build_nfa (rx, rexp->params.pair.left, start, end)
       && rx_nfa_edge (rx, ne_epsilon, *start, *end));
    case r_star:
      {
 struct rx_nfa_state * star_start = 0;
 struct rx_nfa_state * star_end = 0;
 return (rx_build_nfa (rx, rexp->params.pair.left,
         &star_start, &star_end)
  && star_start
  && star_end
  && rx_nfa_edge (rx, ne_epsilon, star_start, star_end)
  && rx_nfa_edge (rx, ne_epsilon, *start, star_start)
  && rx_nfa_edge (rx, ne_epsilon, star_end, *end)
  && rx_nfa_edge (rx, ne_epsilon, star_end, star_start));
      }
    case r_2phase_star:
      {
 struct rx_nfa_state * star_start = 0;
 struct rx_nfa_state * star_end = 0;
 struct rx_nfa_state * loop_exp_start = 0;
 struct rx_nfa_state * loop_exp_end = 0;
 return (rx_build_nfa (rx, rexp->params.pair.left,
         &star_start, &star_end)
  && rx_build_nfa (rx, rexp->params.pair.right,
     &loop_exp_start, &loop_exp_end)
  && star_start
  && star_end
  && loop_exp_end
  && loop_exp_start
  && rx_nfa_edge (rx, ne_epsilon, star_start, *end)
  && rx_nfa_edge (rx, ne_epsilon, *start, star_start)
  && rx_nfa_edge (rx, ne_epsilon, star_end, *end)
  && rx_nfa_edge (rx, ne_epsilon, star_end, loop_exp_start)
  && rx_nfa_edge (rx, ne_epsilon, loop_exp_end, star_start));
      }
    case r_concat:
      {
 struct rx_nfa_state *shared = 0;
 return
   (rx_build_nfa (rx, rexp->params.pair.left, start, &shared)
    && rx_build_nfa (rx, rexp->params.pair.right, &shared, end));
      }
    case r_alternate:
      {
 struct rx_nfa_state *ls = 0;
 struct rx_nfa_state *le = 0;
 struct rx_nfa_state *rs = 0;
 struct rx_nfa_state *re = 0;
 return (rx_build_nfa (rx, rexp->params.pair.left, &ls, &le)
  && rx_build_nfa (rx, rexp->params.pair.right, &rs, &re)
  && rx_nfa_edge (rx, ne_epsilon, *start, ls)
  && rx_nfa_edge (rx, ne_epsilon, *start, rs)
  && rx_nfa_edge (rx, ne_epsilon, le, *end)
  && rx_nfa_edge (rx, ne_epsilon, re, *end));
      }
    case r_side_effect:
      edge = rx_nfa_edge (rx, ne_side_effect, *start, *end);
      if (!edge)
 return 0;
      edge->params.side_effect = rexp->params.side_effect;
      return 1;
    }
  return 0;
}
static void
rx_name_nfa_states (struct rx *rx)
{
  struct rx_nfa_state *n = rx->nfa_states;
  rx->nodec = 0;
  rx->epsnodec = -1;
  while (n)
    {
      struct rx_nfa_edge *e = n->edges;
      if (n->is_start)
 n->eclosure_needed = 1;
      while (e)
 {
   switch (e->type)
     {
     case ne_epsilon:
     case ne_side_effect:
       break;
     case ne_cset:
       n->id = rx->nodec++;
       {
  struct rx_nfa_edge *from_n = n->edges;
  while (from_n)
    {
      from_n->dest->eclosure_needed = 1;
      from_n = from_n->next;
    }
       }
       goto cont;
     }
   e = e->next;
 }
      n->id = rx->epsnodec--;
    cont:
      n = n->next;
    }
  rx->epsnodec = -rx->epsnodec;
}
static int
se_list_cmp (void * va, void * vb)
{
  struct rx_se_list * a = (struct rx_se_list *)va;
  struct rx_se_list * b = (struct rx_se_list *)vb;
  return ((va == vb)
   ? 0
   : (!va
      ? -1
      : (!vb
  ? 1
  : ((long)a->car < (long)b->car
     ? 1
     : ((long)a->car > (long)b->car
        ? -1
        : se_list_cmp ((void *)a->cdr, (void *)b->cdr))))));
}
static int
se_list_equal (void * va, void * vb)
{
  return !(se_list_cmp (va, vb));
}
static struct rx_hash_rules se_list_hash_rules =
{
  se_list_equal,
  compiler_hash_alloc,
  compiler_free_hash,
  compiler_hash_item_alloc,
  compiler_free_hash_item
};
static struct rx_se_list *
side_effect_cons (struct rx * rx,
    void * se, struct rx_se_list * list)
{
  struct rx_se_list * l;
  l = ((struct rx_se_list *) malloc (sizeof (*l)));
  if (!l)
    return 0;
  l->car = se;
  l->cdr = list;
  return l;
}
static struct rx_se_list *
hash_cons_se_prog (struct rx * rx,
     struct rx_hash * memo,
     void * car, struct rx_se_list * cdr)
{
  long hash = (long)car ^ (long)cdr;
  struct rx_se_list template;
  template.car = car;
  template.cdr = cdr;
  {
    struct rx_hash_item * it = rx_hash_store (memo, hash,
           (void *)&template,
           &se_list_hash_rules);
    if (!it)
      return 0;
    if (it->data == (void *)&template)
      {
 struct rx_se_list * consed;
 consed = (struct rx_se_list *) malloc (sizeof (*consed));
 *consed = template;
 it->data = (void *)consed;
      }
    return (struct rx_se_list *)it->data;
  }
}
static struct rx_se_list *
hash_se_prog (struct rx * rx, struct rx_hash * memo, struct rx_se_list * prog)
{
  struct rx_se_list * answer = 0;
  while (prog)
    {
      answer = hash_cons_se_prog (rx, memo, prog->car, answer);
      if (!answer)
 return 0;
      prog = prog->cdr;
    }
  return answer;
}
static int
nfa_set_cmp (void * va, void * vb)
{
  struct rx_nfa_state_set * a = (struct rx_nfa_state_set *)va;
  struct rx_nfa_state_set * b = (struct rx_nfa_state_set *)vb;
  return ((va == vb)
   ? 0
   : (!va
      ? -1
      : (!vb
  ? 1
  : (a->car->id < b->car->id
     ? 1
     : (a->car->id > b->car->id
        ? -1
        : nfa_set_cmp ((void *)a->cdr, (void *)b->cdr))))));
}
static int
nfa_set_equal (void * va, void * vb)
{
  return !nfa_set_cmp (va, vb);
}
static struct rx_hash_rules nfa_set_hash_rules =
{
  nfa_set_equal,
  compiler_hash_alloc,
  compiler_free_hash,
  compiler_hash_item_alloc,
  compiler_free_hash_item
};
static struct rx_nfa_state_set *
nfa_set_cons (struct rx * rx,
       struct rx_hash * memo, struct rx_nfa_state * state,
       struct rx_nfa_state_set * set)
{
  struct rx_nfa_state_set template;
  struct rx_hash_item * node;
  template.car = state;
  template.cdr = set;
  node = rx_hash_store (memo,
   (((long)state) >> 8) ^ (long)set,
   &template, &nfa_set_hash_rules);
  if (!node)
    return 0;
  if (node->data == &template)
    {
      struct rx_nfa_state_set * l;
      l = (struct rx_nfa_state_set *) malloc (sizeof (*l));
      node->data = (void *) l;
      if (!l)
 return 0;
      *l = template;
    }
  return (struct rx_nfa_state_set *)node->data;
}
static struct rx_nfa_state_set *
nfa_set_enjoin (struct rx * rx,
  struct rx_hash * memo, struct rx_nfa_state * state,
  struct rx_nfa_state_set * set)
{
  if (!set || state->id < set->car->id)
    return nfa_set_cons (rx, memo, state, set);
  if (state->id == set->car->id)
    return set;
  else
    {
      struct rx_nfa_state_set * newcdr
 = nfa_set_enjoin (rx, memo, state, set->cdr);
      if (newcdr != set->cdr)
 set = nfa_set_cons (rx, memo, set->car, newcdr);
      return set;
    }
}
struct eclose_frame
{
  struct rx_se_list *prog_backwards;
};
static int
eclose_node (struct rx *rx, struct rx_nfa_state *outnode,
      struct rx_nfa_state *node, struct eclose_frame *frame)
{
  struct rx_nfa_edge *e = node->edges;
  if (node->mark)
    return 1;
  node->mark = 1;
  if (node->id >= 0 || node->is_final)
    {
      struct rx_possible_future **ec;
      struct rx_se_list * prog_in_order
 = ((struct rx_se_list *)hash_se_prog (rx,
           &rx->se_list_memo,
           frame->prog_backwards));
      int cmp;
      ec = &outnode->futures;
      while (*ec)
 {
   cmp = se_list_cmp ((void *)(*ec)->effects, (void *)prog_in_order);
   if (cmp <= 0)
     break;
   ec = &(*ec)->next;
 }
      if (!*ec || (cmp < 0))
 {
   struct rx_possible_future * saved = *ec;
   *ec = rx_possible_future (rx, prog_in_order);
   (*ec)->next = saved;
   if (!*ec)
     return 0;
 }
      if (node->id >= 0)
 {
   (*ec)->destset = nfa_set_enjoin (rx, &rx->set_list_memo,
        node, (*ec)->destset);
   if (!(*ec)->destset)
     return 0;
 }
    }
  while (e)
    {
      switch (e->type)
 {
 case ne_epsilon:
   if (!eclose_node (rx, outnode, e->dest, frame))
     return 0;
   break;
 case ne_side_effect:
   {
     frame->prog_backwards = side_effect_cons (rx,
            e->params.side_effect,
            frame->prog_backwards);
     if (!frame->prog_backwards)
       return 0;
     if (!eclose_node (rx, outnode, e->dest, frame))
       return 0;
     {
       struct rx_se_list * dying = frame->prog_backwards;
       frame->prog_backwards = frame->prog_backwards->cdr;
       free ((char *)dying);
     }
     break;
   }
 default:
   break;
 }
      e = e->next;
    }
  node->mark = 0;
  return 1;
}
static int
rx_eclose_nfa (struct rx *rx)
{
  struct rx_nfa_state *n = rx->nfa_states;
  struct eclose_frame frame;
  static int rx_id = 0;
  frame.prog_backwards = 0;
  rx->rx_id = rx_id++;
  memset ((&rx->se_list_memo), 0, (sizeof (rx->se_list_memo)));
  memset ((&rx->set_list_memo), 0, (sizeof (rx->set_list_memo)));
  while (n)
    {
      n->futures = 0;
      if (n->eclosure_needed && !eclose_node (rx, n, n, &frame))
 return 0;
      n = n->next;
    }
  return 1;
}
static void
rx_delete_epsilon_transitions (struct rx *rx)
{
  struct rx_nfa_state *n = rx->nfa_states;
  struct rx_nfa_edge **e;
  while (n)
    {
      e = &n->edges;
      while (*e)
 {
   struct rx_nfa_edge *t;
   switch ((*e)->type)
     {
     case ne_epsilon:
     case ne_side_effect:
       t = *e;
       *e = t->next;
       rx_free_nfa_edge (t);
       break;
     default:
       e = &(*e)->next;
       break;
     }
 }
      n = n->next;
    }
}
static int
nfacmp (void * va, void * vb)
{
  struct rx_nfa_state **a = (struct rx_nfa_state **)va;
  struct rx_nfa_state **b = (struct rx_nfa_state **)vb;
  return (*a == *b
   ? 0
   : (((*a)->id < 0) == ((*b)->id < 0)
      ? (((*a)->id < (*b)->id) ? -1 : 1)
      : (((*a)->id < 0)
  ? 1 : -1)));
}
static int
count_hash_nodes (struct rx_hash * st)
{
  int x;
  int count = 0;
  for (x = 0; x < 13; ++x)
    count += ((st->children[x])
       ? count_hash_nodes (st->children[x])
       : st->bucket_size[x]);
  return count;
}
static void
se_memo_freer (struct rx_hash_item * node)
{
  free ((char *)node->data);
}
static void
nfa_set_freer (struct rx_hash_item * node)
{
  free ((char *)node->data);
}
static int
rx_compactify_nfa (struct rx *rx,
     void **mem, unsigned long *size)
{
  int total_nodec;
  struct rx_nfa_state *n;
  int edgec = 0;
  int eclosec = 0;
  int se_list_consc = count_hash_nodes (&rx->se_list_memo);
  int nfa_setc = count_hash_nodes (&rx->set_list_memo);
  unsigned long total_size;
  n = rx->nfa_states;
  total_nodec = 0;
  while (n)
    {
      struct rx_nfa_edge *e = n->edges;
      struct rx_possible_future *ec = n->futures;
      ++total_nodec;
      while (e)
 {
   ++edgec;
   e = e->next;
 }
      while (ec)
 {
   ++eclosec;
   ec = ec->next;
 }
      n = n->next;
    }
  total_size = (total_nodec * sizeof (struct rx_nfa_state)
  + edgec * ((((rx->local_cset_size) + (32) - 1) / (32)) * sizeof(RX_subset))
  + edgec * sizeof (struct rx_nfa_edge)
  + nfa_setc * sizeof (struct rx_nfa_state_set)
  + eclosec * sizeof (struct rx_possible_future)
  + se_list_consc * sizeof (struct rx_se_list)
  + rx->reserved);
  if (total_size > *size)
    {
      *mem = (*mem ? realloc (*mem, total_size) : malloc (total_size));
      if (*mem)
 *size = total_size;
      else
 return 0;
    }
  {
    static struct rx_nfa_state **scratch = 0;
    static int scratch_alloc = 0;
    struct rx_nfa_state *state_base = (struct rx_nfa_state *) * mem;
    struct rx_nfa_state *new_state = state_base;
    struct rx_nfa_edge *new_edge =
      (struct rx_nfa_edge *)
 ((char *) state_base + total_nodec * sizeof (struct rx_nfa_state));
    struct rx_se_list * new_se_list =
      (struct rx_se_list *)
 ((char *)new_edge + edgec * sizeof (struct rx_nfa_edge));
    struct rx_possible_future *new_close =
      ((struct rx_possible_future *)
       ((char *) new_se_list
 + se_list_consc * sizeof (struct rx_se_list)));
    struct rx_nfa_state_set * new_nfa_set =
      ((struct rx_nfa_state_set *)
       ((char *)new_close + eclosec * sizeof (struct rx_possible_future)));
    char *new_bitset =
      ((char *) new_nfa_set + nfa_setc * sizeof (struct rx_nfa_state_set));
    int x;
    struct rx_nfa_state *n;
    if (scratch_alloc < total_nodec)
      {
 scratch = ((struct rx_nfa_state **)
     (scratch ? realloc (scratch, total_nodec * sizeof (*scratch)) : malloc (total_nodec * sizeof (*scratch))));
 if (scratch)
   scratch_alloc = total_nodec;
 else
   {
     scratch_alloc = 0;
     return 0;
   }
      }
    for (x = 0, n = rx->nfa_states; n; n = n->next)
      scratch[x++] = n;
    qsort (scratch, total_nodec,
    sizeof (struct rx_nfa_state *), (int (*)())nfacmp);
    for (x = 0; x < total_nodec; ++x)
      {
 struct rx_possible_future *eclose = scratch[x]->futures;
 struct rx_nfa_edge *edge = scratch[x]->edges;
 struct rx_nfa_state *cn = new_state++;
 cn->futures = 0;
 cn->edges = 0;
 cn->next = (x == total_nodec - 1) ? 0 : (cn + 1);
 cn->id = scratch[x]->id;
 cn->is_final = scratch[x]->is_final;
 cn->is_start = scratch[x]->is_start;
 cn->mark = 0;
 while (edge)
   {
     int indx = (edge->dest->id < 0
    ? (total_nodec + edge->dest->id)
    : edge->dest->id);
     struct rx_nfa_edge *e = new_edge++;
     rx_Bitset cset = (rx_Bitset) new_bitset;
     new_bitset += ((((rx->local_cset_size) + (32) - 1) / (32)) * sizeof(RX_subset));
     rx_bitset_null (rx->local_cset_size, cset);
     rx_bitset_union (rx->local_cset_size, cset, edge->params.cset);
     e->next = cn->edges;
     cn->edges = e;
     e->type = edge->type;
     e->dest = state_base + indx;
     e->params.cset = cset;
     edge = edge->next;
   }
 while (eclose)
   {
     struct rx_possible_future *ec = new_close++;
     struct rx_hash_item * sp;
     struct rx_se_list ** sepos;
     struct rx_se_list * sesrc;
     struct rx_nfa_state_set * destlst;
     struct rx_nfa_state_set ** destpos;
     ec->next = cn->futures;
     cn->futures = ec;
     for (sepos = &ec->effects, sesrc = eclose->effects;
   sesrc;
   sesrc = sesrc->cdr, sepos = &(*sepos)->cdr)
       {
  sp = rx_hash_find (&rx->se_list_memo,
       (long)sesrc->car ^ (long)sesrc->cdr,
       sesrc, &se_list_hash_rules);
  if (sp->binding)
    {
      sesrc = (struct rx_se_list *)sp->binding;
      break;
    }
  *new_se_list = *sesrc;
  sp->binding = (void *)new_se_list;
  *sepos = new_se_list;
  ++new_se_list;
       }
     *sepos = sesrc;
     for (destpos = &ec->destset, destlst = eclose->destset;
   destlst;
   destpos = &(*destpos)->cdr, destlst = destlst->cdr)
       {
  sp = rx_hash_find (&rx->set_list_memo,
       ((((long)destlst->car) >> 8)
        ^ (long)destlst->cdr),
       destlst, &nfa_set_hash_rules);
  if (sp->binding)
    {
      destlst = (struct rx_nfa_state_set *)sp->binding;
      break;
    }
  *new_nfa_set = *destlst;
  new_nfa_set->car = state_base + destlst->car->id;
  sp->binding = (void *)new_nfa_set;
  *destpos = new_nfa_set;
  ++new_nfa_set;
       }
     *destpos = destlst;
     eclose = eclose->next;
   }
      }
  }
  rx_free_hash_table (&rx->se_list_memo, se_memo_freer, &se_list_hash_rules);
  memset ((&rx->se_list_memo), 0, (sizeof (rx->se_list_memo)));
  rx_free_hash_table (&rx->set_list_memo, nfa_set_freer, &nfa_set_hash_rules);
  memset ((&rx->set_list_memo), 0, (sizeof (rx->set_list_memo)));
  rx_free_nfa (rx);
  rx->nfa_states = (struct rx_nfa_state *)*mem;
  return 1;
}
void * rx_id_instruction_table[rx_num_instructions] =
{
  (void *) rx_backtrack_point,
  (void *) rx_do_side_effects,
  (void *) rx_cache_miss,
  (void *) rx_next_char,
  (void *) rx_backtrack,
  (void *) rx_error_inx
};
static void
rx_morecore (struct rx_cache * cache);
static char *
rx_cache_malloc (struct rx_cache * cache, int bytes)
{
  while (cache->bytes_left < bytes)
    {
      if (cache->memory_pos)
 cache->memory_pos = cache->memory_pos->next;
      if (!cache->memory_pos)
 {
                                  rx_morecore((struct rx_cache *) cache);
   if (!cache->memory_pos)
     return 0;
 }
      cache->bytes_left = cache->memory_pos->bytes;
      cache->memory_addr = ((char *)cache->memory_pos
       + sizeof (struct rx_blocklist));
    }
  cache->bytes_left -= bytes;
  {
    char * addr = cache->memory_addr;
    cache->memory_addr += bytes;
    return addr;
  }
}
static void
rx_cache_free (struct rx_cache * cache,
        struct rx_freelist ** freelist, char * mem)
{
  struct rx_freelist * it = (struct rx_freelist *)mem;
  it->next = *freelist;
  *freelist = it;
}
static void
install_transition (struct rx_superstate *super,
      struct rx_inx *answer, rx_Bitset trcset)
{
  struct rx_inx * transitions = super->transitions;
  int chr;
  for (chr = 0; chr < 256; )
    if (!*trcset)
      {
 ++trcset;
 chr += 32;
      }
    else
      {
 RX_subset sub = *trcset;
 RX_subset mask = 1;
 int bound = chr + 32;
 while (chr < bound)
   {
     if (sub & mask)
       transitions [chr] = *answer;
     ++chr;
     mask <<= 1;
   }
 ++trcset;
      }
}
static int
qlen (q)
     struct rx_superstate * q;
{
  int count = 1;
  struct rx_superstate * it;
  if (!q)
    return 0;
  for (it = q->next_recyclable; it != q; it = it->next_recyclable)
    ++count;
  return count;
}
static void
check_cache (cache)
     struct rx_cache * cache;
{
  struct rx_cache * you_fucked_up = 0;
  int total = cache->superstates;
  int semi = cache->semifree_superstates;
  if (semi != qlen (cache->semifree_superstate))
    check_cache (you_fucked_up);
  if ((total - semi) != qlen (cache->lru_superstate))
    check_cache (you_fucked_up);
}
static void
semifree_superstate (struct rx_cache * cache)
{
  int disqualified = cache->semifree_superstates;
  if (disqualified == cache->superstates)
    return;
  while (cache->lru_superstate->locks)
    {
      cache->lru_superstate = cache->lru_superstate->next_recyclable;
      ++disqualified;
      if (disqualified == cache->superstates)
 return;
    }
  {
    struct rx_superstate * it = cache->lru_superstate;
    it->next_recyclable->prev_recyclable = it->prev_recyclable;
    it->prev_recyclable->next_recyclable = it->next_recyclable;
    cache->lru_superstate = (it == it->next_recyclable
        ? 0
        : it->next_recyclable);
    if (!cache->semifree_superstate)
      {
 cache->semifree_superstate = it;
 it->next_recyclable = it;
 it->prev_recyclable = it;
      }
    else
      {
 it->prev_recyclable = cache->semifree_superstate->prev_recyclable;
 it->next_recyclable = cache->semifree_superstate;
 it->prev_recyclable->next_recyclable = it;
 it->next_recyclable->prev_recyclable = it;
      }
    {
      struct rx_distinct_future *df;
      it->is_semifree = 1;
      ++cache->semifree_superstates;
      df = it->transition_refs;
      if (df)
 {
   df->prev_same_dest->next_same_dest = 0;
   for (df = it->transition_refs; df; df = df->next_same_dest)
     {
       df->future_frame.inx = cache->instruction_table[rx_cache_miss];
       df->future_frame.data = 0;
       df->future_frame.data_2 = (void *) df;
       if (!df->effects
    && (df->edge->options->next_same_super_edge[0]
        == df->edge->options))
  install_transition (df->present, &df->future_frame,
        df->edge->cset);
     }
   df = it->transition_refs;
   df->prev_same_dest->next_same_dest = df;
 }
    }
  }
}
static void
refresh_semifree_superstate (struct rx_cache * cache,
        struct rx_superstate * super)
{
  struct rx_distinct_future *df;
  if (super->transition_refs)
    {
      super->transition_refs->prev_same_dest->next_same_dest = 0;
      for (df = super->transition_refs; df; df = df->next_same_dest)
 {
   df->future_frame.inx = cache->instruction_table[rx_next_char];
   df->future_frame.data = (void *) super->transitions;
   if (!df->effects
       && (df->edge->options->next_same_super_edge[0]
    == df->edge->options))
     install_transition (df->present, &df->future_frame,
    df->edge->cset);
 }
      super->transition_refs->prev_same_dest->next_same_dest
 = super->transition_refs;
    }
  if (cache->semifree_superstate == super)
    cache->semifree_superstate = (super->prev_recyclable == super
      ? 0
      : super->prev_recyclable);
  super->next_recyclable->prev_recyclable = super->prev_recyclable;
  super->prev_recyclable->next_recyclable = super->next_recyclable;
  if (!cache->lru_superstate)
    (cache->lru_superstate
     = super->next_recyclable
     = super->prev_recyclable
     = super);
  else
    {
      super->next_recyclable = cache->lru_superstate;
      super->prev_recyclable = cache->lru_superstate->prev_recyclable;
      super->next_recyclable->prev_recyclable = super;
      super->prev_recyclable->next_recyclable = super;
    }
  super->is_semifree = 0;
  --cache->semifree_superstates;
}
static void
rx_refresh_this_superstate (struct rx_cache * cache, struct rx_superstate * superstate)
{
  if (superstate->is_semifree)
    refresh_semifree_superstate (cache, superstate);
  else if (cache->lru_superstate == superstate)
    cache->lru_superstate = superstate->next_recyclable;
  else if (superstate != cache->lru_superstate->prev_recyclable)
    {
      superstate->next_recyclable->prev_recyclable
 = superstate->prev_recyclable;
      superstate->prev_recyclable->next_recyclable
 = superstate->next_recyclable;
      superstate->next_recyclable = cache->lru_superstate;
      superstate->prev_recyclable = cache->lru_superstate->prev_recyclable;
      superstate->next_recyclable->prev_recyclable = superstate;
      superstate->prev_recyclable->next_recyclable = superstate;
    }
}
static void
release_superset_low (struct rx_cache * cache,
       struct rx_superset *set)
{
  if (!--set->refs)
    {
      if (set->cdr)
 release_superset_low (cache, set->cdr);
      set->starts_for = 0;
      rx_hash_free
 (rx_hash_find
  (&cache->superset_table,
   (unsigned long)set->car ^ set->id ^ (unsigned long)set->cdr,
   (void *)set,
   &cache->superset_hash_rules),
  &cache->superset_hash_rules);
      rx_cache_free (cache, &cache->free_supersets, (char *)set);
    }
}
static void
rx_release_superset (struct rx *rx,
       struct rx_superset *set)
{
  release_superset_low (rx->cache, set);
}
static int
rx_really_free_superstate (struct rx_cache * cache)
{
  int locked_superstates = 0;
  struct rx_superstate * it;
  if (!cache->superstates)
    return 0;
  {
    while ((cache->hits + cache->misses) > cache->superstates_allowed)
      {
 cache->hits >>= 1;
 cache->misses >>= 1;
      }
    if ( ((cache->hits + cache->misses) * cache->semifree_superstates)
 < (cache->superstates * cache->misses))
      {
 semifree_superstate (cache);
 semifree_superstate (cache);
      }
  }
  while (cache->semifree_superstate && cache->semifree_superstate->locks)
    {
      refresh_semifree_superstate (cache, cache->semifree_superstate);
      ++locked_superstates;
      if (locked_superstates == cache->superstates)
 return 0;
    }
  if (cache->semifree_superstate)
    {
      it = cache->semifree_superstate;
      it->next_recyclable->prev_recyclable = it->prev_recyclable;
      it->prev_recyclable->next_recyclable = it->next_recyclable;
      cache->semifree_superstate = ((it == it->next_recyclable)
        ? 0
        : it->next_recyclable);
      --cache->semifree_superstates;
    }
  else
    {
      while (cache->lru_superstate->locks)
 {
   cache->lru_superstate = cache->lru_superstate->next_recyclable;
   ++locked_superstates;
   if (locked_superstates == cache->superstates)
     return 0;
 }
      it = cache->lru_superstate;
      it->next_recyclable->prev_recyclable = it->prev_recyclable;
      it->prev_recyclable->next_recyclable = it->next_recyclable;
      cache->lru_superstate = ((it == it->next_recyclable)
        ? 0
        : it->next_recyclable);
    }
  if (it->transition_refs)
    {
      struct rx_distinct_future *df;
      for (df = it->transition_refs,
    df->prev_same_dest->next_same_dest = 0;
    df;
    df = df->next_same_dest)
 {
   df->future_frame.inx = cache->instruction_table[rx_cache_miss];
   df->future_frame.data = 0;
   df->future_frame.data_2 = (void *) df;
   df->future = 0;
 }
      it->transition_refs->prev_same_dest->next_same_dest =
 it->transition_refs;
    }
  {
    struct rx_super_edge *tc = it->edges;
    while (tc)
      {
 struct rx_distinct_future * df;
 struct rx_super_edge *tct = tc->next;
 df = tc->options;
 df->next_same_super_edge[1]->next_same_super_edge[0] = 0;
 while (df)
   {
     struct rx_distinct_future *dft = df;
     df = df->next_same_super_edge[0];
     if (dft->future && dft->future->transition_refs == dft)
       {
  dft->future->transition_refs = dft->next_same_dest;
  if (dft->future->transition_refs == dft)
    dft->future->transition_refs = 0;
       }
     dft->next_same_dest->prev_same_dest = dft->prev_same_dest;
     dft->prev_same_dest->next_same_dest = dft->next_same_dest;
     rx_cache_free (cache, &cache->free_discernable_futures,
      (char *)dft);
   }
 rx_cache_free (cache, &cache->free_transition_classes, (char *)tc);
 tc = tct;
      }
  }
  if (it->contents->superstate == it)
    it->contents->superstate = 0;
  release_superset_low (cache, it->contents);
  rx_cache_free (cache, &cache->free_superstates, (char *)it);
  --cache->superstates;
  return 1;
}
static char *
rx_cache_get (struct rx_cache * cache,
       struct rx_freelist ** freelist)
{
  while (!*freelist && rx_really_free_superstate (cache))
    ;
  if (!*freelist)
    return 0;
  {
    struct rx_freelist * it = *freelist;
    *freelist = it->next;
    return (char *)it;
  }
}
static char *
rx_cache_malloc_or_get (struct rx_cache * cache,
   struct rx_freelist ** freelist, int bytes)
{
  if (!*freelist)
    {
      char * answer = rx_cache_malloc (cache, bytes);
      if (answer)
 return answer;
    }
  return rx_cache_get (cache, freelist);
}
static char *
rx_cache_get_superstate (struct rx_cache * cache)
{
  char * answer;
  int bytes = ( sizeof (struct rx_superstate)
        + cache->local_cset_size * sizeof (struct rx_inx));
  if (!cache->free_superstates
      && (cache->superstates < cache->superstates_allowed))
    {
      answer = rx_cache_malloc (cache, bytes);
      if (answer)
 {
   ++cache->superstates;
   return answer;
 }
    }
  answer = rx_cache_get (cache, &cache->free_superstates);
  if (!answer)
    {
      answer = rx_cache_malloc (cache, bytes);
      if (answer)
 ++cache->superstates_allowed;
    }
  ++cache->superstates;
  return answer;
}
static int
supersetcmp (va, vb)
     void * va;
     void * vb;
{
  struct rx_superset * a = (struct rx_superset *)va;
  struct rx_superset * b = (struct rx_superset *)vb;
  return ( (a == b)
   || (a && b && (a->car == b->car) && (a->cdr == b->cdr)));
}
static struct rx_hash_item *
superset_allocator (struct rx_hash_rules * rules, void * val)
{
  struct rx_cache * cache
    = ((struct rx_cache *)
       ((char *)rules
 - (unsigned long)(&((struct rx_cache *)0)->superset_hash_rules)));
  struct rx_superset * template = (struct rx_superset *)val;
  struct rx_superset * newset
    = ((struct rx_superset *)
       rx_cache_malloc_or_get (cache,
          &cache->free_supersets,
          sizeof (*template)));
  if (!newset)
    return 0;
  newset->refs = 0;
  newset->car = template->car;
  newset->id = template->car->id;
  newset->cdr = template->cdr;
  newset->superstate = 0;
  (++(template->cdr)->refs);
  newset->hash_item.data = (void *)newset;
  newset->hash_item.binding = 0;
  return &newset->hash_item;
}
static struct rx_hash *
super_hash_allocator (struct rx_hash_rules * rules)
{
  struct rx_cache * cache
    = ((struct rx_cache *)
       ((char *)rules
 - (unsigned long)(&((struct rx_cache *)0)->superset_hash_rules)));
  return ((struct rx_hash *)
   rx_cache_malloc_or_get (cache,
      &cache->free_hash, sizeof (struct rx_hash)));
}
static void
super_hash_liberator (struct rx_hash * hash, struct rx_hash_rules * rules)
{
  struct rx_cache * cache
    = ((struct rx_cache *)
       (char *)rules - (long)(&((struct rx_cache *)0)->superset_hash_rules));
  rx_cache_free (cache, &cache->free_hash, (char *)hash);
}
static void
superset_hash_item_liberator (struct rx_hash_item * it,
         struct rx_hash_rules * rules)
{
}
int rx_cache_bound = 128;
static int rx_default_cache_got = 0;
static int
bytes_for_cache_size (int supers, int cset_size)
{
  return (int)
    ((float)supers *
     ( (1.03 * (float) ( ((((cset_size) + (32) - 1) / (32)) * sizeof(RX_subset))
    + sizeof (struct rx_super_edge)))
      + (1.80 * (float) sizeof (struct rx_possible_future))
      + (float) ( sizeof (struct rx_superstate)
   + cset_size * sizeof (struct rx_inx))));
}
static void
rx_morecore (struct rx_cache * cache)
{
  if (rx_default_cache_got >= rx_cache_bound)
    return;
  rx_default_cache_got += 16;
  cache->superstates_allowed = rx_cache_bound;
  {
    struct rx_blocklist ** pos = &cache->memory;
    int size = bytes_for_cache_size (16, cache->local_cset_size);
    while (*pos)
      pos = &(*pos)->next;
    *pos = ((struct rx_blocklist *)
     malloc (size + sizeof (struct rx_blocklist)));
    if (!*pos)
      return;
    (*pos)->next = 0;
    (*pos)->bytes = size;
    cache->memory_pos = *pos;
    cache->memory_addr = (char *)*pos + sizeof (**pos);
    cache->bytes_left = size;
  }
}
static struct rx_cache default_cache =
{
  {
    supersetcmp,
    super_hash_allocator,
    super_hash_liberator,
    superset_allocator,
    superset_hash_item_liberator,
  },
  0,
  0,
  0,
  0,
  rx_morecore,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  128,
  256,
  rx_id_instruction_table,
  {
    0,
    0,
    {0},
    {0},
    {0}
  }
};
static struct rx_superset *
rx_superset_cons (struct rx * rx,
    struct rx_nfa_state *car, struct rx_superset *cdr)
{
  struct rx_cache * cache = rx->cache;
  if (!car && !cdr)
    {
      if (!cache->empty_superset)
 {
   cache->empty_superset
     = ((struct rx_superset *)
        rx_cache_malloc_or_get (cache, &cache->free_supersets,
           sizeof (struct rx_superset)));
   if (!cache->empty_superset)
     return 0;
   memset ((cache->empty_superset), 0, (sizeof (struct rx_superset)));
   cache->empty_superset->refs = 1000;
 }
      return cache->empty_superset;
    }
  {
    struct rx_superset template;
    struct rx_hash_item * hit;
    template.car = car;
    template.cdr = cdr;
    template.id = car->id;
    hit = rx_hash_store (&cache->superset_table,
    (unsigned long)car ^ car->id ^ (unsigned long)cdr,
    (void *)&template,
    &cache->superset_hash_rules);
    return (hit
     ? (struct rx_superset *)hit->data
     : 0);
  }
}
static struct rx_superset *
rx_superstate_eclosure_union
  (struct rx * rx, struct rx_superset *set, struct rx_nfa_state_set *ecl)
{
  if (!ecl)
    return set;
  if (!set->car)
    return rx_superset_cons (rx, ecl->car,
        rx_superstate_eclosure_union (rx, set, ecl->cdr));
  if (set->car == ecl->car)
    return rx_superstate_eclosure_union (rx, set, ecl->cdr);
  {
    struct rx_superset * tail;
    struct rx_nfa_state * first;
    if (set->car > ecl->car)
      {
 tail = rx_superstate_eclosure_union (rx, set->cdr, ecl);
 first = set->car;
      }
    else
      {
 tail = rx_superstate_eclosure_union (rx, set, ecl->cdr);
 first = ecl->car;
      }
    if (!tail)
      return 0;
    else
      {
 struct rx_superset * answer;
 answer = rx_superset_cons (rx, first, tail);
 if (!answer)
   {
     (++(tail)->refs);
     rx_release_superset (rx, tail);
   }
 return answer;
      }
  }
}
static struct rx_distinct_future *
include_futures (struct rx *rx,
   struct rx_distinct_future *df, struct rx_nfa_state
   *state, struct rx_superstate *superstate)
{
  struct rx_possible_future *future;
  struct rx_cache * cache = rx->cache;
  for (future = state->futures; future; future = future->next)
    {
      struct rx_distinct_future *dfp;
      struct rx_distinct_future *insert_before = 0;
      if (df)
 df->next_same_super_edge[1]->next_same_super_edge[0] = 0;
      for (dfp = df; dfp; dfp = dfp->next_same_super_edge[0])
 if (dfp->effects == future->effects)
   break;
 else
   {
     int order = rx->se_list_cmp (rx, dfp->effects, future->effects);
     if (order > 0)
       {
  insert_before = dfp;
  dfp = 0;
  break;
       }
   }
      if (df)
 df->next_same_super_edge[1]->next_same_super_edge[0] = df;
      if (!dfp)
 {
   dfp
     = ((struct rx_distinct_future *)
        rx_cache_malloc_or_get (cache, &cache->free_discernable_futures,
           sizeof (struct rx_distinct_future)));
   if (!dfp)
     return 0;
   if (!df)
     {
       df = insert_before = dfp;
       df->next_same_super_edge[0] = df->next_same_super_edge[1] = df;
     }
   else if (!insert_before)
     insert_before = df;
   else if (insert_before == df)
     df = dfp;
   dfp->next_same_super_edge[0] = insert_before;
   dfp->next_same_super_edge[1]
     = insert_before->next_same_super_edge[1];
   dfp->next_same_super_edge[1]->next_same_super_edge[0] = dfp;
   dfp->next_same_super_edge[0]->next_same_super_edge[1] = dfp;
   dfp->next_same_dest = dfp->prev_same_dest = dfp;
   dfp->future = 0;
   dfp->present = superstate;
   dfp->future_frame.inx = rx->instruction_table[rx_cache_miss];
   dfp->future_frame.data = 0;
   dfp->future_frame.data_2 = (void *) dfp;
   dfp->side_effects_frame.inx
     = rx->instruction_table[rx_do_side_effects];
   dfp->side_effects_frame.data = 0;
   dfp->side_effects_frame.data_2 = (void *) dfp;
   dfp->effects = future->effects;
 }
    }
  return df;
}
static struct rx_superstate *
rx_superstate (struct rx *rx,
        struct rx_superset *set)
{
  struct rx_cache * cache = rx->cache;
  struct rx_superstate * superstate = 0;
  if (set->superstate)
    {
      if (set->superstate->rx_id != rx->rx_id)
 {
   superstate = set->superstate;
   if (!superstate->is_semifree)
     {
       if (cache->lru_superstate == superstate)
  {
    cache->lru_superstate = superstate->next_recyclable;
    if (cache->lru_superstate == superstate)
      cache->lru_superstate = 0;
  }
       {
  superstate->next_recyclable->prev_recyclable
    = superstate->prev_recyclable;
  superstate->prev_recyclable->next_recyclable
    = superstate->next_recyclable;
  if (!cache->semifree_superstate)
    {
      (cache->semifree_superstate
       = superstate->next_recyclable
       = superstate->prev_recyclable
       = superstate);
    }
  else
    {
      superstate->next_recyclable = cache->semifree_superstate;
      superstate->prev_recyclable
        = cache->semifree_superstate->prev_recyclable;
      superstate->next_recyclable->prev_recyclable
        = superstate;
      superstate->prev_recyclable->next_recyclable
        = superstate;
      cache->semifree_superstate = superstate;
    }
  ++cache->semifree_superstates;
       }
     }
   set->superstate = 0;
   goto handle_cache_miss;
 }
      ++cache->hits;
      superstate = set->superstate;
      rx_refresh_this_superstate (cache, superstate);
      return superstate;
    }
 handle_cache_miss:
  ++cache->misses;
  superstate = (struct rx_superstate *)rx_cache_get_superstate (cache);
  if (!superstate)
    return 0;
  if (!cache->lru_superstate)
    (cache->lru_superstate
     = superstate->next_recyclable
     = superstate->prev_recyclable
     = superstate);
  else
    {
      superstate->next_recyclable = cache->lru_superstate;
      superstate->prev_recyclable = cache->lru_superstate->prev_recyclable;
      ( superstate->prev_recyclable->next_recyclable
       = superstate->next_recyclable->prev_recyclable
       = superstate);
    }
  superstate->rx_id = rx->rx_id;
  superstate->transition_refs = 0;
  superstate->locks = 0;
  superstate->is_semifree = 0;
  set->superstate = superstate;
  superstate->contents = set;
  (++(set)->refs);
  superstate->edges = 0;
  {
    int x;
    for (x = 0; x < rx->local_cset_size; ++x)
      {
 struct rx_inx * ifr = &superstate->transitions[x];
 ifr->inx = rx->instruction_table [rx_cache_miss];
 ifr->data = ifr->data_2 = 0;
      }
  }
  return superstate;
}
static int
solve_destination (struct rx *rx, struct rx_distinct_future *df)
{
  struct rx_super_edge *tc = df->edge;
  struct rx_superset *nfa_state;
  struct rx_superset *nil_set = rx_superset_cons (rx, 0, 0);
  struct rx_superset *solution = nil_set;
  struct rx_superstate *dest;
  (++(solution)->refs);
  for (nfa_state = df->present->contents;
       nfa_state->car;
       nfa_state = nfa_state->cdr)
    {
      struct rx_nfa_edge *e;
      for (e = nfa_state->car->edges; e; e = e->next)
 if (rx_bitset_is_subset (rx->local_cset_size,
     tc->cset, e->params.cset))
   {
     struct rx_nfa_state *n = e->dest;
     struct rx_possible_future *pf;
     for (pf = n->futures; pf; pf = pf->next)
       if (pf->effects == df->effects)
  {
    struct rx_superset * old_sol;
    old_sol = solution;
    solution = rx_superstate_eclosure_union (rx, solution,
          pf->destset);
    if (!solution)
      return 0;
    (++(solution)->refs);
    rx_release_superset (rx, old_sol);
  }
   }
    }
  if (solution == nil_set)
    {
      df->future_frame.inx = (void *) rx_backtrack;
      df->future_frame.data = 0;
      df->future_frame.data_2 = 0;
      return 1;
    }
  dest = rx_superstate (rx, solution);
  rx_release_superset (rx, solution);
  if (!dest)
    return 0;
  {
    struct rx_distinct_future *dft;
    dft = df;
    df->prev_same_dest->next_same_dest = 0;
    while (dft)
      {
 dft->future = dest;
 dft->future_frame.inx = rx->instruction_table[rx_next_char];
 dft->future_frame.data = (void *) dest->transitions;
 dft = dft->next_same_dest;
      }
    df->prev_same_dest->next_same_dest = df;
  }
  if (!dest->transition_refs)
    dest->transition_refs = df;
  else
    {
      struct rx_distinct_future *dft = dest->transition_refs->next_same_dest;
      dest->transition_refs->next_same_dest = df->next_same_dest;
      df->next_same_dest->prev_same_dest = dest->transition_refs;
      df->next_same_dest = dft;
      dft->prev_same_dest = df;
    }
  return 1;
}
static int
compute_super_edge (struct rx *rx, struct rx_distinct_future **dfout,
     rx_Bitset csetout, struct rx_superstate *superstate,
     unsigned char chr)
{
  struct rx_superset *stateset = superstate->contents;
  rx_bitset_universe (rx->local_cset_size, csetout);
  *dfout = 0;
  while (stateset->car)
    {
      struct rx_nfa_edge *e;
      for (e = stateset->car->edges; e; e = e->next)
 if (((e->params.cset)[((chr) / (32))] & rx_subset_singletons[(chr) & ((32) - 1)]))
   {
     {
       struct rx_distinct_future * saved;
       saved = *dfout;
       *dfout = include_futures (rx, *dfout, e->dest, superstate);
       if (!*dfout)
  {
    struct rx_distinct_future * df;
    df = saved;
    df->next_same_super_edge[1]->next_same_super_edge[0] = 0;
    while (df)
      {
        struct rx_distinct_future *dft;
        dft = df;
        df = df->next_same_super_edge[0];
        if (dft->future && dft->future->transition_refs == dft)
   {
     dft->future->transition_refs = dft->next_same_dest;
     if (dft->future->transition_refs == dft)
       dft->future->transition_refs = 0;
   }
        dft->next_same_dest->prev_same_dest = dft->prev_same_dest;
        dft->prev_same_dest->next_same_dest = dft->next_same_dest;
        rx_cache_free (rx->cache,
         &rx->cache->free_discernable_futures,
         (char *)dft);
      }
    return 0;
  }
     }
     rx_bitset_intersection (rx->local_cset_size,
        csetout, e->params.cset);
   }
 else
   rx_bitset_difference (rx->local_cset_size, csetout, e->params.cset);
      stateset = stateset->cdr;
    }
  return 1;
}
static struct rx_super_edge *
rx_super_edge (struct rx *rx,
        struct rx_superstate *super, rx_Bitset cset,
        struct rx_distinct_future *df)
{
  struct rx_super_edge *tc =
    (struct rx_super_edge *)rx_cache_malloc_or_get
      (rx->cache, &rx->cache->free_transition_classes,
       sizeof (struct rx_super_edge) + ((((rx->local_cset_size) + (32) - 1) / (32)) * sizeof(RX_subset)));
  if (!tc)
    return 0;
  tc->next = super->edges;
  super->edges = tc;
  tc->rx_backtrack_frame.inx = rx->instruction_table[rx_backtrack_point];
  tc->rx_backtrack_frame.data = 0;
  tc->rx_backtrack_frame.data_2 = (void *) tc;
  tc->options = df;
  tc->cset = (rx_Bitset) ((char *) tc + sizeof (*tc));
  rx_bitset_assign (rx->local_cset_size, tc->cset, cset);
  if (df)
    {
      struct rx_distinct_future * dfp = df;
      df->next_same_super_edge[1]->next_same_super_edge[0] = 0;
      while (dfp)
 {
   dfp->edge = tc;
   dfp = dfp->next_same_super_edge[0];
 }
      df->next_same_super_edge[1]->next_same_super_edge[0] = df;
    }
  return tc;
}
static void
install_partial_transition (struct rx_superstate *super,
        struct rx_inx *answer,
        RX_subset set, int offset)
{
  int start = offset;
  int end = start + 32;
  RX_subset pos = 1;
  struct rx_inx * transitions = super->transitions;
  while (start < end)
    {
      if (set & pos)
 transitions[start] = *answer;
      pos <<= 1;
      ++start;
    }
}
static struct rx_inx *
rx_handle_cache_miss
  (struct rx *rx, struct rx_superstate *super, unsigned char chr, void *data)
{
  int offset = chr / (32);
  struct rx_distinct_future *df = data;
  if (!df)
    {
      struct rx_super_edge *tc;
      RX_subset mask = rx_subset_singletons [chr % (32)];
      for (tc = super->edges; tc; tc = tc->next)
 if (tc->cset[offset] & mask)
   {
     struct rx_inx * answer;
     df = tc->options;
     answer = ((tc->options->next_same_super_edge[0] != tc->options)
        ? &tc->rx_backtrack_frame
        : (df->effects
    ? &df->side_effects_frame
    : &df->future_frame));
     install_partial_transition (super, answer,
     tc->cset [offset], offset * 32);
     return answer;
   }
      {
 char cset_space[1024];
 rx_Bitset trcset;
 struct rx_inx *answer;
 if (((((rx->local_cset_size) + (32) - 1) / (32)) * sizeof(RX_subset)) > sizeof (cset_space))
   return 0;
 trcset = (rx_Bitset)cset_space;
 ((super)->locks++);
 if (!compute_super_edge (rx, &df, trcset, super, chr))
   {
     (--(super)->locks);
     return 0;
   }
 if (!df)
   {
     static struct rx_inx
       shared_fail_frame = { (void *)rx_backtrack, 0, 0 };
     answer = &shared_fail_frame;
   }
 else
   {
     tc = rx_super_edge (rx, super, trcset, df);
     if (!tc)
       {
  (--(super)->locks);
  return 0;
       }
     answer = ((tc->options->next_same_super_edge[0] != tc->options)
        ? &tc->rx_backtrack_frame
        : (df->effects
    ? &df->side_effects_frame
    : &df->future_frame));
   }
 install_partial_transition (super, answer,
        trcset[offset], offset * 32);
 (--(super)->locks);
 return answer;
      }
    }
  else if (df->future)
    {
      if (df->future->is_semifree)
 refresh_semifree_superstate (rx->cache, df->future);
      return &df->future_frame;
    }
  else
    {
      ((super)->locks++);
      if (!solve_destination (rx, df))
 {
   (--(super)->locks);
   return 0;
 }
      if (!df->effects
   && (df->edge->options->next_same_super_edge[0] == df->edge->options))
 install_partial_transition (super, &df->future_frame,
        df->edge->cset[offset], offset * 32);
      (--(super)->locks);
      return &df->future_frame;
    }
}
const char *re_error_msg[] =
{
  0,
  "No match",
  "Invalid regular expression",
  "Invalid collation character",
  "Invalid character class name",
  "Trailing backslash",
  "Invalid back reference",
  "Unmatched [ or [^",
  "Unmatched ( or \\(",
  "Unmatched \\{",
  "Invalid content of \\{\\}",
  "Invalid range end",
  "Memory exhausted",
  "Invalid preceding regular expression",
  "Premature end of regular expression",
  "Regular expression too big",
  "Unmatched ) or \\)",
};
typedef unsigned regnum_t;
typedef int pattern_offset_t;
typedef struct
{
  struct rexp_node ** top_expression;
  struct rexp_node ** last_expression;
  pattern_offset_t inner_group_offset;
  regnum_t regnum;
} compile_stack_elt_t;
typedef struct
{
  compile_stack_elt_t *stack;
  unsigned size;
  unsigned avail;
} compile_stack_type;
static boolean
at_begline_loc_p (const char *pattern, const char * p, reg_syntax_t syntax)
{
  const char *prev = p - 2;
  boolean prev_prev_backslash = ((prev > pattern) && (prev[-1] == '\\'));
    return
      (
       ((*prev == '(') && ((syntax & ((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)) || prev_prev_backslash))
       ||
       ((*prev == '|') && ((syntax & ((((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)) || prev_prev_backslash))
       );
}
static boolean
at_endline_loc_p (const char *p, const char *pend, int syntax)
{
  const char *next = p;
  boolean next_backslash = (*next == '\\');
  const char *next_next = (p + 1 < pend) ? (p + 1) : 0;
  return
    (
     ((syntax & ((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
      ? (*next == ')')
      : (next_backslash && next_next && (*next_next == ')')))
    ||
     ((syntax & ((((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
      ? (*next == '|')
      : (next_backslash && next_next && (*next_next == '|')))
     );
}
static unsigned char id_translation[256] =
{
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
 60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
 80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
 100, 101, 102, 103, 104, 105, 106, 107, 108, 109,
 110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
 120, 121, 122, 123, 124, 125, 126, 127, 128, 129,
 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
 140, 141, 142, 143, 144, 145, 146, 147, 148, 149,
 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
 160, 161, 162, 163, 164, 165, 166, 167, 168, 169,
 170, 171, 172, 173, 174, 175, 176, 177, 178, 179,
 180, 181, 182, 183, 184, 185, 186, 187, 188, 189,
 190, 191, 192, 193, 194, 195, 196, 197, 198, 199,
 200, 201, 202, 203, 204, 205, 206, 207, 208, 209,
 210, 211, 212, 213, 214, 215, 216, 217, 218, 219,
 220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
 230, 231, 232, 233, 234, 235, 236, 237, 238, 239,
 240, 241, 242, 243, 244, 245, 246, 247, 248, 249,
 250, 251, 252, 253, 254, 255
};
static rx_Bitset
inverse_translation (struct re_pattern_buffer * rxb,
       char * valid, rx_Bitset cache,
       unsigned char * translate, int c)
{
  rx_Bitset cs
    = cache + c * (((rxb->rx.local_cset_size) + (32) - 1) / (32));
  if (!valid[c])
    {
      int x;
      int c_tr = translate[(unsigned char) (c)];
      rx_bitset_null (rxb->rx.local_cset_size, cs);
      for (x = 0; x < 256; ++x)
 if (translate[(unsigned char) (x)] == c_tr)
   ((cs)[((x) / (32))] |= rx_subset_singletons[(x) & ((32) - 1)]);
      valid[c] = 1;
    }
  return cs;
}
static boolean
group_in_compile_stack (compile_stack_type compile_stack, regnum_t regnum)
{
  int this_element;
  for (this_element = compile_stack.avail - 1;
       this_element >= 0;
       this_element--)
    if (compile_stack.stack[this_element].regnum == regnum)
      return 1;
  return 0;
}
static reg_errcode_t
compile_range (struct re_pattern_buffer * rxb, rx_Bitset cs,
        const char ** p_ptr, const char * pend,
        unsigned char * translate, reg_syntax_t syntax,
        rx_Bitset inv_tr, char * valid_inv_tr)
{
  unsigned this_char;
  const char *p = *p_ptr;
  unsigned char range_end;
  unsigned char range_start = translate[(unsigned char) (p[-2])];
  if (p == pend)
    return REG_ERANGE;
  do {if (p == pend) return REG_EEND; range_end = (unsigned char) *p++; range_end = translate[range_end]; } while (0);
  (*p_ptr)++;
  if (range_start > range_end)
    return syntax & (((((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) ? REG_ERANGE : REG_NOERROR;
  for (this_char = range_start; this_char <= range_end; this_char++)
    {
      rx_Bitset it =
 inverse_translation (rxb, valid_inv_tr, inv_tr, translate, this_char);
      rx_bitset_union (rxb->rx.local_cset_size, cs, it);
    }
  return REG_NOERROR;
}
static void
find_backrefs (char * out, struct rexp_node * rexp,
        struct re_se_params * params)
{
  if (rexp)
    switch (rexp->type)
      {
      case r_cset:
      case r_data:
 return;
      case r_alternate:
      case r_concat:
      case r_opt:
      case r_star:
      case r_2phase_star:
 find_backrefs (out, rexp->params.pair.left, params);
 find_backrefs (out, rexp->params.pair.right, params);
 return;
      case r_side_effect:
 if ( ((int)rexp->params.side_effect >= 0)
     && (params [(int)rexp->params.side_effect].se == re_se_backref))
   out[ params [(int)rexp->params.side_effect].op1] = 1;
 return;
      }
}
static int
compute_fastset (struct re_pattern_buffer * rxb, struct rexp_node * rexp)
{
  if (!rexp)
    return 1;
  switch (rexp->type)
    {
    case r_data:
      return 1;
    case r_cset:
      {
 rx_bitset_union (rxb->rx.local_cset_size,
    rxb->fastset, rexp->params.cset);
      }
      return 0;
    case r_concat:
      return (compute_fastset (rxb, rexp->params.pair.left)
       && compute_fastset (rxb, rexp->params.pair.right));
    case r_2phase_star:
      compute_fastset (rxb, rexp->params.pair.left);
      return 1;
    case r_alternate:
      return !!(compute_fastset (rxb, rexp->params.pair.left)
  + compute_fastset (rxb, rexp->params.pair.right));
    case r_opt:
    case r_star:
      compute_fastset (rxb, rexp->params.pair.left);
      return 1;
    case r_side_effect:
      return 1;
    }
  return 0;
}
static int
is_anchored (struct rexp_node * rexp, rx_side_effect se)
{
  if (!rexp)
    return 2;
  switch (rexp->type)
    {
    case r_cset:
    case r_data:
      return 0;
    case r_concat:
    case r_2phase_star:
      {
 int l = is_anchored (rexp->params.pair.left, se);
 return (l == 2 ? is_anchored (rexp->params.pair.right, se) : l);
      }
    case r_alternate:
      {
 int l = is_anchored (rexp->params.pair.left, se);
 int r = l ? is_anchored (rexp->params.pair.right, se) : 0;
 return ((l) > (r) ? (l) : (r));
      }
    case r_opt:
    case r_star:
      return is_anchored (rexp->params.pair.left, se) ? 2 : 0;
    case r_side_effect:
      return ((rexp->params.side_effect == se)
       ? 1 : 2);
    }
  return 0;
}
static struct rexp_node *
remove_unecessary_side_effects (struct rx * rx, char * needed,
    struct rexp_node * rexp,
    struct re_se_params * params)
{
  struct rexp_node * l;
  struct rexp_node * r;
  if (!rexp)
    return 0;
  else
    switch (rexp->type)
      {
      case r_cset:
      case r_data:
 return rexp;
      case r_alternate:
      case r_concat:
      case r_2phase_star:
 l = remove_unecessary_side_effects (rx, needed,
         rexp->params.pair.left, params);
 r = remove_unecessary_side_effects (rx, needed,
         rexp->params.pair.right, params);
 if ((l && r) || (rexp->type != r_concat))
   {
     rexp->params.pair.left = l;
     rexp->params.pair.right = r;
     return rexp;
   }
 else
   {
     rexp->params.pair.left = rexp->params.pair.right = 0;
     rx_free_rexp (rx, rexp);
     return l ? l : r;
   }
      case r_opt:
      case r_star:
 l = remove_unecessary_side_effects (rx, needed,
         rexp->params.pair.left, params);
 if (l)
   {
     rexp->params.pair.left = l;
     return rexp;
   }
 else
   {
     rexp->params.pair.left = 0;
     rx_free_rexp (rx, rexp);
     return 0;
   }
      case r_side_effect:
 {
   int se = (int)rexp->params.side_effect;
   if ( (se >= 0)
       && ( ((enum re_side_effects)params[se].se == re_se_lparen)
    || ((enum re_side_effects)params[se].se == re_se_rparen))
       && (params [se].op1 > 0)
       && (!needed [params [se].op1]))
     {
       rx_free_rexp (rx, rexp);
       return 0;
     }
   else
     return rexp;
 }
      }
  return 0;
}
static int
pointless_if_repeated (struct rexp_node * node, struct re_se_params * params)
{
  if (!node)
    return 1;
  switch (node->type)
    {
    case r_cset:
      return 0;
    case r_alternate:
    case r_concat:
    case r_2phase_star:
      return (pointless_if_repeated (node->params.pair.left, params)
       && pointless_if_repeated (node->params.pair.right, params));
    case r_opt:
    case r_star:
      return pointless_if_repeated (node->params.pair.left, params);
    case r_side_effect:
      switch (((int)node->params.side_effect < 0)
       ? (enum re_side_effects)node->params.side_effect
       : (enum re_side_effects)params[(int)node->params.side_effect].se)
 {
 case re_se_try:
 case re_se_at_dot:
 case re_se_begbuf:
 case re_se_hat:
 case re_se_wordbeg:
 case re_se_wordbound:
 case re_se_notwordbound:
 case re_se_wordend:
 case re_se_endbuf:
 case re_se_dollar:
 case re_se_fail:
 case re_se_win:
   return 1;
 case re_se_lparen:
 case re_se_rparen:
 case re_se_iter:
 case re_se_end_iter:
 case re_se_syntax:
 case re_se_not_syntax:
 case re_se_backref:
   return 0;
 }
    case r_data:
    default:
      return 0;
    }
}
static int
registers_on_stack (struct re_pattern_buffer * rxb,
      struct rexp_node * rexp, int in_danger,
      struct re_se_params * params)
{
  if (!rexp)
    return 0;
  else
    switch (rexp->type)
      {
      case r_cset:
      case r_data:
 return 0;
      case r_alternate:
      case r_concat:
 return ( registers_on_stack (rxb, rexp->params.pair.left,
           in_danger, params)
  || (registers_on_stack
      (rxb, rexp->params.pair.right,
       in_danger, params)));
      case r_opt:
 return registers_on_stack (rxb, rexp->params.pair.left, 0, params);
      case r_star:
 return registers_on_stack (rxb, rexp->params.pair.left, 1, params);
      case r_2phase_star:
 return
   ( registers_on_stack (rxb, rexp->params.pair.left, 1, params)
    || registers_on_stack (rxb, rexp->params.pair.right, 1, params));
      case r_side_effect:
 {
   int se = (int)rexp->params.side_effect;
   if ( in_danger
       && (se >= 0)
       && (params [se].op1 > 0)
       && ( ((enum re_side_effects)params[se].se == re_se_lparen)
    || ((enum re_side_effects)params[se].se == re_se_rparen)))
     return 1;
   else
     return 0;
 }
      }
  return 0;
}
static char idempotent_complex_se[] =
{
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
  1,
  1,
  1,
  0,
  0,
  0,
  0,
  23
};
static char idempotent_se[] =
{
  13,
  1,
  0,
  0,
  0,
  0,
  0,
  1,
  0,
  0,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
 
 
 
 
 
 
 
  42
};
static int
has_any_se (struct rx * rx,
     struct rexp_node * rexp)
{
  if (!rexp)
    return 0;
  switch (rexp->type)
    {
    case r_cset:
    case r_data:
      return 0;
    case r_side_effect:
      return 1;
    case r_2phase_star:
    case r_concat:
    case r_alternate:
      return
 ( has_any_se (rx, rexp->params.pair.left)
  || has_any_se (rx, rexp->params.pair.right));
    case r_opt:
    case r_star:
      return has_any_se (rx, rexp->params.pair.left);
    }
  return 0;
}
static int
has_non_idempotent_epsilon_path (struct rx * rx,
     struct rexp_node * rexp,
     struct re_se_params * params)
{
  if (!rexp)
    return 0;
  switch (rexp->type)
    {
    case r_cset:
    case r_data:
    case r_star:
      return 0;
    case r_side_effect:
      return
 !((int)rexp->params.side_effect > 0
   ? idempotent_complex_se [ params [(int)rexp->params.side_effect].se ]
   : idempotent_se [-(int)rexp->params.side_effect]);
    case r_alternate:
      return
 ( has_non_idempotent_epsilon_path (rx,
          rexp->params.pair.left, params)
  || has_non_idempotent_epsilon_path (rx,
          rexp->params.pair.right, params));
    case r_2phase_star:
    case r_concat:
      return
 ( has_non_idempotent_epsilon_path (rx,
          rexp->params.pair.left, params)
  && has_non_idempotent_epsilon_path (rx,
          rexp->params.pair.right, params));
    case r_opt:
      return has_non_idempotent_epsilon_path (rx,
           rexp->params.pair.left, params);
    }
  return 0;
}
static int
begins_with_complex_se (struct rx * rx, struct rexp_node * rexp)
{
  if (!rexp)
    return 0;
  switch (rexp->type)
    {
    case r_cset:
    case r_data:
      return 0;
    case r_side_effect:
      return ((int)rexp->params.side_effect >= 0);
    case r_alternate:
      return
 ( begins_with_complex_se (rx, rexp->params.pair.left)
  && begins_with_complex_se (rx, rexp->params.pair.right));
    case r_concat:
      return has_any_se (rx, rexp->params.pair.left);
    case r_opt:
    case r_star:
    case r_2phase_star:
      return 0;
    }
  return 0;
}
static void
speed_up_alt (struct rx * rx,
       struct rexp_node * rexp,
       int unposix)
{
  if (!rexp)
    return;
  switch (rexp->type)
    {
    case r_cset:
    case r_data:
    case r_side_effect:
      return;
    case r_opt:
    case r_star:
      speed_up_alt (rx, rexp->params.pair.left, unposix);
      return;
    case r_2phase_star:
    case r_concat:
      speed_up_alt (rx, rexp->params.pair.left, unposix);
      speed_up_alt (rx, rexp->params.pair.right, unposix);
      return;
    case r_alternate:
      speed_up_alt (rx, rexp->params.pair.left, unposix);
      speed_up_alt (rx, rexp->params.pair.right->params.pair.right, unposix);
      if ( unposix
   || (begins_with_complex_se
       (rx, rexp->params.pair.right->params.pair.right))
   || !( has_any_se (rx, rexp->params.pair.right->params.pair.right)
        || has_any_se (rx, rexp->params.pair.left)))
 {
   struct rexp_node * conc = rexp->params.pair.right;
   rexp->params.pair.right = conc->params.pair.right;
   conc->params.pair.right = 0;
   rx_free_rexp (rx, conc);
 }
    }
}
reg_errcode_t
rx_compile (const char *pattern, int size,
     reg_syntax_t syntax,
     struct re_pattern_buffer * rxb)
{
  RX_subset
    inverse_translate [(1 << 8) * ((((1 << 8)) + (32) - 1) / (32))];
  char
    validate_inv_tr [(1 << 8) * ((((1 << 8)) + (32) - 1) / (32))];
  register unsigned char c, c1;
  const char *p1;
  compile_stack_type compile_stack;
  const char *p = pattern;
  const char *pend = pattern + size;
  unsigned char *translate = (rxb->translate
         ? (unsigned char *)rxb->translate
         : (unsigned char *)id_translation);
  struct rexp_node * rexp = 0;
  struct rexp_node * orig_rexp = 0;
  struct rexp_node * fewer_side_effects = 0;
  struct rexp_node ** top_expression = &rexp;
  struct rexp_node ** last_expression = top_expression;
  struct rexp_node * append;
  regnum_t regnum = 0;
  const char *beg_interval;
  struct re_se_params * params = 0;
  int paramc = 0;
  rx_side_effect side;
  memset ((validate_inv_tr), 0, (sizeof (validate_inv_tr)));
  rxb->rx.instruction_table = rx_id_instruction_table;
  compile_stack.stack = ((compile_stack_elt_t *) malloc ((32) * sizeof (compile_stack_elt_t)));
  if (compile_stack.stack == 0)
    return REG_ESPACE;
  compile_stack.size = 32;
  compile_stack.avail = 0;
  rxb->rx.cache = &default_cache;
  rxb->syntax = syntax;
  rxb->fastmap_accurate = 0;
  rxb->not_bol = rxb->not_eol = 0;
  rxb->least_subs = 0;
  rxb->re_nsub = 0;
   init_syntax_once ();
  while (p != pend)
    {
      do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0);
      switch (c)
        {
        case '^':
          {
            if (
                   p == pattern + 1
                || syntax & ((((1) << 1) << 1) << 1)
                || at_begline_loc_p (pattern, p, syntax))
       {
  struct rexp_node * n
    = rx_mk_r_side_effect (&rxb->rx, (rx_side_effect)re_se_hat);
  if (!n)
    return REG_ESPACE;
  append = n;
  goto append_node;
       }
            else
              goto normal_char;
          }
          break;
        case '$':
          {
            if (
                   p == pend
                || syntax & ((((1) << 1) << 1) << 1)
                || at_endline_loc_p (p, pend, syntax))
       {
  struct rexp_node * n
    = rx_mk_r_side_effect (&rxb->rx, (rx_side_effect)re_se_dollar);
  if (!n)
    return REG_ESPACE;
  append = n;
  goto append_node;
       }
             else
               goto normal_char;
           }
           break;
 case '+':
        case '?':
          if ((syntax & ((1) << 1))
              || (syntax & (((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)))
            goto normal_char;
        handle_plus:
        case '*':
          if (pointless_if_repeated (*last_expression, params))
            {
              if (syntax & ((((((1) << 1) << 1) << 1) << 1) << 1))
                return REG_BADRPT;
              else if (!(syntax & (((((1) << 1) << 1) << 1) << 1)))
                goto normal_char;
            }
          {
            char zero_times_ok = 0, many_times_ok = 0;
            for (;;)
              {
                zero_times_ok |= c != '+';
                many_times_ok |= c != '?';
                if (p == pend)
                  break;
                do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0);
                if (c == '*'
                    || (!(syntax & ((1) << 1)) && (c == '+' || c == '?')))
                  ;
                else if (syntax & ((1) << 1) && c == '\\')
                  {
                    if (p == pend) return REG_EESCAPE;
                    do {if (p == pend) return REG_EEND; c1 = (unsigned char) *p++; c1 = translate[c1]; } while (0);
                    if (!(c1 == '+' || c1 == '?'))
                      {
                        p--;
                        p--;
                        break;
                      }
                    c = c1;
                  }
                else
                  {
                    p--;
                    break;
                  }
               }
            if (!last_expression)
              break;
     {
       struct rexp_node * inner_exp = *last_expression;
       int need_sync = 0;
       if (many_times_ok
    && has_non_idempotent_epsilon_path (&rxb->rx,
            inner_exp, params))
  {
    struct rexp_node * pusher
      = rx_mk_r_side_effect (&rxb->rx,
        (rx_side_effect)re_se_pushpos);
    struct rexp_node * checker
      = rx_mk_r_side_effect (&rxb->rx,
        (rx_side_effect)re_se_chkpos);
    struct rexp_node * pushback
      = rx_mk_r_side_effect (&rxb->rx,
        (rx_side_effect)re_se_pushback);
    rx_Bitset cs = rx_cset (&rxb->rx);
    struct rexp_node * lit_t = rx_mk_r_cset (&rxb->rx, cs);
    struct rexp_node * fake_state
      = rx_mk_r_concat (&rxb->rx, pushback, lit_t);
    struct rexp_node * phase2
      = rx_mk_r_concat (&rxb->rx, checker, fake_state);
    struct rexp_node * popper
      = rx_mk_r_side_effect (&rxb->rx,
        (rx_side_effect)re_se_poppos);
    struct rexp_node * star
      = rx_mk_r_2phase_star (&rxb->rx, inner_exp, phase2);
    struct rexp_node * a
      = rx_mk_r_concat (&rxb->rx, pusher, star);
    struct rexp_node * whole_thing
      = rx_mk_r_concat (&rxb->rx, a, popper);
    if (!(pusher && star && pushback && lit_t && fake_state
   && lit_t && phase2 && checker && popper
   && a && whole_thing))
      return REG_ESPACE;
    ((cs)[(('t') / (32))] |= rx_subset_singletons[('t') & ((32) - 1)]);
    *last_expression = whole_thing;
  }
       else
  {
    struct rexp_node * star =
      (many_times_ok ? rx_mk_r_star : rx_mk_r_opt)
        (&rxb->rx, *last_expression);
    if (!star)
      return REG_ESPACE;
    *last_expression = star;
    need_sync = has_any_se (&rxb->rx, *last_expression);
  }
       if (!zero_times_ok)
  {
    struct rexp_node * concat
      = rx_mk_r_concat (&rxb->rx, inner_exp,
          rx_copy_rexp (&rxb->rx,
          *last_expression));
    if (!concat)
      return REG_ESPACE;
    *last_expression = concat;
  }
       if (need_sync)
  {
    int sync_se = paramc;
    params = (params
       ? ((struct re_se_params *)
          realloc (params,
     sizeof (*params) * (1 + paramc)))
       : ((struct re_se_params *)
          malloc (sizeof (*params))));
    if (!params)
      return REG_ESPACE;
    ++paramc;
    params [sync_se].se = re_se_tv;
    side = (rx_side_effect)sync_se;
    goto add_side_effect;
  }
     }
   }
   break;
 case '.':
   {
     rx_Bitset cs = rx_cset (&rxb->rx);
     struct rexp_node * n = rx_mk_r_cset (&rxb->rx, cs);
     if (!(cs && n))
       return REG_ESPACE;
     rx_bitset_universe (rxb->rx.local_cset_size, cs);
     if (!(rxb->syntax & (((((((1) << 1) << 1) << 1) << 1) << 1) << 1)))
       ((cs)[(('\n') / (32))] &= ~ rx_subset_singletons[('\n') & ((32) - 1)]);
     if (!(rxb->syntax & ((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)))
       ((cs)[((0) / (32))] &= ~ rx_subset_singletons[(0) & ((32) - 1)]);
     append = n;
     goto append_node;
     break;
   }
        case '[':
   if (p == pend) return REG_EBRACK;
          {
            boolean had_char_class = 0;
     rx_Bitset cs = rx_cset (&rxb->rx);
     struct rexp_node * node = rx_mk_r_cset (&rxb->rx, cs);
     int is_inverted = *p == '^';
     if (!(node && cs))
       return REG_ESPACE;
     append = node;
            if (is_inverted)
       p++;
            p1 = p;
            for (;;)
              {
                if (p == pend) return REG_EBRACK;
                do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0);
                if ((syntax & (1)) && c == '\\')
                  {
                    if (p == pend) return REG_EESCAPE;
                    do {if (p == pend) return REG_EEND; c1 = (unsigned char) *p++; c1 = translate[c1]; } while (0);
      {
        rx_Bitset it = inverse_translation (rxb,
         validate_inv_tr,
         inverse_translate,
         translate,
         c1);
        rx_bitset_union (rxb->rx.local_cset_size, cs, it);
      }
                    continue;
                  }
                if (c == ']' && p != p1 + 1)
                  goto finalize_class_and_append;
                if (had_char_class && c == '-' && *p != ']')
                  return REG_ERANGE;
                if (c == '-'
                    && !(p - 2 >= pattern && p[-2] == '[')
                    && !(p - 3 >= pattern && p[-3] == '[' && p[-2] == '^')
                    && *p != ']')
                  {
                    reg_errcode_t ret
                      = compile_range (rxb, cs, &p, pend, translate, syntax,
           inverse_translate, validate_inv_tr);
                    if (ret != REG_NOERROR) return ret;
                  }
                else if (p[0] == '-' && p[1] != ']')
                  {
                    reg_errcode_t ret;
                    do {if (p == pend) return REG_EEND; c1 = (unsigned char) *p++; c1 = translate[c1]; } while (0);
                    ret = compile_range (rxb, cs, &p, pend, translate, syntax,
      inverse_translate, validate_inv_tr);
                    if (ret != REG_NOERROR) return ret;
                  }
  else if ((syntax & (((1) << 1) << 1))
    && (c == '[') && (*p == ':'))
                  {
                    char str[6 + 1];
                    do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0);
                    c1 = 0;
                    if (p == pend) return REG_EBRACK;
                    for (;;)
                      {
                        do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0);
                        if (c == ':' || c == ']' || p == pend
                            || c1 == 6)
     break;
                        str[c1++] = c;
                      }
                    str[c1] = '\0';
                    if (c == ':' && *p == ']')
                      {
                        int ch;
                        boolean is_alnum = !strcmp (str, "alnum");
                        boolean is_alpha = !strcmp (str, "alpha");
                        boolean is_blank = !strcmp (str, "blank");
                        boolean is_cntrl = !strcmp (str, "cntrl");
                        boolean is_digit = !strcmp (str, "digit");
                        boolean is_graph = !strcmp (str, "graph");
                        boolean is_lower = !strcmp (str, "lower");
                        boolean is_print = !strcmp (str, "print");
                        boolean is_punct = !strcmp (str, "punct");
                        boolean is_space = !strcmp (str, "space");
                        boolean is_upper = !strcmp (str, "upper");
                        boolean is_xdigit = !strcmp (str, "xdigit");
                        if (!(!strcmp (str, "alpha") || !strcmp (str, "upper") || !strcmp (str, "lower") || !strcmp (str, "digit") || !strcmp (str, "alnum") || !strcmp (str, "xdigit") || !strcmp (str, "space") || !strcmp (str, "print") || !strcmp (str, "punct") || !strcmp (str, "graph") || !strcmp (str, "cntrl") || !strcmp (str, "blank"))) return REG_ECTYPE;
                        do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0);
                        if (p == pend) return REG_EBRACK;
                        for (ch = 0; ch < 1 << 8; ch++)
                          {
                            if ( (is_alnum && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISalnum))
                                || (is_alpha && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISalpha))
                                || (is_blank && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISblank))
                                || (is_cntrl && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _IScntrl))
                                || (is_digit && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISdigit))
                                || (is_graph && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISgraph))
                                || (is_lower && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISlower))
                                || (is_print && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISprint))
                                || (is_punct && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISpunct))
                                || (is_space && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISspace))
                                || (is_upper && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISupper))
                                || (is_xdigit && ((*__ctype_b_loc ())[(int) ((ch))] & (unsigned short int) _ISxdigit)))
         {
    rx_Bitset it =
      inverse_translation (rxb,
             validate_inv_tr,
             inverse_translate,
             translate,
             ch);
    rx_bitset_union (rxb->rx.local_cset_size,
       cs, it);
         }
                          }
                        had_char_class = 1;
                      }
                    else
                      {
                        c1++;
                        while (c1--)
                          p--;
   {
     rx_Bitset it =
       inverse_translation (rxb,
       validate_inv_tr,
       inverse_translate,
       translate,
       '[');
     rx_bitset_union (rxb->rx.local_cset_size,
        cs, it);
   }
   {
     rx_Bitset it =
       inverse_translation (rxb,
       validate_inv_tr,
       inverse_translate,
       translate,
       ':');
     rx_bitset_union (rxb->rx.local_cset_size,
        cs, it);
   }
                        had_char_class = 0;
                      }
                  }
                else
                  {
                    had_char_class = 0;
      {
        rx_Bitset it = inverse_translation (rxb,
         validate_inv_tr,
         inverse_translate,
         translate,
         c);
        rx_bitset_union (rxb->rx.local_cset_size, cs, it);
      }
                  }
              }
   finalize_class_and_append:
     if (is_inverted)
       {
  rx_bitset_complement (rxb->rx.local_cset_size, cs);
  if (syntax & (((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
    ((cs)[(('\n') / (32))] &= ~ rx_subset_singletons[('\n') & ((32) - 1)]);
       }
     goto append_node;
          }
          break;
 case '(':
          if (syntax & ((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
            goto handle_open;
          else
            goto normal_char;
        case ')':
          if (syntax & ((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
            goto handle_close;
          else
            goto normal_char;
        case '\n':
          if (syntax & ((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
            goto handle_alt;
          else
            goto normal_char;
 case '|':
          if (syntax & ((((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
            goto handle_alt;
          else
            goto normal_char;
        case '{':
   if ((syntax & ((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)) && (syntax & (((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)))
     goto handle_interval;
   else
     goto normal_char;
        case '\\':
          if (p == pend) return REG_EESCAPE;
          do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; } while (0);
          switch (c)
            {
            case '(':
              if (syntax & ((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
                goto normal_backslash;
            handle_open:
              rxb->re_nsub++;
              regnum++;
              if ((compile_stack.avail == compile_stack.size))
                {
                  ((compile_stack.stack) = (compile_stack_elt_t *) realloc (compile_stack.stack, (compile_stack.size << 1) * sizeof (compile_stack_elt_t)));
                  if (compile_stack.stack == 0) return REG_ESPACE;
                  compile_stack.size <<= 1;
                }
       if (*last_expression)
  {
    struct rexp_node * concat
      = rx_mk_r_concat (&rxb->rx, *last_expression, 0);
    if (!concat)
      return REG_ESPACE;
    *last_expression = concat;
    last_expression = &concat->params.pair.right;
  }
       (compile_stack.stack[compile_stack.avail]).top_expression = top_expression;
       (compile_stack.stack[compile_stack.avail]).last_expression = last_expression;
              (compile_stack.stack[compile_stack.avail]).regnum = regnum;
              compile_stack.avail++;
       top_expression = last_expression;
       break;
            case ')':
              if (syntax & ((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)) goto normal_backslash;
            handle_close:
              if ((compile_stack.avail == 0))
                if (syntax & ((((((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
                  goto normal_char;
                else
                  return REG_ERPAREN;
              {
                regnum_t this_group_regnum;
  struct rexp_node ** inner = top_expression;
                compile_stack.avail--;
  top_expression = (compile_stack.stack[compile_stack.avail]).top_expression;
  last_expression = (compile_stack.stack[compile_stack.avail]).last_expression;
                this_group_regnum = (compile_stack.stack[compile_stack.avail]).regnum;
  {
    int left_se = paramc;
    int right_se = paramc + 1;
    params = (params
       ? ((struct re_se_params *)
          realloc (params,
     (paramc + 2) * sizeof (params[0])))
       : ((struct re_se_params *)
          malloc (2 * sizeof (params[0]))));
    if (!params)
      return REG_ESPACE;
    paramc += 2;
    params[left_se].se = re_se_lparen;
    params[left_se].op1 = this_group_regnum;
    params[right_se].se = re_se_rparen;
    params[right_se].op1 = this_group_regnum;
    {
      struct rexp_node * left
        = rx_mk_r_side_effect (&rxb->rx,
          (rx_side_effect)left_se);
      struct rexp_node * right
        = rx_mk_r_side_effect (&rxb->rx,
          (rx_side_effect)right_se);
      struct rexp_node * c1
        = (*inner
    ? rx_mk_r_concat (&rxb->rx, left, *inner) : left);
      struct rexp_node * c2
        = rx_mk_r_concat (&rxb->rx, c1, right);
      if (!(left && right && c1 && c2))
        return REG_ESPACE;
      *inner = c2;
    }
  }
  break;
       }
            case '|':
              if ((syntax & (((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)) || (syntax & ((((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)))
                goto normal_backslash;
            handle_alt:
              if (syntax & (((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
                goto normal_char;
       {
  struct rexp_node * alt
    = rx_mk_r_alternate (&rxb->rx, *top_expression, 0);
  if (!alt)
    return REG_ESPACE;
  *top_expression = alt;
  last_expression = &alt->params.pair.right;
  {
    int sync_se = paramc;
    params = (params
       ? ((struct re_se_params *)
          realloc (params,
     (paramc + 1) * sizeof (params[0])))
       : ((struct re_se_params *)
          malloc (sizeof (params[0]))));
    if (!params)
      return REG_ESPACE;
    ++paramc;
    params[sync_se].se = re_se_tv;
    {
      struct rexp_node * sync
        = rx_mk_r_side_effect (&rxb->rx,
          (rx_side_effect)sync_se);
      struct rexp_node * conc
        = rx_mk_r_concat (&rxb->rx, sync, 0);
      if (!sync || !conc)
        return REG_ESPACE;
      *last_expression = conc;
      last_expression = &conc->params.pair.right;
    }
  }
       }
              break;
            case '{':
              if (!(syntax & ((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
                  || ((syntax & ((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)) && (syntax & (((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)))
                  || (p - 2 == pattern && p == pend))
                goto normal_backslash;
            handle_interval:
              {
                int lower_bound = -1, upper_bound = -1;
                beg_interval = p - 1;
                if (p == pend)
                  {
                    if (syntax & (((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
                      goto unfetch_interval;
                    else
                      return REG_EBRACE;
                  }
                { if (p != pend) { do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0); while (((*__ctype_b_loc ())[(int) ((c))] & (unsigned short int) _ISdigit)) { if (lower_bound < 0) lower_bound = 0; lower_bound = lower_bound * 10 + c - '0'; if (p == pend) break; do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0); } } };
                if (c == ',')
                  {
                    { if (p != pend) { do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0); while (((*__ctype_b_loc ())[(int) ((c))] & (unsigned short int) _ISdigit)) { if (upper_bound < 0) upper_bound = 0; upper_bound = upper_bound * 10 + c - '0'; if (p == pend) break; do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0); } } };
                    if (upper_bound < 0) upper_bound = ((1 << 15) - 1);
                  }
                else
                  upper_bound = lower_bound;
                if (lower_bound < 0 || upper_bound > ((1 << 15) - 1)
                    || lower_bound > upper_bound)
                  {
                    if (syntax & (((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
                      goto unfetch_interval;
                    else
                      return REG_BADBR;
                  }
                if (!(syntax & (((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)))
                  {
                    if (c != '\\') return REG_EBRACE;
                    do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0);
                  }
                if (c != '}')
                  {
                    if (syntax & (((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
                      goto unfetch_interval;
                    else
                      return REG_BADBR;
                  }
                if (pointless_if_repeated (*last_expression, params))
                  {
                    if (syntax & ((((((1) << 1) << 1) << 1) << 1) << 1))
                      return REG_BADRPT;
                    else if (!(syntax & (((((1) << 1) << 1) << 1) << 1)))
                      goto unfetch_interval;
                  }
                 if (upper_bound == 0)
     {
       if (*last_expression)
         {
    rx_free_rexp (&rxb->rx, *last_expression);
    *last_expression = 0;
         }
     }
  else
    {
      int iter_se = paramc;
      int end_se = paramc + 1;
      params = (params
         ? ((struct re_se_params *)
     realloc (params,
       sizeof (*params) * (2 + paramc)))
         : ((struct re_se_params *)
     malloc (2 * sizeof (*params))));
      if (!params)
        return REG_ESPACE;
      paramc += 2;
      params [iter_se].se = re_se_iter;
      params [iter_se].op1 = lower_bound;
      params[iter_se].op2 = upper_bound;
      params[end_se].se = re_se_end_iter;
      params[end_se].op1 = lower_bound;
      params[end_se].op2 = upper_bound;
      {
        struct rexp_node * push0
   = rx_mk_r_side_effect (&rxb->rx,
            (rx_side_effect)re_se_push0);
        struct rexp_node * start_one_iter
   = rx_mk_r_side_effect (&rxb->rx,
            (rx_side_effect)iter_se);
        struct rexp_node * phase1
   = rx_mk_r_concat (&rxb->rx, start_one_iter,
       *last_expression);
        struct rexp_node * pushback
   = rx_mk_r_side_effect (&rxb->rx,
            (rx_side_effect)re_se_pushback);
        rx_Bitset cs = rx_cset (&rxb->rx);
        struct rexp_node * lit_t
   = rx_mk_r_cset (&rxb->rx, cs);
        struct rexp_node * phase2
   = rx_mk_r_concat (&rxb->rx, pushback, lit_t);
        struct rexp_node * loop
   = rx_mk_r_2phase_star (&rxb->rx, phase1, phase2);
        struct rexp_node * push_n_loop
   = rx_mk_r_concat (&rxb->rx, push0, loop);
        struct rexp_node * final_test
   = rx_mk_r_side_effect (&rxb->rx,
            (rx_side_effect)end_se);
        struct rexp_node * full_exp
   = rx_mk_r_concat (&rxb->rx, push_n_loop, final_test);
        if (!(push0 && start_one_iter && phase1
       && pushback && lit_t && phase2
       && loop && push_n_loop && final_test && full_exp))
   return REG_ESPACE;
        ((cs)[(('t') / (32))] |= rx_subset_singletons[('t') & ((32) - 1)]);
        *last_expression = full_exp;
      }
    }
                beg_interval = 0;
              }
              break;
            unfetch_interval:
               p = beg_interval;
               beg_interval = ((void *)0);
               do {if (p == pend) return REG_EEND; c = (unsigned char) *p++; c = translate[c]; } while (0);
               if (!(syntax & (((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)))
                 {
                   if (p > pattern && p[-1] == '\\')
                     goto normal_backslash;
                 }
               goto normal_char;
            case 'w':
            case 'W':
       {
  rx_Bitset cs = rx_cset (&rxb->rx);
  struct rexp_node * n = (cs ? rx_mk_r_cset (&rxb->rx, cs) : 0);
  if (!(cs && n))
    return REG_ESPACE;
  if (c == 'W')
    rx_bitset_universe (rxb->rx.local_cset_size ,cs);
  {
    int x;
    for (x = rxb->rx.local_cset_size - 1; x > 0; --x)
      if (re_syntax_table[x] & 1)
        ((cs)[((x) / (32))] ^= rx_subset_singletons[(x) & ((32) - 1)]);
  }
  append = n;
  goto append_node;
       }
              break;
            case '<':
       side = (rx_side_effect)re_se_wordbeg;
       goto add_side_effect;
              break;
            case '>':
              side = (rx_side_effect)re_se_wordend;
       goto add_side_effect;
              break;
            case 'b':
              side = (rx_side_effect)re_se_wordbound;
       goto add_side_effect;
              break;
            case 'B':
              side = (rx_side_effect)re_se_notwordbound;
       goto add_side_effect;
              break;
            case '`':
       side = (rx_side_effect)re_se_begbuf;
       goto add_side_effect;
       break;
            case '\'':
       side = (rx_side_effect)re_se_endbuf;
       goto add_side_effect;
              break;
     add_side_effect:
       {
  struct rexp_node * se
    = rx_mk_r_side_effect (&rxb->rx, side);
  if (!se)
    return REG_ESPACE;
  append = se;
  goto append_node;
       }
       break;
            case '1': case '2': case '3': case '4': case '5':
            case '6': case '7': case '8': case '9':
              if (syntax & (((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))
                goto normal_char;
              c1 = c - '0';
              if (c1 > regnum)
                return REG_ESUBREG;
              if (group_in_compile_stack (compile_stack, c1))
  return REG_ESUBREG;
       {
  int backref_se = paramc;
  params = (params
     ? ((struct re_se_params *)
        realloc (params,
          sizeof (*params) * (1 + paramc)))
     : ((struct re_se_params *)
        malloc (sizeof (*params))));
  if (!params)
    return REG_ESPACE;
  ++paramc;
  params[backref_se].se = re_se_backref;
  params[backref_se].op1 = c1;
  side = (rx_side_effect)backref_se;
  goto add_side_effect;
       }
              break;
            case '+':
            case '?':
              if (syntax & ((1) << 1))
                goto handle_plus;
              else
                goto normal_backslash;
            default:
            normal_backslash:
              c = translate[(unsigned char) (c)];
              goto normal_char;
            }
          break;
 default:
 normal_char:
     {
       rx_Bitset cs = rx_cset(&rxb->rx);
       struct rexp_node * match = rx_mk_r_cset (&rxb->rx, cs);
       rx_Bitset it;
       if (!(cs && match))
  return REG_ESPACE;
       it = inverse_translation (rxb, validate_inv_tr,
     inverse_translate, translate, c);
       rx_bitset_union ((1 << 8), cs, it);
       append = match;
     append_node:
       if (*last_expression)
  {
    struct rexp_node * concat
      = rx_mk_r_concat (&rxb->rx, *last_expression, append);
    if (!concat)
      return REG_ESPACE;
    *last_expression = concat;
    last_expression = &concat->params.pair.right;
  }
       else
  *last_expression = append;
     }
 }
    }
  {
    int win_se = paramc;
    params = (params
       ? ((struct re_se_params *)
   realloc (params,
     sizeof (*params) * (1 + paramc)))
       : ((struct re_se_params *)
   malloc (sizeof (*params))));
    if (!params)
      return REG_ESPACE;
    ++paramc;
    params[win_se].se = re_se_win;
    {
      struct rexp_node * se
 = rx_mk_r_side_effect (&rxb->rx, (rx_side_effect)win_se);
      struct rexp_node * concat
 = rx_mk_r_concat (&rxb->rx, rexp, se);
      if (!(se && concat))
 return REG_ESPACE;
      rexp = concat;
    }
  }
  if (!(compile_stack.avail == 0))
    return REG_EPAREN;
      free (compile_stack.stack);
  orig_rexp = rexp;
  {
    rx_Bitset cs = rx_cset(&rxb->rx);
    rx_Bitset cs2 = rx_cset(&rxb->rx);
    char * se_map = (char *) __builtin_alloca (paramc);
    struct rexp_node * new_rexp = 0;
    memset ((se_map), 0, (paramc));
    find_backrefs (se_map, rexp, params);
    fewer_side_effects =
      remove_unecessary_side_effects (&rxb->rx, se_map,
          rx_copy_rexp (&rxb->rx, rexp), params);
    speed_up_alt (&rxb->rx, rexp, 0);
    speed_up_alt (&rxb->rx, fewer_side_effects, 1);
    {
      char * syntax_parens = rxb->syntax_parens;
      if (syntax_parens == (char *)0x1)
 rexp = remove_unecessary_side_effects
   (&rxb->rx, se_map, rexp, params);
      else if (syntax_parens)
 {
   int x;
   for (x = 0; x < paramc; ++x)
     if (( (params[x].se == re_se_lparen)
   || (params[x].se == re_se_rparen))
  && (!syntax_parens [params[x].op1]))
       se_map [x] = 1;
   rexp = remove_unecessary_side_effects
     (&rxb->rx, se_map, rexp, params);
 }
    }
    new_rexp =
      rx_mk_r_alternate
 (&rxb->rx,
  rx_mk_r_concat (&rxb->rx, rx_mk_r_cset (&rxb->rx, cs2), rexp),
  rx_mk_r_concat (&rxb->rx,
    rx_mk_r_cset (&rxb->rx, cs), fewer_side_effects));
    if (!(new_rexp && cs && cs2))
      return REG_ESPACE;
    ((cs2)[(('\0') / (32))] |= rx_subset_singletons[('\0') & ((32) - 1)]);
    ((cs)[(('\1') / (32))] |= rx_subset_singletons[('\1') & ((32) - 1)]);
    rexp = new_rexp;
  }
  {
    struct rx_nfa_state *start = 0;
    struct rx_nfa_state *end = 0;
    if (!rx_build_nfa (&rxb->rx, rexp, &start, &end))
      return REG_ESPACE;
    else
      {
 void * mem = (void *)rxb->buffer;
 unsigned long size = rxb->allocated;
 int start_id;
 char * perm_mem;
 int iterator_size = paramc * sizeof (params[0]);
 end->is_final = 1;
 start->is_start = 1;
 rx_name_nfa_states (&rxb->rx);
 start_id = start->id;
 if (!rx_eclose_nfa (&rxb->rx))
   return REG_ESPACE;
 else
   {
     rx_delete_epsilon_transitions (&rxb->rx);
     rxb->rx.reserved = ( sizeof (params[0]) * paramc
    + ((((rxb->rx.local_cset_size) + (32) - 1) / (32)) * sizeof(RX_subset)));
     if (!rx_compactify_nfa (&rxb->rx, &mem, &size))
       return REG_ESPACE;
     rxb->buffer = mem;
     rxb->allocated = size;
     rxb->rx.buffer = mem;
     rxb->rx.allocated = size;
     perm_mem = ((char *)rxb->rx.buffer
   + rxb->rx.allocated - rxb->rx.reserved);
     rxb->se_params = ((struct re_se_params *)perm_mem);
     memcpy ((rxb->se_params), (params), (iterator_size));
     perm_mem += iterator_size;
     rxb->fastset = (rx_Bitset) perm_mem;
     rxb->start = rx_id_to_nfa_state (&rxb->rx, start_id);
   }
 rx_bitset_null (rxb->rx.local_cset_size, rxb->fastset);
 rxb->can_match_empty = compute_fastset (rxb, orig_rexp);
 rxb->match_regs_on_stack =
   registers_on_stack (rxb, orig_rexp, 0, params);
 rxb->search_regs_on_stack =
   registers_on_stack (rxb, fewer_side_effects, 0, params);
 if (rxb->can_match_empty)
   rx_bitset_universe (rxb->rx.local_cset_size, rxb->fastset);
 rxb->is_anchored = is_anchored (orig_rexp, (rx_side_effect) re_se_hat);
 rxb->begbuf_only = is_anchored (orig_rexp,
     (rx_side_effect) re_se_begbuf);
      }
    rx_free_rexp (&rxb->rx, rexp);
    if (params)
      free (params);
  }
  return REG_NOERROR;
}
const char * rx_error_msg[] =
{ 0,
    "No match",
    "Invalid regular expression",
    "Invalid collation character",
    "Invalid character class name",
    "Trailing backslash",
    "Invalid back reference",
    "Unmatched [ or [^",
    "Unmatched ( or \\(",
    "Unmatched \\{",
    "Invalid content of \\{\\}",
    "Invalid range end",
    "Memory exhausted",
    "Invalid preceding regular expression",
    "Premature end of regular expression",
    "Regular expression too big",
    "Unmatched ) or \\)",
};
static char slowmap [256] =
{
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
};
static void
rx_blow_up_fastmap (struct re_pattern_buffer * rxb)
{
  int x;
  for (x = 0; x < 256; ++x)
    rxb->fastmap [x] = !!((rxb->fastset)[((x) / (32))] & rx_subset_singletons[(x) & ((32) - 1)]);
  rxb->fastmap_accurate = 1;
}
struct stack_chunk
{
  struct stack_chunk * next_chunk;
  int bytes_left;
  char * sp;
};
struct counter_frame
{
  int tag;
  int val;
  struct counter_frame * inherited_from;
  struct counter_frame * cdr;
};
struct backtrack_frame
{
  char * counter_stack_sp;
  struct rx_superstate * stk_super;
  const unsigned char * stk_tst_pos;
  int stk_tst_half;
  unsigned int stk_c;
  const unsigned char * stk_tst_str_half;
  const unsigned char * stk_tst_end_half;
  int stk_last_l;
  int stk_last_r;
  int stk_test_ret;
  struct rx_distinct_future * df;
  struct rx_distinct_future * first_df;
};
int
re_search_2 (struct re_pattern_buffer *rxb,
  const char * string1, int size1,
  const char * string2, int size2,
  int startpos, int range,
  struct re_registers *regs,
  int stop)
{
  regoff_t * lparen = 0;
  regoff_t * rparen = 0;
  regoff_t * best_lpspace = 0;
  regoff_t * best_rpspace = 0;
  int last_l;
  int last_r;
  int * best_lparen;
  int * best_rparen;
  int best_last_l;
  int best_last_r;
  unsigned num_regs = rxb->re_nsub + 1;
  int total_size = size1 + size2;
  if ((startpos < 0) || (startpos > total_size))
    return -1;
  {
    int endpos = startpos + range;
    if (endpos < -1)
      range = (-1 - startpos);
    else if (endpos > total_size)
      range = total_size - startpos;
  }
  if (rxb->begbuf_only && (range > 0))
    {
      if (startpos > 0)
 return -1;
      else
 range = 1;
    }
  if (!regs || rxb->no_sub)
    {
      best_lpspace = (regoff_t *)__builtin_alloca (num_regs * sizeof(regoff_t));
      best_rpspace = (regoff_t *)__builtin_alloca (num_regs * sizeof(regoff_t));
      best_lparen = best_lpspace;
      best_rparen = best_rpspace;
    }
  else
    {
      if (rxb->regs_allocated == 0)
 {
   regs->num_regs = ((30) > (rxb->re_nsub + 1) ? (30) : (rxb->re_nsub + 1));
   regs->start = ((regoff_t *) malloc ((regs->num_regs) * sizeof (regoff_t)));
   regs->end = ((regoff_t *) malloc ((regs->num_regs) * sizeof (regoff_t)));
   if (regs->start == 0 || regs->end == 0)
     return -2;
   rxb->regs_allocated = 1;
 }
      else if (rxb->regs_allocated == 1)
 {
   if (regs->num_regs < num_regs + 1)
     {
       regs->num_regs = num_regs + 1;
       ((regs->start) = (regoff_t *) realloc (regs->start, (regs->num_regs) * sizeof (regoff_t)));
       ((regs->end) = (regoff_t *) realloc (regs->end, (regs->num_regs) * sizeof (regoff_t)));
       if (regs->start == 0 || regs->end == 0)
  return -2;
     }
 }
      else if (rxb->regs_allocated != 2)
 return -2;
      if (regs->num_regs < num_regs + 1)
 {
   best_lpspace = ((regoff_t *)
     __builtin_alloca (num_regs * sizeof(regoff_t)));
   best_rpspace = ((regoff_t *)
     __builtin_alloca (num_regs * sizeof(regoff_t)));
   best_lparen = best_lpspace;
   best_rparen = best_rpspace;
 }
      else
 {
   best_lparen = regs->start;
   best_rparen = regs->end;
 }
    }
  lparen = (regoff_t *) __builtin_alloca (num_regs * sizeof(regoff_t));
  rparen = (regoff_t *) __builtin_alloca (num_regs * sizeof(regoff_t));
  if (!(best_rparen && best_lparen && lparen && rparen))
    return -2;
  best_last_l = best_last_r = -1;
  {
    const unsigned char * translate = (rxb->translate
           ? (unsigned char *)rxb->translate
           : (unsigned char *)id_translation);
    int ret_val = -1;
    int fastmap_chr = -1;
    int fastmap_val = 0;
    char * fastmap = rxb->fastmap ? (char *)rxb->fastmap : (char *)slowmap;
    int search_direction;
    int search_end;
    int offset;
    const unsigned char * pos;
    const unsigned char * string;
    const unsigned char * end;
    int size;
    int half;
    struct rx_superstate * start_super = 0;
    int nfa_choice = ((regs && !rxb->least_subs) ? '\0' : '\1');
    const unsigned char * abs_end;
    int first_found;
    if ((fastmap == rxb->fastmap) && !rxb->fastmap_accurate)
      rx_blow_up_fastmap (rxb);
    {
      struct rx_superset * start_contents;
      struct rx_nfa_state_set * start_nfa_set;
      start_nfa_set = rxb->start->futures->destset;
      if ( rxb->rx.start_set
   && (rxb->rx.start_set->starts_for == &rxb->rx))
 start_contents = rxb->rx.start_set;
      else
 {
   start_contents =
     rx_superstate_eclosure_union (&rxb->rx,
       rx_superset_cons (&rxb->rx, 0, 0),
       start_nfa_set);
   if (!start_contents)
     return -1;
   start_contents->starts_for = &rxb->rx;
   rxb->rx.start_set = start_contents;
 }
      if ( start_contents->superstate
   && (start_contents->superstate->rx_id == rxb->rx.rx_id))
 {
   start_super = start_contents->superstate;
   ((start_super)->locks++);
 }
      else
 {
   (++(start_contents)->refs);
   start_super = rx_superstate (&rxb->rx, start_contents);
   if (!start_super)
     return -1;
   ((start_super)->locks++);
   rx_release_superset (&rxb->rx, start_contents);
 }
    }
    abs_end = ((const unsigned char *) ((stop <= size1)
     ? string1 + stop
     : string2 + stop - size1));
    first_found = !regs;
    if (range >= 0)
      {
 search_end = ((size1 + size2) < (startpos + range) ? (size1 + size2) : (startpos + range)) + 1;
 search_direction = 1;
      }
    else
      {
 search_end = ((-1) > (startpos + range) ? (-1) : (startpos + range));
 search_direction = -1;
      }
    if ((search_direction == 1)
 ? (startpos > search_end)
 : (startpos < search_end))
      return -1;
    if (!string2 || (startpos < size1))
      {
 string = (const unsigned char *)string1;
 size = size1;
 offset = 0;
 pos = (const unsigned char *)(string1 + startpos);
 half = 0;
 end = (const unsigned char *)((string1 + size1) < (string1 + stop) ? (string1 + size1) : (string1 + stop));
      }
    else
      {
 string = (const unsigned char *)string2;
 size = size2;
 offset = size1;
 pos = (const unsigned char *)(string2 + startpos - size1);
 half = 1;
 end = (const unsigned char *)((string2 + size2) < (string2 + stop - size1) ? (string2 + size2) : (string2 + stop - size1));
      }
  init_fastmap_sentinal:
    if (size)
      {
 fastmap_chr = ((search_direction == 1)
         ? *(end - 1)
         : *string);
 fastmap_val = fastmap[fastmap_chr];
 fastmap[fastmap_chr] = 1;
      }
    else
      {
 fastmap_chr = -1;
 fastmap_val = 0;
      }
    do
      {
 if (pos == end)
   goto fastmap_hit_bound;
 else
   {
     if (search_direction == 1)
       {
  if (fastmap_val)
    {
      for (;;)
        {
   while (!fastmap[*pos])
     ++pos;
   goto commence_a_matchin;
        }
    }
  else
    {
      for (;;)
        {
   while (!fastmap[*pos])
     ++pos;
   if (*pos != fastmap_chr)
     goto commence_a_matchin;
   else
     {
       ++pos;
       if (pos == end)
         goto fastmap_hit_bound;
     }
        }
    }
       }
     else
       {
  const unsigned char * bound = string - 1;
  if (fastmap_val)
    {
      for (;;)
        {
   while (!fastmap[*pos])
     --pos;
   goto commence_a_matchin;
        }
    }
  else
    {
      for (;;)
        {
   while (!fastmap[*pos])
     --pos;
   if ((*pos != fastmap_chr) || fastmap_val)
     goto commence_a_matchin;
   else
     {
       --pos;
       if (pos == bound)
         goto fastmap_hit_bound;
     }
        }
    }
       }
   }
      fastmap_hit_bound:
 {
   if ((search_direction == 1) && string2 && (half == 0))
     {
       string = (const unsigned char *)string2;
       size = size2;
       offset = size1;
       half = 1;
       end = (const unsigned char *)((string2 + size2) < (string2 + stop - size1) ? (string2 + size2) : (string2 + stop - size1));
       startpos = size1;
       pos = (const unsigned char *)string2;
       goto init_fastmap_sentinal;
     }
   else if ( string1
     && (search_direction == -1)
     && (half == 1))
     {
       string = (const unsigned char *)string1;
       size = size1;
       offset = 0;
       end = (const unsigned char *)string1 + size1;
       half = 0;
       startpos = size1 - 1;
       pos = (const unsigned char *)string1 + size1 - 1;
       goto init_fastmap_sentinal;
     }
   else if (search_direction == -1)
     goto finish;
 }
      commence_a_matchin:
 startpos = pos - string + offset;
 if (startpos == search_end)
   goto finish;
 last_l = last_r = 0;
 lparen[0] = startpos;
 {
   struct rx_superstate * super = start_super;
   struct rx_inx * ifr;
   const unsigned char * tst_pos = pos - 1;
   int tst_half = half;
   unsigned char c = nfa_choice;
   const unsigned char * tst_str_half = string;
   const unsigned char * tst_end_half = end;
   struct stack_chunk * counter_stack = 0;
   struct stack_chunk * backtrack_stack = 0;
   int backtrack_frame_bytes =
     (sizeof (struct backtrack_frame)
      + (rxb->match_regs_on_stack
  ? sizeof (regoff_t) * (num_regs + 1) * 2
  : 0));
   int chunk_bytes = backtrack_frame_bytes * 64;
   struct stack_chunk * free_chunks = 0;
   int test_ret = -1;
   while (1)
     {
       int inx;
     top_of_cycle:
       ifr = &super->transitions [c];
     recurse_test_match:
     restart:
       {
  struct rx_inx * next_tr_table = (struct rx_inx *)ifr->data;
  struct rx_inx * this_tr_table = super->transitions;
  while (next_tr_table)
    {
      this_tr_table = next_tr_table;
      ++tst_pos;
      if (tst_pos == tst_end_half)
        {
   if ( (tst_pos != abs_end)
       && string2
       && half == 0)
     {
       tst_str_half = (const unsigned char *)string2;
       tst_end_half = abs_end;
       tst_pos = (const unsigned char *)string2;
       tst_half = 1;
     }
   else
     {
       test_ret = 1;
       goto test_do_return;
     }
        }
      c = *tst_pos;
      ifr = this_tr_table + c;
      next_tr_table = (struct rx_inx *)ifr->data;
    }
  super =
    ((struct rx_superstate *)
     ((char *)this_tr_table
      - ((unsigned long)
         ((struct rx_superstate *)0)->transitions)));
       }
       inx = (int)ifr->inx;
       switch ((enum rx_opcode)inx)
  {
  case rx_do_side_effects:
    {
      struct rx_distinct_future * df =
        (struct rx_distinct_future *)ifr->data_2;
      struct rx_se_list * el = df->effects;
      while (el)
        {
   int effect = (int)el->car;
   if (effect < 0)
     {
       switch ((enum re_side_effects) effect)
         {
         case re_se_pushback:
    ifr = &df->future_frame;
    if (!ifr->data)
      {
        struct rx_superstate * sup = super;
        ((sup)->locks++);
        if (!rx_handle_cache_miss (&rxb->rx,
              super, c,
              ifr->data_2))
          {
     (--(sup)->locks);
     test_ret = 0;
     goto test_do_return;
          }
        (--(sup)->locks);
      }
    c = 't';
    super
      = ((struct rx_superstate *)
         ((char *)ifr->data
          - (long)(((struct rx_superstate *)0)
            ->transitions)));
    goto top_of_cycle;
    break;
         case re_se_push0:
    {
      struct counter_frame * old_cf
         = (counter_stack
     ? ((struct counter_frame *)
        counter_stack->sp)
     : 0);
      struct counter_frame * cf;
      if (!counter_stack || (counter_stack->bytes_left < (sizeof (struct counter_frame)))) { struct stack_chunk * new_chunk; if (free_chunks) { new_chunk = free_chunks; free_chunks = free_chunks->next_chunk; } else { new_chunk = (struct stack_chunk *)__builtin_alloca (chunk_bytes); if (!new_chunk) { ret_val = 0; goto test_do_return; } } new_chunk->sp = (char *)new_chunk + sizeof (struct stack_chunk); new_chunk->bytes_left = (chunk_bytes - (sizeof (struct counter_frame)) - sizeof (struct stack_chunk)); new_chunk->next_chunk = counter_stack; counter_stack = new_chunk; } else (counter_stack->sp += (sizeof (struct counter_frame))), (counter_stack->bytes_left -= (sizeof (struct counter_frame)));
      cf = ((struct counter_frame *)
     counter_stack->sp);
      cf->tag = re_se_iter;
      cf->val = 0;
      cf->inherited_from = 0;
      cf->cdr = old_cf;
      break;
    }
         case re_se_fail:
    goto test_do_return;
         case re_se_begbuf:
    if (!(string1 ? ((tst_half == 0) && ((unsigned char *)tst_pos == (unsigned char *)string1 - 1)) : ((unsigned char *)tst_pos == (unsigned char *)string2 - 1)))
      goto test_do_return;
    break;
         case re_se_endbuf:
    if (!(string2 ? ((tst_half == 1) && ((unsigned char *)tst_pos == ((unsigned char *)string2 + size2 - 1))) : ((unsigned char *)tst_pos == ((unsigned char *)string1 + size1 - 1))))
      goto test_do_return;
    break;
         case re_se_wordbeg:
    if ( (re_syntax_table[(string2 && (tst_half == 0) && ((tst_pos + 1) == ((unsigned char *)string1 + size1))) ? *(unsigned char *)string2 : ((string1 && (tst_half == 1) && ((tst_pos + 1) == (unsigned char *)string2 - 1)) ? *((unsigned char *)string1 + size1 - 1) : *(tst_pos + 1))] == 1)
        && ( (string1 ? ((tst_half == 0) && ((unsigned char *)tst_pos == (unsigned char *)string1 - 1)) : ((unsigned char *)tst_pos == (unsigned char *)string2 - 1))
     || !(re_syntax_table[(string2 && (tst_half == 0) && ((tst_pos) == ((unsigned char *)string1 + size1))) ? *(unsigned char *)string2 : ((string1 && (tst_half == 1) && ((tst_pos) == (unsigned char *)string2 - 1)) ? *((unsigned char *)string1 + size1 - 1) : *(tst_pos))] == 1)))
      break;
    else
      goto test_do_return;
         case re_se_wordend:
    if ( !(string1 ? ((tst_half == 0) && ((unsigned char *)tst_pos == (unsigned char *)string1 - 1)) : ((unsigned char *)tst_pos == (unsigned char *)string2 - 1))
        && (re_syntax_table[(string2 && (tst_half == 0) && ((tst_pos) == ((unsigned char *)string1 + size1))) ? *(unsigned char *)string2 : ((string1 && (tst_half == 1) && ((tst_pos) == (unsigned char *)string2 - 1)) ? *((unsigned char *)string1 + size1 - 1) : *(tst_pos))] == 1)
        && ((string2 ? ((tst_half == 1) && ((unsigned char *)tst_pos == ((unsigned char *)string2 + size2 - 1))) : ((unsigned char *)tst_pos == ((unsigned char *)string1 + size1 - 1)))
     || !(re_syntax_table[(string2 && (tst_half == 0) && ((tst_pos + 1) == ((unsigned char *)string1 + size1))) ? *(unsigned char *)string2 : ((string1 && (tst_half == 1) && ((tst_pos + 1) == (unsigned char *)string2 - 1)) ? *((unsigned char *)string1 + size1 - 1) : *(tst_pos + 1))] == 1)))
      break;
    else
      goto test_do_return;
         case re_se_wordbound:
    if (((string1 ? ((tst_half == 0) && ((unsigned char *)tst_pos == (unsigned char *)string1 - 1)) : ((unsigned char *)tst_pos == (unsigned char *)string2 - 1)) || (string2 ? ((tst_half == 1) && ((unsigned char *)tst_pos == ((unsigned char *)string2 + size2 - 1))) : ((unsigned char *)tst_pos == ((unsigned char *)string1 + size1 - 1))) || (re_syntax_table[(string2 && (tst_half == 0) && ((tst_pos) == ((unsigned char *)string1 + size1))) ? *(unsigned char *)string2 : ((string1 && (tst_half == 1) && ((tst_pos) == (unsigned char *)string2 - 1)) ? *((unsigned char *)string1 + size1 - 1) : *(tst_pos))] == 1) != (re_syntax_table[(string2 && (tst_half == 0) && ((tst_pos + 1) == ((unsigned char *)string1 + size1))) ? *(unsigned char *)string2 : ((string1 && (tst_half == 1) && ((tst_pos + 1) == (unsigned char *)string2 - 1)) ? *((unsigned char *)string1 + size1 - 1) : *(tst_pos + 1))] == 1)))
      break;
    else
      goto test_do_return;
         case re_se_notwordbound:
    if (!((string1 ? ((tst_half == 0) && ((unsigned char *)tst_pos == (unsigned char *)string1 - 1)) : ((unsigned char *)tst_pos == (unsigned char *)string2 - 1)) || (string2 ? ((tst_half == 1) && ((unsigned char *)tst_pos == ((unsigned char *)string2 + size2 - 1))) : ((unsigned char *)tst_pos == ((unsigned char *)string1 + size1 - 1))) || (re_syntax_table[(string2 && (tst_half == 0) && ((tst_pos) == ((unsigned char *)string1 + size1))) ? *(unsigned char *)string2 : ((string1 && (tst_half == 1) && ((tst_pos) == (unsigned char *)string2 - 1)) ? *((unsigned char *)string1 + size1 - 1) : *(tst_pos))] == 1) != (re_syntax_table[(string2 && (tst_half == 0) && ((tst_pos + 1) == ((unsigned char *)string1 + size1))) ? *(unsigned char *)string2 : ((string1 && (tst_half == 1) && ((tst_pos + 1) == (unsigned char *)string2 - 1)) ? *((unsigned char *)string1 + size1 - 1) : *(tst_pos + 1))] == 1)))
      break;
    else
      goto test_do_return;
         case re_se_hat:
    if ((string1 ? ((tst_half == 0) && ((unsigned char *)tst_pos == (unsigned char *)string1 - 1)) : ((unsigned char *)tst_pos == (unsigned char *)string2 - 1)))
      {
        if (rxb->not_bol)
          goto test_do_return;
        else
          break;
      }
    else
      {
        char pos_c = *tst_pos;
        if ( (translate[(unsigned char) (pos_c)]
         == translate[(unsigned char) ('\n')])
     && rxb->newline_anchor)
          break;
        else
          goto test_do_return;
      }
         case re_se_dollar:
    if ((string2 ? ((tst_half == 1) && ((unsigned char *)tst_pos == ((unsigned char *)string2 + size2 - 1))) : ((unsigned char *)tst_pos == ((unsigned char *)string1 + size1 - 1))))
      {
        if (rxb->not_eol)
          goto test_do_return;
        else
          break;
      }
    else
      {
        const unsigned char * next_pos
          = ((string2 && (tst_half == 0) &&
       (tst_pos
        == ((unsigned char *)
            string1 + size1 - 1)))
      ? (unsigned char *)string2
      : tst_pos + 1);
        if ( (translate[(unsigned char) (*next_pos)]
         == translate[(unsigned char) ('\n')])
     && rxb->newline_anchor)
          break;
        else
          goto test_do_return;
      }
         case re_se_try:
    break;
         case re_se_pushpos:
    {
      int urhere =
        ((int)(tst_pos - tst_str_half)
         + ((tst_half == 0) ? 0 : size1));
      struct counter_frame * old_cf
        = (counter_stack
           ? ((struct counter_frame *)
       counter_stack->sp)
           : 0);
      struct counter_frame * cf;
      if (!counter_stack || (counter_stack->bytes_left < (sizeof (struct counter_frame)))) { struct stack_chunk * new_chunk; if (free_chunks) { new_chunk = free_chunks; free_chunks = free_chunks->next_chunk; } else { new_chunk = (struct stack_chunk *)__builtin_alloca (chunk_bytes); if (!new_chunk) { ret_val = 0; goto test_do_return; } } new_chunk->sp = (char *)new_chunk + sizeof (struct stack_chunk); new_chunk->bytes_left = (chunk_bytes - (sizeof (struct counter_frame)) - sizeof (struct stack_chunk)); new_chunk->next_chunk = counter_stack; counter_stack = new_chunk; } else (counter_stack->sp += (sizeof (struct counter_frame))), (counter_stack->bytes_left -= (sizeof (struct counter_frame)));
      cf = ((struct counter_frame *)
     counter_stack->sp);
      cf->tag = re_se_pushpos;
      cf->val = urhere;
      cf->inherited_from = 0;
      cf->cdr = old_cf;
      break;
    }
         case re_se_chkpos:
    {
      int urhere =
        ((int)(tst_pos - tst_str_half)
         + ((tst_half == 0) ? 0 : size1));
      struct counter_frame * cf
        = ((struct counter_frame *)
           counter_stack->sp);
      if (cf->val == urhere)
        goto test_do_return;
      cf->val = urhere;
      break;
    }
    break;
         case re_se_poppos:
    if (counter_stack->sp == ((char *)counter_stack + sizeof(*counter_stack))) { struct stack_chunk * new_chunk = counter_stack->next_chunk; counter_stack->next_chunk = free_chunks; free_chunks = counter_stack; counter_stack = new_chunk; } else (counter_stack->sp -= sizeof (struct counter_frame)), (counter_stack->bytes_left += sizeof (struct counter_frame));
    break;
         case re_se_at_dot:
         case re_se_syntax:
         case re_se_not_syntax:
    break;
         case re_se_win:
         case re_se_lparen:
         case re_se_rparen:
         case re_se_backref:
         case re_se_iter:
         case re_se_end_iter:
         case re_se_tv:
         case re_floogle_flap:
    ret_val = 0;
    goto test_do_return;
         }
     }
   else
     {
       switch (rxb->se_params [effect].se)
         {
         case re_se_win:
    {
      int urhere =
        ((int)(tst_pos - tst_str_half)
         + ((tst_half == 0)
     ? 0 : size1));
      if ( (best_last_r < 0)
          || (urhere + 1 > best_rparen[0]))
        {
          int x;
          for (x = 0; x <= last_l; ++x)
     best_lparen[x] = lparen[x];
          best_last_l = last_l;
          for (x = 0; x <= last_r; ++x)
     best_rparen[x] = rparen[x];
          best_rparen[0] = urhere + 1;
          best_last_r = last_r;
        }
      if (first_found)
        {
          test_ret = -2;
          goto test_do_return;
        }
    }
    break;
         case re_se_lparen:
    {
      int urhere =
        ((int)(tst_pos - tst_str_half)
         + ((tst_half == 0) ? 0 : size1));
      int reg = rxb->se_params [effect].op1;
        {
          lparen[reg] = urhere + 1;
          if (last_l < reg)
     while (++last_l < reg)
       lparen[last_l] = -1;
        }
      break;
    }
         case re_se_rparen:
    {
      int urhere =
        ((int)(tst_pos - tst_str_half)
         + ((tst_half == 0) ? 0 : size1));
      int reg = rxb->se_params [effect].op1;
      rparen[reg] = urhere + 1;
      if (last_r < reg)
        {
          while (++last_r < reg)
     rparen[last_r] = -1;
        }
      break;
    }
         case re_se_backref:
    {
      int reg = rxb->se_params [effect].op1;
      if (reg > last_r || rparen[reg] < 0)
        goto test_do_return;
      {
        const unsigned char * there
          = tst_str_half + lparen[reg];
        const unsigned char * last
          = tst_str_half + rparen[reg];
        const unsigned char * here = tst_pos + 1;
        if ((here == tst_end_half) && string2
     && (tst_str_half
         == (unsigned char *) string1)
     && (tst_end_half != abs_end))
          {
     here = (unsigned char *)string2;
     tst_end_half = abs_end;
          }
        while (there < last && here < tst_end_half)
          if (translate[(unsigned char) (*there)]
       != translate[(unsigned char) (*here)])
     goto test_do_return;
          else
     {
       ++there; ++here;
       if ((here == tst_end_half) && string2
           && (tst_str_half
        == (unsigned char *)string1)
           && (tst_end_half != abs_end))
         {
           here = (unsigned char *)string2;
           tst_end_half = abs_end;
           tst_half = 1;
         }
     }
        if (there != last)
          goto test_do_return;
        tst_pos = here - 1;
        if ((here == (unsigned char *)string2)
     && (unsigned char *)string1)
          {
     tst_pos = ((unsigned char *)string1
         + size1 - 1);
     tst_end_half = tst_pos + 1;
     tst_half = 0;
          }
      }
      break;
    }
         case re_se_iter:
    {
      struct counter_frame * csp
        = ((struct counter_frame *)
           counter_stack->sp);
      if (csp->val == rxb->se_params[effect].op2)
        goto test_do_return;
      else
        ++csp->val;
      break;
    }
         case re_se_end_iter:
    {
      struct counter_frame * csp
        = ((struct counter_frame *)
           counter_stack->sp);
      if (csp->val < rxb->se_params[effect].op1)
        goto test_do_return;
      else
        {
          struct counter_frame * source = csp;
          while (source->inherited_from)
     source = source->inherited_from;
          if (!source || !source->cdr)
     {
       if (counter_stack->sp == ((char *)counter_stack + sizeof(*counter_stack))) { struct stack_chunk * new_chunk = counter_stack->next_chunk; counter_stack->next_chunk = free_chunks; free_chunks = counter_stack; counter_stack = new_chunk; } else (counter_stack->sp -= sizeof(struct counter_frame)), (counter_stack->bytes_left += sizeof(struct counter_frame));
     }
          else
     {
       source = source->cdr;
       csp->val = source->val;
       csp->tag = source->tag;
       csp->cdr = 0;
       csp->inherited_from = source;
     }
        }
      break;
    }
         case re_se_tv:
    break;
         case re_se_try:
         case re_se_pushback:
         case re_se_push0:
         case re_se_pushpos:
         case re_se_chkpos:
         case re_se_poppos:
         case re_se_at_dot:
         case re_se_syntax:
         case re_se_not_syntax:
         case re_se_begbuf:
         case re_se_hat:
         case re_se_wordbeg:
         case re_se_wordbound:
         case re_se_notwordbound:
         case re_se_wordend:
         case re_se_endbuf:
         case re_se_dollar:
         case re_se_fail:
         case re_floogle_flap:
    ret_val = 0;
    goto test_do_return;
         }
     }
   el = el->cdr;
        }
      ifr = &df->future_frame;
      goto restart;
    }
  case rx_backtrack_point:
    {
      struct backtrack_frame * bf;
      if (!backtrack_stack || (backtrack_stack->bytes_left < (backtrack_frame_bytes))) { struct stack_chunk * new_chunk; if (free_chunks) { new_chunk = free_chunks; free_chunks = free_chunks->next_chunk; } else { new_chunk = (struct stack_chunk *)__builtin_alloca (chunk_bytes); if (!new_chunk) { ret_val = 0; goto test_do_return; } } new_chunk->sp = (char *)new_chunk + sizeof (struct stack_chunk); new_chunk->bytes_left = (chunk_bytes - (backtrack_frame_bytes) - sizeof (struct stack_chunk)); new_chunk->next_chunk = backtrack_stack; backtrack_stack = new_chunk; } else (backtrack_stack->sp += (backtrack_frame_bytes)), (backtrack_stack->bytes_left -= (backtrack_frame_bytes));
      bf = ((struct backtrack_frame *)
     backtrack_stack->sp);
      {
        bf->stk_super = super;
        ((super)->locks++);
        bf->stk_tst_pos = tst_pos;
        bf->stk_tst_half = tst_half;
        bf->stk_c = c;
        bf->stk_tst_str_half = tst_str_half;
        bf->stk_tst_end_half = tst_end_half;
        bf->stk_last_l = last_l;
        bf->stk_last_r = last_r;
        bf->df = ((struct rx_super_edge *)ifr->data_2)->options;
        bf->first_df = bf->df;
        bf->counter_stack_sp = (counter_stack
           ? counter_stack->sp
           : 0);
        bf->stk_test_ret = test_ret;
        if (rxb->match_regs_on_stack)
   {
     int x;
     regoff_t * stk =
       (regoff_t *)((char *)bf + sizeof (*bf));
     for (x = 0; x <= last_l; ++x)
       stk[x] = lparen[x];
     stk += x;
     for (x = 0; x <= last_r; ++x)
       stk[x] = rparen[x];
   }
      }
    while_non_det_options:
      if (bf->df->next_same_super_edge[0] == bf->first_df)
        {
   ifr = (bf->df->effects
          ? &bf->df->side_effects_frame
          : &bf->df->future_frame);
   (--(super)->locks);
   if (backtrack_stack->sp == ((char *)backtrack_stack + sizeof(*backtrack_stack))) { struct stack_chunk * new_chunk = backtrack_stack->next_chunk; backtrack_stack->next_chunk = free_chunks; free_chunks = backtrack_stack; backtrack_stack = new_chunk; } else (backtrack_stack->sp -= backtrack_frame_bytes), (backtrack_stack->bytes_left += backtrack_frame_bytes);
   goto restart;
        }
      else
        {
   if (counter_stack)
     {
       struct counter_frame * old_cf
         = ((struct counter_frame *)counter_stack->sp);
       struct counter_frame * cf;
       if (!counter_stack || (counter_stack->bytes_left < (sizeof (struct counter_frame)))) { struct stack_chunk * new_chunk; if (free_chunks) { new_chunk = free_chunks; free_chunks = free_chunks->next_chunk; } else { new_chunk = (struct stack_chunk *)__builtin_alloca (chunk_bytes); if (!new_chunk) { ret_val = 0; goto test_do_return; } } new_chunk->sp = (char *)new_chunk + sizeof (struct stack_chunk); new_chunk->bytes_left = (chunk_bytes - (sizeof (struct counter_frame)) - sizeof (struct stack_chunk)); new_chunk->next_chunk = counter_stack; counter_stack = new_chunk; } else (counter_stack->sp += (sizeof (struct counter_frame))), (counter_stack->bytes_left -= (sizeof (struct counter_frame)));
       cf = ((struct counter_frame *)counter_stack->sp);
       cf->tag = old_cf->tag;
       cf->val = old_cf->val;
       cf->inherited_from = old_cf;
       cf->cdr = 0;
     }
   ifr = (bf->df->effects
          ? &bf->df->side_effects_frame
          : &bf->df->future_frame);
   goto recurse_test_match;
        }
    test_do_return:
      if (!backtrack_stack)
        {
   if (test_ret)
     goto return_from_test_match;
   else
     goto error_in_testing_match;
        }
      bf = ((struct backtrack_frame *)
     backtrack_stack->sp);
      while (counter_stack
      && (!bf->counter_stack_sp
          || (bf->counter_stack_sp != counter_stack->sp)))
        {
   if (counter_stack->sp == ((char *)counter_stack + sizeof(*counter_stack))) { struct stack_chunk * new_chunk = counter_stack->next_chunk; counter_stack->next_chunk = free_chunks; free_chunks = counter_stack; counter_stack = new_chunk; } else (counter_stack->sp -= sizeof (struct counter_frame)), (counter_stack->bytes_left += sizeof (struct counter_frame));
        }
      if (!test_ret)
        {
   if (backtrack_stack->sp == ((char *)backtrack_stack + sizeof(*backtrack_stack))) { struct stack_chunk * new_chunk = backtrack_stack->next_chunk; backtrack_stack->next_chunk = free_chunks; free_chunks = backtrack_stack; backtrack_stack = new_chunk; } else (backtrack_stack->sp -= backtrack_frame_bytes), (backtrack_stack->bytes_left += backtrack_frame_bytes);
   goto test_do_return;
        }
      if ((test_ret == -2) && first_found)
        {
   (--(bf->stk_super)->locks);
   if (backtrack_stack->sp == ((char *)backtrack_stack + sizeof(*backtrack_stack))) { struct stack_chunk * new_chunk = backtrack_stack->next_chunk; backtrack_stack->next_chunk = free_chunks; free_chunks = backtrack_stack; backtrack_stack = new_chunk; } else (backtrack_stack->sp -= backtrack_frame_bytes), (backtrack_stack->bytes_left += backtrack_frame_bytes);
   goto test_do_return;
        }
      if (bf->stk_test_ret < 0)
        test_ret = bf->stk_test_ret;
      last_l = bf->stk_last_l;
      last_r = bf->stk_last_r;
      bf->df = bf->df->next_same_super_edge[0];
      super = bf->stk_super;
      tst_pos = bf->stk_tst_pos;
      tst_half = bf->stk_tst_half;
      c = bf->stk_c;
      tst_str_half = bf->stk_tst_str_half;
      tst_end_half = bf->stk_tst_end_half;
      if (rxb->match_regs_on_stack)
        {
   int x;
   regoff_t * stk =
     (regoff_t *)((char *)bf + sizeof (*bf));
   for (x = 0; x <= last_l; ++x)
     lparen[x] = stk[x];
   stk += x;
   for (x = 0; x <= last_r; ++x)
     rparen[x] = stk[x];
        }
      goto while_non_det_options;
    }
  case rx_cache_miss:
    ifr = rx_handle_cache_miss (&rxb->rx, super, c, ifr->data_2);
    if (!ifr)
      {
        test_ret = 0;
        goto test_do_return;
      }
    goto restart;
  case rx_backtrack:
    goto test_do_return;
  case rx_next_char:
  case rx_error_inx:
  case rx_num_instructions:
    ret_val = 0;
    goto test_do_return;
  }
     }
 }
      error_in_testing_match:
 ret_val = -2;
 goto finish;
      return_from_test_match:
 if (best_last_l >= 0)
   {
     if (regs && (regs->start != best_lparen))
       {
  memcpy ((regs->start), (best_lparen), (regs->num_regs * sizeof (int)));
  memcpy ((regs->end), (best_rparen), (regs->num_regs * sizeof (int)));
       }
     if (regs && !rxb->no_sub)
       {
  int q;
  int bound = (regs->num_regs > num_regs
        ? regs->num_regs
        : num_regs);
  regoff_t * s = regs->start;
  regoff_t * e = regs->end;
  for (q = best_last_l + 1; q < bound; ++q)
    s[q] = e[q] = -1;
       }
     ret_val = best_lparen[0];
     goto finish;
   }
 pos += search_direction;
 startpos += search_direction;
      } while (startpos < search_end);
  finish:
    if (fastmap_chr >= 0)
      fastmap[fastmap_chr] = fastmap_val;
    if (start_super)
      (--(start_super)->locks);
    return ret_val;
  }
}
int
re_search (struct re_pattern_buffer * rxb, const char *string,
    int size, int startpos, int range,
    struct re_registers *regs)
{
  return re_search_2 (rxb, 0, 0, string, size, startpos, range, regs, size);
}
int
re_match_2 (struct re_pattern_buffer * rxb,
     const char * string1, int size1,
     const char * string2, int size2,
     int pos, struct re_registers *regs, int stop)
{
  struct re_registers some_regs;
  regoff_t start;
  regoff_t end;
  int srch;
  int save = rxb->regs_allocated;
  struct re_registers * regs_to_pass = regs;
  if (!regs)
    {
      some_regs.start = &start;
      some_regs.end = &end;
      some_regs.num_regs = 1;
      regs_to_pass = &some_regs;
      rxb->regs_allocated = 2;
    }
  srch = re_search_2 (rxb, string1, size1, string2, size2,
        pos, 1, regs_to_pass, stop);
  if (regs_to_pass != regs)
    rxb->regs_allocated = save;
  if (srch < 0)
    return srch;
  return regs_to_pass->end[0] - regs_to_pass->start[0];
}
int
re_match (struct re_pattern_buffer * rxb,
   const char * string,
   int size, int pos,
   struct re_registers *regs)
{
  return re_match_2 (rxb, string, size, 0, 0, pos, regs, size);
}
reg_syntax_t re_syntax_options = 0;
reg_syntax_t
re_set_syntax (reg_syntax_t syntax)
{
  reg_syntax_t ret = re_syntax_options;
  re_syntax_options = syntax;
  return ret;
}
void
re_set_registers (struct re_pattern_buffer *bufp,
    struct re_registers *regs,
    unsigned num_regs,
    regoff_t * starts, regoff_t * ends)
{
  if (num_regs)
    {
      bufp->regs_allocated = 1;
      regs->num_regs = num_regs;
      regs->start = starts;
      regs->end = ends;
    }
  else
    {
      bufp->regs_allocated = 0;
      regs->num_regs = 0;
      regs->start = regs->end = (regoff_t) 0;
    }
}
static int
cplx_se_sublist_len (struct rx_se_list * list)
{
  int x = 0;
  while (list)
    {
      if ((int)list->car >= 0)
 ++x;
      list = list->cdr;
    }
  return x;
}
static int
posix_se_list_order (struct rx * rx,
       struct rx_se_list * a, struct rx_se_list * b)
{
  int al = cplx_se_sublist_len (a);
  int bl = cplx_se_sublist_len (b);
  if (!al && !bl)
    return ((a == b)
     ? 0
     : ((a < b) ? -1 : 1));
  else if (!al)
    return -1;
  else if (!bl)
    return 1;
  else
    {
      rx_side_effect * av = ((rx_side_effect *)
        __builtin_alloca (sizeof (rx_side_effect) * (al + 1)));
      rx_side_effect * bv = ((rx_side_effect *)
        __builtin_alloca (sizeof (rx_side_effect) * (bl + 1)));
      struct rx_se_list * ap = a;
      struct rx_se_list * bp = b;
      int ai, bi;
      for (ai = al - 1; ai >= 0; --ai)
 {
   while ((int)ap->car < 0)
     ap = ap->cdr;
   av[ai] = ap->car;
   ap = ap->cdr;
 }
      av[al] = (rx_side_effect)-2;
      for (bi = bl - 1; bi >= 0; --bi)
 {
   while ((int)bp->car < 0)
     bp = bp->cdr;
   bv[bi] = bp->car;
   bp = bp->cdr;
 }
      bv[bl] = (rx_side_effect)-1;
      {
 int ret;
 int x = 0;
 while (av[x] == bv[x])
   ++x;
 ret = ((av[x] < bv[x]) ? -1 : 1);
 return ret;
      }
    }
}
const char *
re_compile_pattern (const char *pattern,
      int length,
      struct re_pattern_buffer * rxb)
{
  reg_errcode_t ret;
  rxb->regs_allocated = 0;
  rxb->no_sub = 0;
  rxb->rx.local_cset_size = 256;
  rxb->newline_anchor = 1;
  rxb->re_nsub = 0;
  rxb->start = 0;
  rxb->se_params = 0;
  rxb->rx.nodec = 0;
  rxb->rx.epsnodec = 0;
  rxb->rx.instruction_table = 0;
  rxb->rx.nfa_states = 0;
  rxb->rx.se_list_cmp = posix_se_list_order;
  rxb->rx.start_set = 0;
  ret = rx_compile (pattern, length, re_syntax_options, rxb);
  __builtin_alloca (0);
  return rx_error_msg[(int) ret];
}
int
re_compile_fastmap (struct re_pattern_buffer * rxb)
{
  rx_blow_up_fastmap (rxb);
  return 0;
}
int
regcomp (regex_t * preg, const char * pattern, int cflags)
{
  reg_errcode_t ret;
  unsigned syntax
    = cflags & 1 ? (((((1) << 1) << 1) | (((((((1) << 1) << 1) << 1) << 1) << 1) << 1) | ((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) | ((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) | (((((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)) | ((((1) << 1) << 1) << 1) | (((((1) << 1) << 1) << 1) << 1) | (((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) | ((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) | ((((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) | ((((((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)) : (((((1) << 1) << 1) | (((((((1) << 1) << 1) << 1) << 1) << 1) << 1) | ((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) | ((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) | (((((((((((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1)) | ((1) << 1));
  preg->buffer = 0;
  preg->allocated = 0;
  preg->fastmap = malloc (256);
  if (!preg->fastmap)
    return REG_ESPACE;
  preg->fastmap_accurate = 0;
  if (cflags & (1 << 1))
    {
      unsigned i;
      preg->translate = (char *) malloc (256);
      if (!preg->translate)
        return (int) REG_ESPACE;
      for (i = 0; i < (1 << 8); i++)
        preg->translate[i] = ((*__ctype_b_loc ())[(int) ((i))] & (unsigned short int) _ISupper) ? tolower (i) : i;
    }
  else
    preg->translate = 0;
  if (cflags & ((1 << 1) << 1))
    {
      syntax &= ~(((((((1) << 1) << 1) << 1) << 1) << 1) << 1);
      syntax |= (((((((((1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1);
      preg->newline_anchor = 1;
    }
  else
    preg->newline_anchor = 0;
  preg->no_sub = !!(cflags & (((1 << 1) << 1) << 1));
  preg->re_nsub = 0;
  preg->start = 0;
  preg->se_params = 0;
  preg->rx.nodec = 0;
  preg->rx.epsnodec = 0;
  preg->rx.instruction_table = 0;
  preg->rx.nfa_states = 0;
  preg->rx.local_cset_size = 256;
  preg->rx.start = 0;
  preg->rx.se_list_cmp = posix_se_list_order;
  preg->rx.start_set = 0;
  ret = rx_compile (pattern, strlen (pattern), syntax, preg);
  __builtin_alloca (0);
  if (ret == REG_ERPAREN) ret = REG_EPAREN;
  return (int) ret;
}
int
regexec (const regex_t *preg, const char *string,
  size_t nmatch, regmatch_t pmatch[],
  int eflags)
{
  int ret;
  struct re_registers regs;
  regex_t private_preg;
  int len = strlen (string);
  boolean want_reg_info = !preg->no_sub && nmatch > 0;
  private_preg = *preg;
  private_preg.not_bol = !!(eflags & 1);
  private_preg.not_eol = !!(eflags & (1 << 1));
  private_preg.regs_allocated = 2;
  if (want_reg_info)
    {
      regs.num_regs = nmatch;
      regs.start = ((regoff_t *) malloc ((nmatch) * sizeof (regoff_t)));
      regs.end = ((regoff_t *) malloc ((nmatch) * sizeof (regoff_t)));
      if (regs.start == 0 || regs.end == 0)
        return (int) REG_NOMATCH;
    }
  ret = re_search (&private_preg,
     string, len,
                                0,
                  len,
                   want_reg_info ? &regs : (struct re_registers *) 0);
  if (want_reg_info)
    {
      if (ret >= 0)
        {
          unsigned r;
          for (r = 0; r < nmatch; r++)
            {
              pmatch[r].rm_so = regs.start[r];
              pmatch[r].rm_eo = regs.end[r];
            }
        }
      free (regs.start);
      free (regs.end);
    }
  return ret >= 0 ? (int) REG_NOERROR : (int) REG_NOMATCH;
}
size_t
regerror (int errcode, const regex_t *preg,
   char *errbuf, size_t errbuf_size)
{
  const char *msg
    = rx_error_msg[errcode] == 0 ? "Success" : rx_error_msg[errcode];
  size_t msg_size = strlen (msg) + 1;
  if (errbuf_size != 0)
    {
      if (msg_size > errbuf_size)
        {
          strncpy (errbuf, msg, errbuf_size - 1);
          errbuf[errbuf_size - 1] = 0;
        }
      else
        strcpy (errbuf, msg);
    }
  return msg_size;
}
void
regfree (regex_t *preg)
{
  if (preg->buffer != 0)
    free (preg->buffer);
  preg->buffer = 0;
  preg->allocated = 0;
  if (preg->fastmap != 0)
    free (preg->fastmap);
  preg->fastmap = 0;
  preg->fastmap_accurate = 0;
   if (preg->translate != 0)
    free (preg->translate);
  preg->translate = 0;
}
