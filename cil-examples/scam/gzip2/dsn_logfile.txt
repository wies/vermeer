#line 1 "gzip.preprocessed.c"
extern char *optarg ;
#line 2
extern int optind ;
#line 12
extern int getopt_long(int argc , char * const  *argv , char const   *shortopts , struct option  const  *longopts , int *longind ) ;
#line 180
extern int _IO_putc(int __c , _IO_FILE *__fp ) ;
#line 202
extern struct _IO_FILE *stdin ;
#line 203
extern struct _IO_FILE *stdout ;
#line 204
extern struct _IO_FILE *stderr ;
#line 221
extern int fflush(FILE *__stream ) ;
#line 244
extern int fprintf(FILE * __restrict  __stream , char const   * __restrict  __format  , ...) ;
#line 246
extern int printf(char const   * __restrict  __format  , ...) ;
#line 313
extern char *fgets(char * __restrict  __s , int __n , FILE * __restrict  __stream ) ;
#line 359
extern void perror(char const   *__s ) ;
#line 363
extern  __attribute__((__nothrow__)) int ( __attribute__((__leaf__)) fileno)(FILE *__stream ) ;
#line 374
extern  __attribute__((__nothrow__)) void *( __attribute__((__nonnull__(1,2), __leaf__)) memcpy)(void * __restrict  __dest , void const   * __restrict  __src , size_t __n ) ;
#line 384
extern  __attribute__((__nothrow__)) void *( __attribute__((__nonnull__(1), __leaf__)) memset)(void *__s , int __c , size_t __n ) ;
#line 385
extern  __attribute__((__nothrow__)) int ( __attribute__((__nonnull__(1,2), __leaf__)) memcmp)(void const   *__s1 , void const   *__s2 , size_t __n )  __attribute__((__pure__)) ;
#line 391
extern  __attribute__((__nothrow__)) char *( __attribute__((__nonnull__(1,2), __leaf__)) strcpy)(char * __restrict  __dest , char const   * __restrict  __src ) ;
#line 393
extern  __attribute__((__nothrow__)) char *( __attribute__((__nonnull__(1,2), __leaf__)) strncpy)(char * __restrict  __dest , char const   * __restrict  __src , size_t __n ) ;
#line 396
extern  __attribute__((__nothrow__)) char *( __attribute__((__nonnull__(1,2), __leaf__)) strcat)(char * __restrict  __dest , char const   * __restrict  __src ) ;
#line 400
extern  __attribute__((__nothrow__)) int ( __attribute__((__nonnull__(1,2), __leaf__)) strcmp)(char const   *__s1 , char const   *__s2 )  __attribute__((__pure__)) ;
#line 402
extern  __attribute__((__nothrow__)) int ( __attribute__((__nonnull__(1,2), __leaf__)) strncmp)(char const   *__s1 , char const   *__s2 , size_t __n )  __attribute__((__pure__)) ;
#line 430
extern  __attribute__((__nothrow__)) char *( __attribute__((__nonnull__(1), __leaf__)) strrchr)(char const   *__s , int __c )  __attribute__((__pure__)) ;
#line 434
extern  __attribute__((__nothrow__)) size_t ( __attribute__((__nonnull__(1,2), __leaf__)) strcspn)(char const   *__s , char const   *__reject )  __attribute__((__pure__)) ;
#line 436
extern  __attribute__((__nothrow__)) size_t ( __attribute__((__nonnull__(1,2), __leaf__)) strspn)(char const   *__s , char const   *__accept )  __attribute__((__pure__)) ;
#line 453
extern  __attribute__((__nothrow__)) size_t ( __attribute__((__nonnull__(1), __leaf__)) strlen)(char const   *__s )  __attribute__((__pure__)) ;
#line 496
int method ;
#line 497 "gzip.preprocessed.c"
uch inbuf[32832]  ;
#line 498 "gzip.preprocessed.c"
uch outbuf[18432]  ;
#line 499 "gzip.preprocessed.c"
ush d_buf[32768]  ;
#line 500 "gzip.preprocessed.c"
uch window[65536L]  ;
#line 501 "gzip.preprocessed.c"
ush prev[1L << 16]  ;
#line 502 "gzip.preprocessed.c"
unsigned int insize  ;
#line 503 "gzip.preprocessed.c"
unsigned int inptr  ;
#line 504 "gzip.preprocessed.c"
unsigned int outcnt  ;
#line 505 "gzip.preprocessed.c"
long bytes_in  ;
#line 506 "gzip.preprocessed.c"
long bytes_out  ;
#line 507 "gzip.preprocessed.c"
long header_bytes  ;
#line 508 "gzip.preprocessed.c"
int ifd  ;
#line 509 "gzip.preprocessed.c"
int ofd  ;
#line 510 "gzip.preprocessed.c"
char ifname[1024]  ;
#line 511 "gzip.preprocessed.c"
char ofname[1024]  ;
#line 512 "gzip.preprocessed.c"
char *progname  ;
#line 513 "gzip.preprocessed.c"
long time_stamp  ;
#line 514 "gzip.preprocessed.c"
long ifile_size  ;
#line 516 "gzip.preprocessed.c"
int decrypt  ;
#line 517
int exit_code ;
#line 518
int verbose ;
#line 519
int quiet ;
#line 520
int level ;
#line 521
int test ;
#line 522
int to_stdout ;
#line 523 "gzip.preprocessed.c"
int save_orig_name  ;
#line 524
int zip(int in , int out ) ;
#line 525
int file_read(char *buf , unsigned int size ) ;
#line 526
int unzip(int in , int out ) ;
#line 527
int check_zipfile(int in ) ;
#line 528
int unpack(int in , int out ) ;
#line 529
int unlzh(int in , int out ) ;
#line 530
void abort_gzip(void) ;
#line 531
void lm_init(int pack_level , ush *flags ) ;
#line 532
ulg deflate(void) ;
#line 533
void ct_init(ush *attr , int *methodp ) ;
#line 534
int ct_tally(int dist , int lc ) ;
#line 535
ulg flush_block(char *buf , ulg stored_len , int eof ) ;
#line 536
void bi_init(file_t zipfile ) ;
#line 537
void send_bits(int value , int length ) ;
#line 538
unsigned int bi_reverse(unsigned int code , int len ) ;
#line 539
void bi_windup(void) ;
#line 540
void copy_block(char *buf , unsigned int len , int header ) ;
#line 541 "gzip.preprocessed.c"
int (*read_buf)(char *buf , unsigned int size )  ;
#line 542
int copy(int in , int out ) ;
#line 543
ulg updcrc(uch *s , unsigned int n ) ;
#line 544
void clear_bufs(void) ;
#line 545
int fill_inbuf(int eof_ok ) ;
#line 546
void flush_outbuf(void) ;
#line 547
void flush_window(void) ;
#line 548
void write_buf(int fd , voidp buf , unsigned int cnt ) ;
#line 549
char *strlwr(char *s ) ;
#line 550
char *basename(char *fname ) ;
#line 551
void make_simple_name(char *name ) ;
#line 552
char *add_envopt(int *argcp , char ***argvp , char *env ) ;
#line 553
void error(char *m ) ;
#line 554
void warn(char *a , char *b ) ;
#line 555
void read_error(void) ;
#line 556
void write_error(void) ;
#line 557
void display_ratio(long num , long den , FILE *file ) ;
#line 558
voidp xmalloc(unsigned int size ) ;
#line 559
int inflate(void) ;
#line 560
int maxbits ;
#line 561
int block_mode ;
#line 562
int lzw(int in , int out ) ;
#line 563
int unlzw(int in , int out ) ;
#line 580
extern  __attribute__((__nothrow__)) unsigned short const   **( __attribute__((__leaf__)) __ctype_b_loc)(void)  __attribute__((__const__)) ;
#line 958
extern  __attribute__((__nothrow__)) __sighandler_t ( __attribute__((__leaf__)) signal)(int __sig , void (*__handler)(int  ) ) ;
#line 1170
extern  __attribute__((__nothrow__)) int ( __attribute__((__nonnull__(1,2), __leaf__)) stat)(char const   * __restrict  __file , struct stat * __restrict  __buf ) ;
#line 1172
extern  __attribute__((__nothrow__)) int ( __attribute__((__nonnull__(2), __leaf__)) fstat)(int __fd , struct stat *__buf ) ;
#line 1176
extern  __attribute__((__nothrow__)) int ( __attribute__((__nonnull__(1,2), __leaf__)) lstat)(char const   * __restrict  __file , struct stat * __restrict  __buf ) ;
#line 1178
extern  __attribute__((__nothrow__)) int ( __attribute__((__nonnull__(1), __leaf__)) chmod)(char const   *__file , __mode_t __mode ) ;
#line 1220
extern  __attribute__((__nothrow__)) int *( __attribute__((__leaf__)) __errno_location)(void)  __attribute__((__const__)) ;
#line 1222 "gzip.preprocessed.c"
static file_t zfile  ;
#line 1223 "gzip.preprocessed.c"
static unsigned short bi_buf  ;
#line 1224 "gzip.preprocessed.c"
static int bi_valid  ;
#line 1287 "gzip.preprocessed.c"
ulg window_size   = 65536UL;
#line 1288 "gzip.preprocessed.c"
long block_start  ;
#line 1289 "gzip.preprocessed.c"
static unsigned int ins_h  ;
#line 1290 "gzip.preprocessed.c"
unsigned int prev_length  ;
#line 1291 "gzip.preprocessed.c"
unsigned int strstart  ;
#line 1292 "gzip.preprocessed.c"
unsigned int match_start  ;
#line 1293 "gzip.preprocessed.c"
static int eofile  ;
#line 1294 "gzip.preprocessed.c"
static unsigned int lookahead  ;
#line 1295 "gzip.preprocessed.c"
unsigned int max_chain_length  ;
#line 1296 "gzip.preprocessed.c"
static unsigned int max_lazy_match  ;
#line 1297 "gzip.preprocessed.c"
static int compr_level  ;
#line 1298 "gzip.preprocessed.c"
unsigned int good_match  ;
#line 1305 "gzip.preprocessed.c"
int nice_match  ;
#line 1306 "gzip.preprocessed.c"
static config configuration_table[10]   = 
#line 1306
  {{(ush )0, (ush )0, (ush )0, (ush )0}, {(ush )4, (ush )4, (ush )8, (ush )4}, {(ush )4, (ush )5, (ush )16, (ush )8}, {(ush )4, (ush )6, (ush )32, (ush )32}, {(ush )4, (ush )4, (ush )16, (ush )16}, {(ush )8, (ush )16, (ush )32, (ush )32}, {(ush )8, (ush )16, (ush )128, (ush )128}, {(ush )8, (ush )32, (ush )128, (ush )256}, {(ush )32, (ush )128, (ush )258, (ush )1024}, {(ush )32, (ush )258, (ush )258, (ush )4096}};
#line 1317
static void fill_window(void) ;
#line 1318
static ulg deflate_fast(void) ;
#line 1319
int longest_match(IPos cur_match ) ;
#line 1562
extern  __attribute__((__nothrow__)) int ( __attribute__((__nonnull__(1), __leaf__)) atoi)(char const   *__nptr )  __attribute__((__pure__)) ;
#line 1690
extern  __attribute__((__nothrow__)) void *( __attribute__((__leaf__)) malloc)(size_t __size )  __attribute__((__malloc__)) ;
#line 1691
extern  __attribute__((__nothrow__)) void *( __attribute__((__leaf__)) calloc)(size_t __nmemb , size_t __size )  __attribute__((__malloc__)) ;
#line 1697
extern  __attribute__((__nothrow__)) void ( __attribute__((__leaf__)) free)(void *__ptr ) ;
#line 1713
extern  __attribute__((__nothrow__, __noreturn__)) void ( __attribute__((__leaf__)) exit)(int __status ) ;
#line 1719
extern  __attribute__((__nothrow__)) char *( __attribute__((__nonnull__(1), __leaf__)) getenv)(char const   *__name ) ;
#line 1815
int huft_build(unsigned int *b , unsigned int n , unsigned int s , ush *d , ush *e , struct huft **t , int *m ) ;
#line 1816
int huft_free(struct huft *t ) ;
#line 1817
int inflate_codes(struct huft *tl , struct huft *td , int bl , int bd ) ;
#line 1818
int inflate_stored(void) ;
#line 1819
int inflate_fixed(void) ;
#line 1820
int inflate_dynamic(void) ;
#line 1821
int inflate_block(int *e ) ;
#line 1823 "gzip.preprocessed.c"
static unsigned int border[19]   = 
#line 1823
  {16U, 17U, 18U, 0U, 8U, 7U, 9U, 6U, 10U, 5U, 11U, 4U, 12U, 3U, 13U, 2U, 14U, 1U, 15U};
#line 1825 "gzip.preprocessed.c"
static ush cplens[31]   = 
#line 1825
  {(ush )3, (ush )4, (ush )5, (ush )6, (ush )7, (ush )8, (ush )9, (ush )10, (ush )11, (ush )13, (ush )15, (ush )17, (ush )19, (ush )23, (ush )27, (ush )31, (ush )35, (ush )43, (ush )51, (ush )59, (ush )67, (ush )83, (ush )99, (ush )115, (ush )131, (ush )163, (ush )195, (ush )227, (ush )258, (ush )0, (ush )0};
#line 1828 "gzip.preprocessed.c"
static ush cplext[31]   = 
#line 1828
  {(ush )0, (ush )0, (ush )0, (ush )0, (ush )0, (ush )0, (ush )0, (ush )0, (ush )1, (ush )1, (ush )1, (ush )1, (ush )2, (ush )2, (ush )2, (ush )2, (ush )3, (ush )3, (ush )3, (ush )3, (ush )4, (ush )4, (ush )4, (ush )4, (ush )5, (ush )5, (ush )5, (ush )5, (ush )0, (ush )99, (ush )99};
#line 1831 "gzip.preprocessed.c"
static ush cpdist[30]   = 
#line 1831
  {(ush )1, (ush )2, (ush )3, (ush )4, (ush )5, (ush )7, (ush )9, (ush )13, (ush )17, (ush )25, (ush )33, (ush )49, (ush )65, (ush )97, (ush )129, (ush )193, (ush )257, (ush )385, (ush )513, (ush )769, (ush )1025, (ush )1537, (ush )2049, (ush )3073, (ush )4097, (ush )6145, (ush )8193, (ush )12289, (ush )16385, (ush )24577};
#line 1835 "gzip.preprocessed.c"
static ush cpdext[30]   = 
#line 1835
  {(ush )0, (ush )0, (ush )0, (ush )0, (ush )1, (ush )1, (ush )2, (ush )2, (ush )3, (ush )3, (ush )4, (ush )4, (ush )5, (ush )5, (ush )6, (ush )6, (ush )7, (ush )7, (ush )8, (ush )8, (ush )9, (ush )9, (ush )10, (ush )10, (ush )11, (ush )11, (ush )12, (ush )12, (ush )13, (ush )13};
#line 1839 "gzip.preprocessed.c"
ulg bb  ;
#line 1840 "gzip.preprocessed.c"
unsigned int bk  ;
#line 1841 "gzip.preprocessed.c"
ush mask_bits[17]   = 
#line 1841
  {(ush )0, (ush )1, (ush )3, (ush )7, (ush )15, (ush )31, (ush )63, (ush )127, (ush )255, (ush )511, (ush )1023, (ush )2047, (ush )4095, (ush )8191, (ush )16383, (ush )32767, (ush )65535};
#line 1846 "gzip.preprocessed.c"
int lbits   = 9;
#line 1847 "gzip.preprocessed.c"
int dbits   = 6;
#line 1848 "gzip.preprocessed.c"
unsigned int hufts  ;
#line 2328 "gzip.preprocessed.c"
static int msg_done   = 0;
#line 2340 "gzip.preprocessed.c"
static int extra_lbits[29]   = 
#line 2340
  {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0};
#line 2342 "gzip.preprocessed.c"
static int extra_dbits[30]   = 
#line 2342
  {0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13};
#line 2344 "gzip.preprocessed.c"
static int extra_blbits[19]   = 
#line 2344
  {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 7};
#line 2356 "gzip.preprocessed.c"
static ct_data dyn_ltree[573]  ;
#line 2357 "gzip.preprocessed.c"
static ct_data dyn_dtree[61]  ;
#line 2358 "gzip.preprocessed.c"
static ct_data static_ltree[288]  ;
#line 2359 "gzip.preprocessed.c"
static ct_data static_dtree[30]  ;
#line 2360 "gzip.preprocessed.c"
static ct_data bl_tree[39]  ;
#line 2370 "gzip.preprocessed.c"
static tree_desc l_desc   = {dyn_ltree, static_ltree, extra_lbits, 257, 286, 15, 0};
#line 2372 "gzip.preprocessed.c"
static tree_desc d_desc   = {dyn_dtree, static_dtree, extra_dbits, 0, 30, 15, 0};
#line 2374 "gzip.preprocessed.c"
static tree_desc bl_desc   = {bl_tree, (ct_data *)0, extra_blbits, 0, 19, 7, 0};
#line 2376 "gzip.preprocessed.c"
static ush bl_count[16]  ;
#line 2377 "gzip.preprocessed.c"
static uch bl_order[19]   = 
#line 2377
  {(uch )16, (uch )17, (uch )18, (uch )0, (uch )8, (uch )7, (uch )9, (uch )6, (uch )10, (uch )5, (uch )11, (uch )4, (uch )12, (uch )3, (uch )13, (uch )2, (uch )14, (uch )1, (uch )15};
#line 2379 "gzip.preprocessed.c"
static int heap[573]  ;
#line 2380 "gzip.preprocessed.c"
static int heap_len  ;
#line 2381 "gzip.preprocessed.c"
static int heap_max  ;
#line 2382 "gzip.preprocessed.c"
static uch depth[573]  ;
#line 2383 "gzip.preprocessed.c"
static uch length_code[256]  ;
#line 2384 "gzip.preprocessed.c"
static uch dist_code[512]  ;
#line 2385 "gzip.preprocessed.c"
static int base_length[29]  ;
#line 2386 "gzip.preprocessed.c"
static int base_dist[30]  ;
#line 2387 "gzip.preprocessed.c"
static uch flag_buf[4096]  ;
#line 2388 "gzip.preprocessed.c"
static unsigned int last_lit  ;
#line 2389 "gzip.preprocessed.c"
static unsigned int last_dist  ;
#line 2390 "gzip.preprocessed.c"
static unsigned int last_flags  ;
#line 2391 "gzip.preprocessed.c"
static uch flags  ;
#line 2392 "gzip.preprocessed.c"
static uch flag_bit  ;
#line 2393 "gzip.preprocessed.c"
static ulg opt_len  ;
#line 2394 "gzip.preprocessed.c"
static ulg static_len  ;
#line 2395 "gzip.preprocessed.c"
static ulg compressed_len  ;
#line 2396 "gzip.preprocessed.c"
static ulg input_len  ;
#line 2397 "gzip.preprocessed.c"
ush *file_type  ;
#line 2398 "gzip.preprocessed.c"
int *file_method  ;
#line 2401
static void init_block(void) ;
#line 2402
static void pqdownheap(ct_data *tree , int k ) ;
#line 2403
static void gen_bitlen(tree_desc *desc ) ;
#line 2404
static void gen_codes(ct_data *tree , int max_code ) ;
#line 2405
static void build_tree(tree_desc *desc ) ;
#line 2406
static void scan_tree(ct_data *tree , int max_code ) ;
#line 2407
static void send_tree(ct_data *tree , int max_code ) ;
#line 2408
static int build_bl_tree(void) ;
#line 2409
static void send_all_trees(int lcodes , int dcodes , int blcodes ) ;
#line 2410
static void compress_block(ct_data *ltree , ct_data *dtree ) ;
#line 2411
static void set_file_type(void) ;
#line 2916
static unsigned int decode(unsigned int count , uch *buffer ) ;
#line 2917
static void decode_start(void) ;
#line 2918
static void huf_decode_start(void) ;
#line 2919
static unsigned int decode_c(void) ;
#line 2920
static unsigned int decode_p(void) ;
#line 2921
static void read_pt_len(int nn , int nbit , int i_special ) ;
#line 2922
static void read_c_len(void) ;
#line 2923
static void fillbuf(int n ) ;
#line 2924
static unsigned int getbits(int n ) ;
#line 2925
static void init_getbits(void) ;
#line 2926
static void make_table(int nchar , uch *bitlen , int tablebits , ush *table ) ;
#line 2927 "gzip.preprocessed.c"
static uch pt_len[19]  ;
#line 2928 "gzip.preprocessed.c"
static unsigned int blocksize  ;
#line 2929 "gzip.preprocessed.c"
static ush pt_table[256]  ;
#line 2930 "gzip.preprocessed.c"
static ush bitbuf  ;
#line 2931 "gzip.preprocessed.c"
static unsigned int subbitbuf  ;
#line 2932 "gzip.preprocessed.c"
static int bitcount  ;
#line 3120 "gzip.preprocessed.c"
static int j  ;
#line 3121 "gzip.preprocessed.c"
static int done  ;
#line 3132 "gzip.preprocessed.c"
static unsigned int i  ;
#line 3183
extern  __attribute__((__nothrow__)) __off_t ( __attribute__((__leaf__)) lseek)(int __fd , __off_t __offset , int __whence ) ;
#line 3184
extern int close(int __fd ) ;
#line 3185
extern ssize_t read(int __fd , void *__buf , size_t __nbytes ) ;
#line 3186
extern ssize_t write(int __fd , void const   *__buf , size_t __n ) ;
#line 3198
extern  __attribute__((__nothrow__)) int ( __attribute__((__nonnull__(1), __leaf__)) chown)(char const   *__file , __uid_t __owner , __gid_t __group ) ;
#line 3569
extern  __attribute__((__nothrow__)) int ( __attribute__((__leaf__)) isatty)(int __fd ) ;
#line 3586
extern  __attribute__((__nothrow__)) int ( __attribute__((__nonnull__(1), __leaf__)) unlink)(char const   *__name ) ;
#line 3642
extern int ( __attribute__((__nonnull__(1))) open)(char const   *__file , int __oflag  , ...) ;
#line 3661 "gzip.preprocessed.c"
int block_mode   = 128;
#line 3810 "gzip.preprocessed.c"
static ulg orig_len  ;
#line 3811 "gzip.preprocessed.c"
static int max_len  ;
#line 3812 "gzip.preprocessed.c"
static uch literal[256]  ;
#line 3813 "gzip.preprocessed.c"
static int lit_base[26]  ;
#line 3814 "gzip.preprocessed.c"
static int leaves[26]  ;
#line 3815 "gzip.preprocessed.c"
static int parents[26]  ;
#line 3816 "gzip.preprocessed.c"
static int peek_bits  ;
#line 3817 "gzip.preprocessed.c"
static ulg un_bitbuf  ;
#line 3818 "gzip.preprocessed.c"
static int valid  ;
#line 3819
static void read_tree(void) ;
#line 3820
static void un_build_tree(void) ;
#line 3911 "gzip.preprocessed.c"
char *key  ;
#line 3912 "gzip.preprocessed.c"
int pkzip   = 0;
#line 3913 "gzip.preprocessed.c"
int ext_header   = 0;
#line 4013
ulg crc_32_tab[256] ;
#line 4034
ulg updcrc(uch *s , unsigned int n ) ;
#line 4034 "gzip.preprocessed.c"
static ulg crc___0   = (ulg )4294967295L;
#line 4223 "gzip.preprocessed.c"
ulg crc_32_tab[256]   = 
#line 4223
  {(ulg )0L, (ulg )1996959894L, (ulg )3993919788L, (ulg )2567524794L, (ulg )124634137L, (ulg )1886057615L, (ulg )3915621685L, (ulg )2657392035L, (ulg )249268274L, (ulg )2044508324L, (ulg )3772115230L, (ulg )2547177864L, (ulg )162941995L, (ulg )2125561021L, (ulg )3887607047L, (ulg )2428444049L, (ulg )498536548L, (ulg )1789927666L, (ulg )4089016648L, (ulg )2227061214L, (ulg )450548861L, (ulg )1843258603L, (ulg )4107580753L, (ulg )2211677639L, (ulg )325883990L, (ulg )1684777152L, (ulg )4251122042L, (ulg )2321926636L, (ulg )335633487L, (ulg )1661365465L, (ulg )4195302755L, (ulg )2366115317L, (ulg )997073096L, (ulg )1281953886L, (ulg )3579855332L, (ulg )2724688242L, (ulg )1006888145L, (ulg )1258607687L, (ulg )3524101629L, (ulg )2768942443L, (ulg )901097722L, (ulg )1119000684L,
   (ulg )3686517206L, (ulg )2898065728L, (ulg )853044451L, (ulg )1172266101L, (ulg )3705015759L, (ulg )2882616665L, (ulg )651767980L, (ulg )1373503546L, (ulg )3369554304L, (ulg )3218104598L, (ulg )565507253L, (ulg )1454621731L, (ulg )3485111705L, (ulg )3099436303L, (ulg )671266974L, (ulg )1594198024L, (ulg )3322730930L, (ulg )2970347812L, (ulg )795835527L, (ulg )1483230225L, (ulg )3244367275L, (ulg )3060149565L, (ulg )1994146192L, (ulg )31158534L, (ulg )2563907772L, (ulg )4023717930L, (ulg )1907459465L, (ulg )112637215L, (ulg )2680153253L, (ulg )3904427059L, (ulg )2013776290L, (ulg )251722036L, (ulg )2517215374L, (ulg )3775830040L, (ulg )2137656763L, (ulg )141376813L, (ulg )2439277719L, (ulg )3865271297L, (ulg )1802195444L, (ulg )476864866L, (ulg )2238001368L, (ulg )4066508878L,
   (ulg )1812370925L, (ulg )453092731L, (ulg )2181625025L, (ulg )4111451223L, (ulg )1706088902L, (ulg )314042704L, (ulg )2344532202L, (ulg )4240017532L, (ulg )1658658271L, (ulg )366619977L, (ulg )2362670323L, (ulg )4224994405L, (ulg )1303535960L, (ulg )984961486L, (ulg )2747007092L, (ulg )3569037538L, (ulg )1256170817L, (ulg )1037604311L, (ulg )2765210733L, (ulg )3554079995L, (ulg )1131014506L, (ulg )879679996L, (ulg )2909243462L, (ulg )3663771856L, (ulg )1141124467L, (ulg )855842277L, (ulg )2852801631L, (ulg )3708648649L, (ulg )1342533948L, (ulg )654459306L, (ulg )3188396048L, (ulg )3373015174L, (ulg )1466479909L, (ulg )544179635L, (ulg )3110523913L, (ulg )3462522015L, (ulg )1591671054L, (ulg )702138776L, (ulg )2966460450L, (ulg )3352799412L, (ulg )1504918807L, (ulg )783551873L,
   (ulg )3082640443L, (ulg )3233442989L, (ulg )3988292384L, (ulg )2596254646L, (ulg )62317068L, (ulg )1957810842L, (ulg )3939845945L, (ulg )2647816111L, (ulg )81470997L, (ulg )1943803523L, (ulg )3814918930L, (ulg )2489596804L, (ulg )225274430L, (ulg )2053790376L, (ulg )3826175755L, (ulg )2466906013L, (ulg )167816743L, (ulg )2097651377L, (ulg )4027552580L, (ulg )2265490386L, (ulg )503444072L, (ulg )1762050814L, (ulg )4150417245L, (ulg )2154129355L, (ulg )426522225L, (ulg )1852507879L, (ulg )4275313526L, (ulg )2312317920L, (ulg )282753626L, (ulg )1742555852L, (ulg )4189708143L, (ulg )2394877945L, (ulg )397917763L, (ulg )1622183637L, (ulg )3604390888L, (ulg )2714866558L, (ulg )953729732L, (ulg )1340076626L, (ulg )3518719985L, (ulg )2797360999L, (ulg )1068828381L, (ulg )1219638859L,
   (ulg )3624741850L, (ulg )2936675148L, (ulg )906185462L, (ulg )1090812512L, (ulg )3747672003L, (ulg )2825379669L, (ulg )829329135L, (ulg )1181335161L, (ulg )3412177804L, (ulg )3160834842L, (ulg )628085408L, (ulg )1382605366L, (ulg )3423369109L, (ulg )3138078467L, (ulg )570562233L, (ulg )1426400815L, (ulg )3317316542L, (ulg )2998733608L, (ulg )733239954L, (ulg )1555261956L, (ulg )3268935591L, (ulg )3050360625L, (ulg )752459403L, (ulg )1541320221L, (ulg )2607071920L, (ulg )3965973030L, (ulg )1969922972L, (ulg )40735498L, (ulg )2617837225L, (ulg )3943577151L, (ulg )1913087877L, (ulg )83908371L, (ulg )2512341634L, (ulg )3803740692L, (ulg )2075208622L, (ulg )213261112L, (ulg )2463272603L, (ulg )3855990285L, (ulg )2094854071L, (ulg )198958881L, (ulg )2262029012L, (ulg )4057260610L,
   (ulg )1759359992L, (ulg )534414190L, (ulg )2176718541L, (ulg )4139329115L, (ulg )1873836001L, (ulg )414664567L, (ulg )2282248934L, (ulg )4279200368L, (ulg )1711684554L, (ulg )285281116L, (ulg )2405801727L, (ulg )4167216745L, (ulg )1634467795L, (ulg )376229701L, (ulg )2685067896L, (ulg )3608007406L, (ulg )1308918612L, (ulg )956543938L, (ulg )2808555105L, (ulg )3495958263L, (ulg )1231636301L, (ulg )1047427035L, (ulg )2932959818L, (ulg )3654703836L, (ulg )1088359270L, (ulg )936918000L, (ulg )2847714899L, (ulg )3736837829L, (ulg )1202900863L, (ulg )817233897L, (ulg )3183342108L, (ulg )3401237130L, (ulg )1404277552L, (ulg )615818150L, (ulg )3134207493L, (ulg )3453421203L, (ulg )1423857449L, (ulg )601450431L, (ulg )3009837614L, (ulg )3294710456L, (ulg )1567103746L, (ulg )711928724L,
   (ulg )3020668471L, (ulg )3272380065L, (ulg )1510334235L, (ulg )755167117L};
#line 4277 "gzip.preprocessed.c"
static ulg crc  ;
#line 4329 "gzip.preprocessed.c"
static char *license_msg[15]   = 
#line 4329
  {(char *)"   Copyright (C) 1992-1993 Jean-loup Gailly", (char *)"   This program is free software; you can redistribute it and/or modify", (char *)"   it under the terms of the GNU General Public License as published by", (char *)"   the Free Software Foundation; either version 2, or (at your option)", (char *)"   any later version.", (char *)"", (char *)"   This program is distributed in the hope that it will be useful,", (char *)"   but WITHOUT ANY WARRANTY; without even the implied warranty of", (char *)"   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the", (char *)"   GNU General Public License for more details.", (char *)"", (char *)"   You should have received a copy of the GNU General Public License",
   (char *)"   along with this program; if not, write to the Free Software", (char *)"   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.", (char *)0};
#line 4393
extern  __attribute__((__nothrow__)) char *( __attribute__((__leaf__)) ctime)(time_t const   *__timer ) ;
#line 4453
extern DIR *( __attribute__((__nonnull__(1))) opendir)(char const   *__name ) ;
#line 4455
extern int ( __attribute__((__nonnull__(1))) closedir)(DIR *__dirp ) ;
#line 4456
extern struct dirent *( __attribute__((__nonnull__(1))) readdir)(DIR *__dirp ) ;
#line 4486
extern  __attribute__((__nothrow__)) int ( __attribute__((__nonnull__(1), __leaf__)) utime)(char const   *__file , struct utimbuf  const  *__file_times ) ;
#line 4496 "gzip.preprocessed.c"
int ascii   = 0;
#line 4497 "gzip.preprocessed.c"
int to_stdout   = 0;
#line 4498 "gzip.preprocessed.c"
int decompress   = 0;
#line 4499 "gzip.preprocessed.c"
int force   = 0;
#line 4500 "gzip.preprocessed.c"
int no_name   = -1;
#line 4501 "gzip.preprocessed.c"
int no_time   = -1;
#line 4502 "gzip.preprocessed.c"
int recursive   = 0;
#line 4503 "gzip.preprocessed.c"
int list   = 0;
#line 4504 "gzip.preprocessed.c"
int verbose   = 0;
#line 4505 "gzip.preprocessed.c"
int quiet   = 0;
#line 4506 "gzip.preprocessed.c"
int do_lzw   = 0;
#line 4507 "gzip.preprocessed.c"
int test   = 0;
#line 4508 "gzip.preprocessed.c"
int foreground  ;
#line 4510 "gzip.preprocessed.c"
int maxbits   = 16;
#line 4511 "gzip.preprocessed.c"
int method   = 8;
#line 4512 "gzip.preprocessed.c"
int level   = 6;
#line 4513 "gzip.preprocessed.c"
int exit_code   = 0;
#line 4515 "gzip.preprocessed.c"
int last_member  ;
#line 4516 "gzip.preprocessed.c"
int part_nb  ;
#line 4519 "gzip.preprocessed.c"
char *env  ;
#line 4520 "gzip.preprocessed.c"
char **args   = (char **)((void *)0);
#line 4521 "gzip.preprocessed.c"
char z_suffix[31]  ;
#line 4522 "gzip.preprocessed.c"
int z_len  ;
#line 4525 "gzip.preprocessed.c"
long total_in   = 0L;
#line 4526 "gzip.preprocessed.c"
long total_out   = 0L;
#line 4529 "gzip.preprocessed.c"
int remove_ofname   = 0;
#line 4530 "gzip.preprocessed.c"
struct stat istat  ;
#line 4536 "gzip.preprocessed.c"
struct option longopts[24]   = 
#line 4536
  {{"ascii", 0, (int *)0, 'a'}, {"to-stdout", 0, (int *)0, 'c'}, {"stdout", 0, (int *)0, 'c'}, {"decompress", 0, (int *)0, 'd'}, {"uncompress", 0, (int *)0, 'd'}, {"force", 0, (int *)0, 'f'}, {"help", 0, (int *)0, 'h'}, {"list", 0, (int *)0, 'l'}, {"license", 0, (int *)0, 'L'}, {"no-name", 0, (int *)0, 'n'}, {"name", 0, (int *)0, 'N'}, {"quiet", 0, (int *)0, 'q'}, {"silent", 0, (int *)0, 'q'}, {"recursive", 0, (int *)0, 'r'}, {"suffix", 1, (int *)0, 'S'}, {"test", 0, (int *)0, 't'}, {"no-time", 0, (int *)0, 'T'}, {"verbose", 0, (int *)0, 'v'}, {"version", 0, (int *)0, 'V'}, {"fast", 0, (int *)0, '1'}, {"best", 0, (int *)0, '9'}, {"lzw", 0, (int *)0, 'Z'}, {"bits", 1, (int *)0, 'b'}, {(char const   *)0, 0, (int *)0, 0}};
#line 4563
static void usage(void) ;
#line 4564
static void help(void) ;
#line 4565
static void license(void) ;
#line 4566
static void version(void) ;
#line 4567
static void treat_stdin(void) ;
#line 4568
static void treat_file(char *iname ) ;
#line 4569
static int create_outfile(void) ;
#line 4570
static int do_stat(char *name , struct stat *sbuf ) ;
#line 4571
static char *get_suffix(char *name ) ;
#line 4572
static int get_istat(char *iname , struct stat *sbuf ) ;
#line 4573
static int make_ofname(void) ;
#line 4574
static int same_file(struct stat *stat1 , struct stat *stat2 ) ;
#line 4575
static int name_too_long(char *name , struct stat *statb ) ;
#line 4576
static void shorten_name(char *name ) ;
#line 4577
static int get_method(int in ) ;
#line 4578
static void do_list(int ifd___0 , int method___0 ) ;
#line 4579
static int check_ofname(void) ;
#line 4580
static void copy_stat(struct stat *ifstat ) ;
#line 4581
static void do_exit(int exitcode ) ;
#line 4582
int main(int argc , char **argv ) ;
#line 4583 "gzip.preprocessed.c"
int (*work)(int infile , int outfile )   = & zip;
#line 4584
static void treat_dir(char *dir ) ;
#line 4585
static void reset_times(char *name , struct stat *statb ) ;
#line 4596
static void help(void) ;
#line 4596 "gzip.preprocessed.c"
static char *help_msg[18]   = 
#line 4596
  {(char *)" -c --stdout      write on standard output, keep original files unchanged", (char *)" -d --decompress  decompress", (char *)" -f --force       force overwrite of output file and compress links", (char *)" -h --help        give this help", (char *)" -l --list        list compressed file contents", (char *)" -L --license     display software license", (char *)" -n --no-name     do not save or restore the original name and time stamp", (char *)" -N --name        save or restore the original name and time stamp", (char *)" -q --quiet       suppress all warnings", (char *)" -r --recursive   operate recursively on directories", (char *)" -S .suf  --suffix .suf     use suffix .suf on compressed files", (char *)" -t --test        test compressed file integrity",
   (char *)" -v --verbose     verbose mode", (char *)" -V --version     display version number", (char *)" -1 --fast        compress faster", (char *)" -9 --best        compress better", (char *)" file...          files to (de)compress. If none given, use standard input.", (char *)0};
#line 4974
static char *get_suffix(char *name ) ;
#line 4974 "gzip.preprocessed.c"
static char *known_suffixes[9]   = 
#line 4974
  {z_suffix, (char *)".gz", (char *)".z", (char *)".taz", (char *)".tgz", (char *)"-gz", (char *)"-z", (char *)"_z", (char *)((void *)0)};
#line 5001
static int get_istat(char *iname , struct stat *sbuf ) ;
#line 5001 "gzip.preprocessed.c"
static char *suffixes[6]   = {z_suffix, (char *)".gz", (char *)".z", (char *)"-z", (char *)".Z", (char *)((void *)0)};
#line 5201
static void do_list(int ifd___0 , int method___0 ) ;
#line 5201 "gzip.preprocessed.c"
static int first_time   = 1;
#line 5202
static void do_list(int ifd___0 , int method___0 ) ;
#line 5202 "gzip.preprocessed.c"
static char *methods[9]   = 
#line 5202
  {(char *)"store", (char *)"compr", (char *)"pack ", (char *)"lzh  ", (char *)"", (char *)"", (char *)"", (char *)"", (char *)"defla"};
#line 5451
static void do_exit(int exitcode ) ;
#line 5451 "gzip.preprocessed.c"
static int in_exit   = 0;
#line 4634 "gzip.preprocessed.c"
int main(int  argc__0, char ** argv__0){
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
#line 4642 "gzip.preprocessed.c"
  __cil_tmp19__1 = &argv__1;
#line 4642 "gzip.preprocessed.c"
  __cil_tmp20__1 = *__cil_tmp19__1;
#line 4642 "gzip.preprocessed.c"
  __cil_tmp21__1 = (__cil_tmp20__1) + (0);
#line 4642 "gzip.preprocessed.c"
  __cil_tmp22__1 = *__cil_tmp21__1;
#line 4642 "gzip.preprocessed.c"
  //progname = basename(__cil_tmp22__1);
  {
#line 4642 "gzip.preprocessed.c"
    char * __arg_tmp_0__2  = __cil_tmp22__1;
#line 4642 "gzip.preprocessed.c"
    char *__return__2;
#line 4109 "gzip.preprocessed.c"
    //enter basename
    char * fname__2 = __arg_tmp_0__2 ;
    char * p__2;
    char const   * __cil_tmp3__2;
    void * __cil_tmp4__2;
    unsigned long  __cil_tmp5__2;
    unsigned long  __cil_tmp6__2;
#line 4113 "gzip.preprocessed.c"
    __cil_tmp3__2 = (char const   *)(fname__2);
#line 4113 "gzip.preprocessed.c"
    //p__2 = strrchr(__cil_tmp3__2, '/');
    {
#line 4113 "gzip.preprocessed.c"
      char const   * __arg_tmp_0__3  = __cil_tmp3__2;
#line 4113 "gzip.preprocessed.c"
      int  __arg_tmp_1__3  = '/';
#line 4113 "gzip.preprocessed.c"
      char *__return__3;
#line 4113 "gzip.preprocessed.c"
      p__2 = __return__3;
    }
#line 4113 "gzip.preprocessed.c"
    __cil_tmp4__2 = (void *)(0);
#line 4113 "gzip.preprocessed.c"
    __cil_tmp5__2 = (unsigned long )(__cil_tmp4__2);
#line 4113 "gzip.preprocessed.c"
    __cil_tmp6__2 = (unsigned long )(p__2);
#line 4113 "gzip.preprocessed.c"
    fname__2 = (p__2) + (1);
#line 4115 "gzip.preprocessed.c"
    //exiting basename
#line 4115 "gzip.preprocessed.c"
    __return__2 = fname__2;
#line 4642 "gzip.preprocessed.c"
    progname = __return__2;
  }
#line 4643 "gzip.preprocessed.c"
  __cil_tmp23__1 = (char const   *)(progname);
#line 4643 "gzip.preprocessed.c"
  //tmp__1 = strlen(__cil_tmp23__1);
  {
#line 4643 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp23__1;
#line 4643 "gzip.preprocessed.c"
    size_t __return__2;
#line 4643 "gzip.preprocessed.c"
    tmp__1 = __return__2;
  }
#line 4643 "gzip.preprocessed.c"
  proglen__1 = (int )(tmp__1);
#line 4644 "gzip.preprocessed.c"
  __cil_tmp24__1 = (progname) + (proglen__1);
#line 4644 "gzip.preprocessed.c"
  __cil_tmp25__1 = (__cil_tmp24__1) - (4);
#line 4644 "gzip.preprocessed.c"
  __cil_tmp26__1 = (char const   *)(__cil_tmp25__1);
#line 4644 "gzip.preprocessed.c"
  //tmp___0__1 = strcmp(__cil_tmp26__1, ".exe");
  {
#line 4644 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp26__1;
#line 4644 "gzip.preprocessed.c"
    char const   * __arg_tmp_1__2  = ".exe";
#line 4644 "gzip.preprocessed.c"
    int __return__2;
#line 4644 "gzip.preprocessed.c"
    tmp___0__1 = __return__2;
  }
#line 4647 "gzip.preprocessed.c"
  __cil_tmp29__1 = (char *)("GZIP");
#line 4647 "gzip.preprocessed.c"
  //env = add_envopt(&argc__1, &argv__1, __cil_tmp29__1);
  {
#line 4647 "gzip.preprocessed.c"
    int * __arg_tmp_0__2  = &argc__2;
#line 4647 "gzip.preprocessed.c"
    char *** __arg_tmp_1__2  = &argv__2;
#line 4647 "gzip.preprocessed.c"
    char * __arg_tmp_2__2  = __cil_tmp29__1;
#line 4647 "gzip.preprocessed.c"
    char *__return__2;
#line 4127 "gzip.preprocessed.c"
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
#line 4135 "gzip.preprocessed.c"
    oargc__2 = *argcp__2;
#line 4136 "gzip.preprocessed.c"
    nargc__2 = 0;
#line 4137 "gzip.preprocessed.c"
    __cil_tmp25__2 = (char const   *)(env__2);
#line 4137 "gzip.preprocessed.c"
    //tmp__2 = getenv(__cil_tmp25__2);
    {
#line 4137 "gzip.preprocessed.c"
      char const   * __arg_tmp_0__3  = __cil_tmp25__2;
#line 4137 "gzip.preprocessed.c"
      char *__return__3;
#line 4137 "gzip.preprocessed.c"
      tmp__2 = __return__3;
    }
#line 4137 "gzip.preprocessed.c"
    env__2 = tmp__2;
#line 4138 "gzip.preprocessed.c"
    __cil_tmp26__2 = (void *)(0);
#line 4138 "gzip.preprocessed.c"
    __cil_tmp27__2 = (unsigned long )(__cil_tmp26__2);
#line 4138 "gzip.preprocessed.c"
    __cil_tmp28__2 = (unsigned long )(env__2);
#line 4138 "gzip.preprocessed.c"
    __cil_tmp29__2 = (void *)(0);
#line 4138 "gzip.preprocessed.c"
    //exiting add_envopt
#line 4138 "gzip.preprocessed.c"
    __return__2 = (char *)(__cil_tmp29__2);
#line 4647 "gzip.preprocessed.c"
    env = __return__2;
  }
#line 4648 "gzip.preprocessed.c"
  __cil_tmp30__1 = (void *)(0);
#line 4648 "gzip.preprocessed.c"
  __cil_tmp31__1 = (unsigned long )(__cil_tmp30__1);
#line 4648 "gzip.preprocessed.c"
  __cil_tmp32__1 = (unsigned long )(env);
#line 4649 "gzip.preprocessed.c"
  __cil_tmp34__1 = (void (*)(int  ))(1);
#line 4649 "gzip.preprocessed.c"
  //tmp___1__1 = signal(2, __cil_tmp34__1);
  {
#line 4649 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 2;
#line 4649 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp34__1;
#line 4649 "gzip.preprocessed.c"
    __sighandler_t __return__2;
#line 4649 "gzip.preprocessed.c"
    tmp___1__1 = __return__2;
  }
#line 4649 "gzip.preprocessed.c"
  __cil_tmp35__1 = (void (*)(int  ))(1);
#line 4649 "gzip.preprocessed.c"
  __cil_tmp36__1 = (unsigned long )(__cil_tmp35__1);
#line 4649 "gzip.preprocessed.c"
  __cil_tmp37__1 = (unsigned long )(tmp___1__1);
#line 4649 "gzip.preprocessed.c"
  foreground = (__cil_tmp37__1) != (__cil_tmp36__1);
#line 4651 "gzip.preprocessed.c"
  __cil_tmp38__1 = (void (*)(int  ))(&abort_gzip);
#line 4651 "gzip.preprocessed.c"
  //signal(2, __cil_tmp38__1);
  {
#line 4651 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 2;
#line 4651 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp38__1;
  }
#line 4653 "gzip.preprocessed.c"
  __cil_tmp39__1 = (void (*)(int  ))(1);
#line 4653 "gzip.preprocessed.c"
  //tmp___2__1 = signal(15, __cil_tmp39__1);
  {
#line 4653 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 15;
#line 4653 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp39__1;
#line 4653 "gzip.preprocessed.c"
    __sighandler_t __return__2;
#line 4653 "gzip.preprocessed.c"
    tmp___2__1 = __return__2;
  }
#line 4653 "gzip.preprocessed.c"
  __cil_tmp40__1 = (void (*)(int  ))(1);
#line 4653 "gzip.preprocessed.c"
  __cil_tmp41__1 = (unsigned long )(__cil_tmp40__1);
#line 4653 "gzip.preprocessed.c"
  __cil_tmp42__1 = (unsigned long )(tmp___2__1);
#line 4654 "gzip.preprocessed.c"
  __cil_tmp43__1 = (void (*)(int  ))(&abort_gzip);
#line 4654 "gzip.preprocessed.c"
  //signal(15, __cil_tmp43__1);
  {
#line 4654 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 15;
#line 4654 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp43__1;
  }
#line 4656 "gzip.preprocessed.c"
  __cil_tmp44__1 = (void (*)(int  ))(1);
#line 4656 "gzip.preprocessed.c"
  //tmp___3__1 = signal(1, __cil_tmp44__1);
  {
#line 4656 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 1;
#line 4656 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp44__1;
#line 4656 "gzip.preprocessed.c"
    __sighandler_t __return__2;
#line 4656 "gzip.preprocessed.c"
    tmp___3__1 = __return__2;
  }
#line 4656 "gzip.preprocessed.c"
  __cil_tmp45__1 = (void (*)(int  ))(1);
#line 4656 "gzip.preprocessed.c"
  __cil_tmp46__1 = (unsigned long )(__cil_tmp45__1);
#line 4656 "gzip.preprocessed.c"
  __cil_tmp47__1 = (unsigned long )(tmp___3__1);
#line 4657 "gzip.preprocessed.c"
  __cil_tmp48__1 = (void (*)(int  ))(&abort_gzip);
#line 4657 "gzip.preprocessed.c"
  //signal(1, __cil_tmp48__1);
  {
#line 4657 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = 1;
#line 4657 "gzip.preprocessed.c"
    void (* __arg_tmp_1__2 )(int ) = __cil_tmp48__1;
  }
#line 4659 "gzip.preprocessed.c"
  __cil_tmp49__1 = (char const   *)(progname);
#line 4659 "gzip.preprocessed.c"
  __cil_tmp50__1 = (size_t )(2);
#line 4659 "gzip.preprocessed.c"
  //tmp___6__1 = strncmp(__cil_tmp49__1, "un", __cil_tmp50__1);
  {
#line 4659 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp49__1;
#line 4659 "gzip.preprocessed.c"
    char const   * __arg_tmp_1__2  = "un";
#line 4659 "gzip.preprocessed.c"
    size_t  __arg_tmp_2__2  = __cil_tmp50__1;
#line 4659 "gzip.preprocessed.c"
    int __return__2;
#line 4659 "gzip.preprocessed.c"
    tmp___6__1 = __return__2;
  }
#line 4659 "gzip.preprocessed.c"
  __cil_tmp51__1 = (char const   *)(progname);
#line 4659 "gzip.preprocessed.c"
  __cil_tmp52__1 = (size_t )(3);
#line 4659 "gzip.preprocessed.c"
  //tmp___7__1 = strncmp(__cil_tmp51__1, "gun", __cil_tmp52__1);
  {
#line 4659 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp51__1;
#line 4659 "gzip.preprocessed.c"
    char const   * __arg_tmp_1__2  = "gun";
#line 4659 "gzip.preprocessed.c"
    size_t  __arg_tmp_2__2  = __cil_tmp52__1;
#line 4659 "gzip.preprocessed.c"
    int __return__2;
#line 4659 "gzip.preprocessed.c"
    tmp___7__1 = __return__2;
  }
#line 4662 "gzip.preprocessed.c"
  __cil_tmp53__1 = (progname) + (1);
#line 4662 "gzip.preprocessed.c"
  __cil_tmp54__1 = (char const   *)(__cil_tmp53__1);
#line 4662 "gzip.preprocessed.c"
  //tmp___4__1 = strcmp(__cil_tmp54__1, "cat");
  {
#line 4662 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp54__1;
#line 4662 "gzip.preprocessed.c"
    char const   * __arg_tmp_1__2  = "cat";
#line 4662 "gzip.preprocessed.c"
    int __return__2;
#line 4662 "gzip.preprocessed.c"
    tmp___4__1 = __return__2;
  }
#line 4662 "gzip.preprocessed.c"
  __cil_tmp55__1 = (char const   *)(progname);
#line 4662 "gzip.preprocessed.c"
  //tmp___5__1 = strcmp(__cil_tmp55__1, "gzcat");
  {
#line 4662 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp55__1;
#line 4662 "gzip.preprocessed.c"
    char const   * __arg_tmp_1__2  = "gzcat";
#line 4662 "gzip.preprocessed.c"
    int __return__2;
#line 4662 "gzip.preprocessed.c"
    tmp___5__1 = __return__2;
  }
#line 4666 "gzip.preprocessed.c"
  __cil_tmp56__1 = (0) * (1UL);
#line 4666 "gzip.preprocessed.c"
  __cil_tmp57__1 = ((unsigned long )(z_suffix)) + (__cil_tmp56__1);
#line 4666 "gzip.preprocessed.c"
  __cil_tmp58__1 = (char *)(__cil_tmp57__1);
#line 4666 "gzip.preprocessed.c"
  __cil_tmp59__1 = (char * __restrict  )(__cil_tmp58__1);
#line 4666 "gzip.preprocessed.c"
  __cil_tmp60__1 = (char const   * __restrict  )(".gz");
#line 4666 "gzip.preprocessed.c"
  __cil_tmp61__1 = (31UL) - (1UL);
#line 4666 "gzip.preprocessed.c"
  //strncpy(__cil_tmp59__1, __cil_tmp60__1, __cil_tmp61__1);
  {
#line 4666 "gzip.preprocessed.c"
    char * __restrict   __arg_tmp_0__2  = __cil_tmp59__1;
#line 4666 "gzip.preprocessed.c"
    char const   * __restrict   __arg_tmp_1__2  = __cil_tmp60__1;
#line 4666 "gzip.preprocessed.c"
    unsigned long  __arg_tmp_2__2  = __cil_tmp61__1;
  }
#line 4667 "gzip.preprocessed.c"
  __cil_tmp62__1 = (0) * (1UL);
#line 4667 "gzip.preprocessed.c"
  __cil_tmp63__1 = ((unsigned long )(z_suffix)) + (__cil_tmp62__1);
#line 4667 "gzip.preprocessed.c"
  __cil_tmp64__1 = (char *)(__cil_tmp63__1);
#line 4667 "gzip.preprocessed.c"
  __cil_tmp65__1 = (char const   *)(__cil_tmp64__1);
#line 4667 "gzip.preprocessed.c"
  //tmp___8__1 = strlen(__cil_tmp65__1);
  {
#line 4667 "gzip.preprocessed.c"
    char const   * __arg_tmp_0__2  = __cil_tmp65__1;
#line 4667 "gzip.preprocessed.c"
    size_t __return__2;
#line 4667 "gzip.preprocessed.c"
    tmp___8__1 = __return__2;
  }
#line 4667 "gzip.preprocessed.c"
  z_len = (int )(tmp___8__1);
#line 4668 "gzip.preprocessed.c"
  __cil_tmp66__1 = &argc__1;
#line 4668 "gzip.preprocessed.c"
  __cil_tmp67__1 = *__cil_tmp66__1;
#line 4668 "gzip.preprocessed.c"
  __cil_tmp68__1 = &argv__1;
#line 4668 "gzip.preprocessed.c"
  __cil_tmp69__1 = *__cil_tmp68__1;
#line 4668 "gzip.preprocessed.c"
  __cil_tmp70__1 = (char * const  *)(__cil_tmp69__1);
#line 4668 "gzip.preprocessed.c"
  __cil_tmp71__1 = (0) * (32UL);
#line 4668 "gzip.preprocessed.c"
  __cil_tmp72__1 = ((unsigned long )(longopts)) + (__cil_tmp71__1);
#line 4668 "gzip.preprocessed.c"
  __cil_tmp73__1 = (struct option *)(__cil_tmp72__1);
#line 4668 "gzip.preprocessed.c"
  __cil_tmp74__1 = (struct option  const  *)(__cil_tmp73__1);
#line 4668 "gzip.preprocessed.c"
  __cil_tmp75__1 = (int *)(0);
#line 4668 "gzip.preprocessed.c"
  //optc__1 = getopt_long(__cil_tmp67__1, __cil_tmp70__1, "ab:cdfhH?lLmMnNqrS:tvVZ123456789", __cil_tmp74__1, __cil_tmp75__1);
  {
#line 4668 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = __cil_tmp67__1;
#line 4668 "gzip.preprocessed.c"
    char * const  * __arg_tmp_1__2  = __cil_tmp70__1;
#line 4668 "gzip.preprocessed.c"
    char const   * __arg_tmp_2__2  = "ab:cdfhH?lLmMnNqrS:tvVZ123456789";
#line 4668 "gzip.preprocessed.c"
    struct option  const  * __arg_tmp_3__2  = __cil_tmp74__1;
#line 4668 "gzip.preprocessed.c"
    int * __arg_tmp_4__2  = __cil_tmp75__1;
#line 4668 "gzip.preprocessed.c"
    int __return__2;
#line 4668 "gzip.preprocessed.c"
    optc__1 = __return__2;
  }
#line 4679 "gzip.preprocessed.c"
  decompress = 1;
#line 4668 "gzip.preprocessed.c"
  __cil_tmp66__1 = &argc__1;
#line 4668 "gzip.preprocessed.c"
  __cil_tmp67__1 = *__cil_tmp66__1;
#line 4668 "gzip.preprocessed.c"
  __cil_tmp68__1 = &argv__1;
#line 4668 "gzip.preprocessed.c"
  __cil_tmp69__1 = *__cil_tmp68__1;
#line 4668 "gzip.preprocessed.c"
  __cil_tmp70__1 = (char * const  *)(__cil_tmp69__1);
#line 4668 "gzip.preprocessed.c"
  __cil_tmp71__1 = (0) * (32UL);
#line 4668 "gzip.preprocessed.c"
  __cil_tmp72__1 = ((unsigned long )(longopts)) + (__cil_tmp71__1);
#line 4668 "gzip.preprocessed.c"
  __cil_tmp73__1 = (struct option *)(__cil_tmp72__1);
#line 4668 "gzip.preprocessed.c"
  __cil_tmp74__1 = (struct option  const  *)(__cil_tmp73__1);
#line 4668 "gzip.preprocessed.c"
  __cil_tmp75__1 = (int *)(0);
#line 4668 "gzip.preprocessed.c"
  //optc__1 = getopt_long(__cil_tmp67__1, __cil_tmp70__1, "ab:cdfhH?lLmMnNqrS:tvVZ123456789", __cil_tmp74__1, __cil_tmp75__1);
  {
#line 4668 "gzip.preprocessed.c"
    int  __arg_tmp_0__2  = __cil_tmp67__1;
#line 4668 "gzip.preprocessed.c"
    char * const  * __arg_tmp_1__2  = __cil_tmp70__1;
#line 4668 "gzip.preprocessed.c"
    char const   * __arg_tmp_2__2  = "ab:cdfhH?lLmMnNqrS:tvVZ123456789";
#line 4668 "gzip.preprocessed.c"
    struct option  const  * __arg_tmp_3__2  = __cil_tmp74__1;
#line 4668 "gzip.preprocessed.c"
    int * __arg_tmp_4__2  = __cil_tmp75__1;
#line 4668 "gzip.preprocessed.c"
    int __return__2;
#line 4668 "gzip.preprocessed.c"
    optc__1 = __return__2;
  }
#line 4725 "gzip.preprocessed.c"
  no_time = decompress;
#line 4726 "gzip.preprocessed.c"
  no_name = decompress;
#line 4727 "gzip.preprocessed.c"
  __cil_tmp85__1 = &argc__1;
#line 4727 "gzip.preprocessed.c"
  __cil_tmp86__1 = *__cil_tmp85__1;
#line 4727 "gzip.preprocessed.c"
  file_count__1 = (__cil_tmp86__1) - (optind);
#line 4751 "gzip.preprocessed.c"
  //treat_stdin();
  {
#line 4759 "gzip.preprocessed.c"
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
#line 4761 "gzip.preprocessed.c"
    tmp___1__2 = stdin;
#line 4761 "gzip.preprocessed.c"
    //tmp___2__2 = fileno(tmp___1__2);
    {
#line 4761 "gzip.preprocessed.c"
      struct _IO_FILE * __arg_tmp_0__3  = tmp___1__2;
#line 4761 "gzip.preprocessed.c"
      int __return__3;
#line 4761 "gzip.preprocessed.c"
      tmp___2__2 = __return__3;
    }
#line 4761 "gzip.preprocessed.c"
    //tmp___3__2 = isatty(tmp___2__2);
    {
#line 4761 "gzip.preprocessed.c"
      int  __arg_tmp_0__3  = tmp___2__2;
#line 4761 "gzip.preprocessed.c"
      int __return__3;
#line 4761 "gzip.preprocessed.c"
      tmp___3__2 = __return__3;
    }
#line 4771 "gzip.preprocessed.c"
    tmp___4__2 = 1;
#line 4774 "gzip.preprocessed.c"
    tmp___5__2 = 1;
#line 4777 "gzip.preprocessed.c"
    __cil_tmp17__2 = (0) * (1UL);
#line 4777 "gzip.preprocessed.c"
    __cil_tmp18__2 = ((unsigned long )(ifname)) + (__cil_tmp17__2);
#line 4777 "gzip.preprocessed.c"
    __cil_tmp19__2 = (char *)(__cil_tmp18__2);
#line 4777 "gzip.preprocessed.c"
    __cil_tmp20__2 = (char * __restrict  )(__cil_tmp19__2);
#line 4777 "gzip.preprocessed.c"
    __cil_tmp21__2 = (char const   * __restrict  )("stdin");
#line 4777 "gzip.preprocessed.c"
    //strcpy(__cil_tmp20__2, __cil_tmp21__2);
    {
#line 4777 "gzip.preprocessed.c"
      char * __restrict   __arg_tmp_0__3  = __cil_tmp20__2;
#line 4777 "gzip.preprocessed.c"
      char const   * __restrict   __arg_tmp_1__3  = __cil_tmp21__2;
    }
#line 4778 "gzip.preprocessed.c"
    __cil_tmp22__2 = (0) * (1UL);
#line 4778 "gzip.preprocessed.c"
    __cil_tmp23__2 = ((unsigned long )(ofname)) + (__cil_tmp22__2);
#line 4778 "gzip.preprocessed.c"
    __cil_tmp24__2 = (char *)(__cil_tmp23__2);
#line 4778 "gzip.preprocessed.c"
    __cil_tmp25__2 = (char * __restrict  )(__cil_tmp24__2);
#line 4778 "gzip.preprocessed.c"
    __cil_tmp26__2 = (char const   * __restrict  )("stdout");
#line 4778 "gzip.preprocessed.c"
    //strcpy(__cil_tmp25__2, __cil_tmp26__2);
    {
#line 4778 "gzip.preprocessed.c"
      char * __restrict   __arg_tmp_0__3  = __cil_tmp25__2;
#line 4778 "gzip.preprocessed.c"
      char const   * __restrict   __arg_tmp_1__3  = __cil_tmp26__2;
    }
#line 4779 "gzip.preprocessed.c"
    __cil_tmp27__2 = &time_stamp;
#line 4779 "gzip.preprocessed.c"
    *__cil_tmp27__2 = 0L;
#line 4786 "gzip.preprocessed.c"
    ifile_size = -1L;
#line 4787 "gzip.preprocessed.c"
    //clear_bufs();
    {
#line 4046 "gzip.preprocessed.c"
      //enter clear_bufs
#line 4048 "gzip.preprocessed.c"
      outcnt = 0U;
#line 4049 "gzip.preprocessed.c"
      inptr = 0U;
#line 4049 "gzip.preprocessed.c"
      insize = inptr;
#line 4050 "gzip.preprocessed.c"
      bytes_out = 0L;
#line 4050 "gzip.preprocessed.c"
      bytes_in = bytes_out;
    }
#line 4788 "gzip.preprocessed.c"
    to_stdout = 1;
#line 4789 "gzip.preprocessed.c"
    part_nb = 0;
#line 4791 "gzip.preprocessed.c"
    __cil_tmp30__2 = &method;
#line 4791 "gzip.preprocessed.c"
    //*__cil_tmp30__2 = get_method(ifd);
    {
#line 4791 "gzip.preprocessed.c"
      int  __arg_tmp_0__3  = ifd;
#line 4791 "gzip.preprocessed.c"
      int __return__3;
#line 5062 "gzip.preprocessed.c"
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
#line 5072 "gzip.preprocessed.c"
      //tmp___6__3 = fill_inbuf(0);
      {
#line 5072 "gzip.preprocessed.c"
        int  __arg_tmp_0__4  = 0;
#line 5072 "gzip.preprocessed.c"
        int __return__4;
#line 4052 "gzip.preprocessed.c"
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
#line 4056 "gzip.preprocessed.c"
        insize = 0U;
#line 4057 "gzip.preprocessed.c"
        //tmp__4 = __errno_location();
        {
#line 4057 "gzip.preprocessed.c"
          int *__return__5;
#line 4057 "gzip.preprocessed.c"
          tmp__4 = __return__5;
        }
#line 4057 "gzip.preprocessed.c"
        *tmp__4 = 0;
#line 4059 "gzip.preprocessed.c"
        __cil_tmp5__4 = (0) * (1UL);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp6__4 = ((unsigned long )(inbuf)) + (__cil_tmp5__4);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp7__4 = (uch *)(__cil_tmp6__4);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp8__4 = (char *)(__cil_tmp7__4);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp9__4 = (__cil_tmp8__4) + (insize);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp10__4 = (void *)(__cil_tmp9__4);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp11__4 = (32768U) - (insize);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp12__4 = (size_t )(__cil_tmp11__4);
#line 4059 "gzip.preprocessed.c"
        //tmp___0__4 = read(ifd, __cil_tmp10__4, __cil_tmp12__4);
        {
#line 4059 "gzip.preprocessed.c"
          int  __arg_tmp_0__5  = ifd;
#line 4059 "gzip.preprocessed.c"
          void * __arg_tmp_1__5  = __cil_tmp10__4;
#line 4059 "gzip.preprocessed.c"
          size_t  __arg_tmp_2__5  = __cil_tmp12__4;
#line 4059 "gzip.preprocessed.c"
          ssize_t __return__5;
#line 4059 "gzip.preprocessed.c"
          tmp___0__4 = __return__5;
        }
#line 4059 "gzip.preprocessed.c"
        len__4 = (int )(tmp___0__4);
#line 4061 "gzip.preprocessed.c"
        __cil_tmp13__4 = (unsigned int )(len__4);
#line 4061 "gzip.preprocessed.c"
        insize = (insize) + (__cil_tmp13__4);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp5__4 = (0) * (1UL);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp6__4 = ((unsigned long )(inbuf)) + (__cil_tmp5__4);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp7__4 = (uch *)(__cil_tmp6__4);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp8__4 = (char *)(__cil_tmp7__4);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp9__4 = (__cil_tmp8__4) + (insize);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp10__4 = (void *)(__cil_tmp9__4);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp11__4 = (32768U) - (insize);
#line 4059 "gzip.preprocessed.c"
        __cil_tmp12__4 = (size_t )(__cil_tmp11__4);
#line 4059 "gzip.preprocessed.c"
        //tmp___0__4 = read(ifd, __cil_tmp10__4, __cil_tmp12__4);
        {
#line 4059 "gzip.preprocessed.c"
          int  __arg_tmp_0__5  = ifd;
#line 4059 "gzip.preprocessed.c"
          void * __arg_tmp_1__5  = __cil_tmp10__4;
#line 4059 "gzip.preprocessed.c"
          size_t  __arg_tmp_2__5  = __cil_tmp12__4;
#line 4059 "gzip.preprocessed.c"
          ssize_t __return__5;
#line 4059 "gzip.preprocessed.c"
          tmp___0__4 = __return__5;
        }
#line 4059 "gzip.preprocessed.c"
        len__4 = (int )(tmp___0__4);
#line 4067 "gzip.preprocessed.c"
        __cil_tmp14__4 = (ulg )(insize);
#line 4067 "gzip.preprocessed.c"
        __cil_tmp15__4 = (ulg )(bytes_in);
#line 4067 "gzip.preprocessed.c"
        __cil_tmp16__4 = (__cil_tmp15__4) + (__cil_tmp14__4);
#line 4067 "gzip.preprocessed.c"
        bytes_in = (long )(__cil_tmp16__4);
#line 4068 "gzip.preprocessed.c"
        inptr = 1U;
#line 4069 "gzip.preprocessed.c"
        __cil_tmp17__4 = (0) * (1UL);
#line 4069 "gzip.preprocessed.c"
        __cil_tmp18__4 = ((unsigned long )(inbuf)) + (__cil_tmp17__4);
#line 4069 "gzip.preprocessed.c"
        mem_20__4 = (uch *)(__cil_tmp18__4);
#line 4069 "gzip.preprocessed.c"
        __cil_tmp19__4 = *mem_20__4;
#line 4069 "gzip.preprocessed.c"
        //exiting fill_inbuf
#line 4069 "gzip.preprocessed.c"
        __return__4 = (int )(__cil_tmp19__4);
#line 5072 "gzip.preprocessed.c"
        tmp___6__3 = __return__4;
      }
#line 5072 "gzip.preprocessed.c"
      tmp___7__3 = tmp___6__3;
#line 5072 "gzip.preprocessed.c"
      __cil_tmp87__3 = (0) * (1UL);
#line 5072 "gzip.preprocessed.c"
      __cil_tmp88__3 = ((unsigned long )(magic__3)) + (__cil_tmp87__3);
#line 5072 "gzip.preprocessed.c"
      mem_277__3 = (char *)(__cil_tmp88__3);
#line 5072 "gzip.preprocessed.c"
      *mem_277__3 = (char )(tmp___7__3);
#line 5073 "gzip.preprocessed.c"
      tmp___8__3 = inptr;
#line 5073 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5073 "gzip.preprocessed.c"
      __cil_tmp89__3 = (tmp___8__3) * (1UL);
#line 5073 "gzip.preprocessed.c"
      __cil_tmp90__3 = ((unsigned long )(inbuf)) + (__cil_tmp89__3);
#line 5073 "gzip.preprocessed.c"
      mem_278__3 = (uch *)(__cil_tmp90__3);
#line 5073 "gzip.preprocessed.c"
      __cil_tmp91__3 = *mem_278__3;
#line 5073 "gzip.preprocessed.c"
      tmp___10__3 = (int )(__cil_tmp91__3);
#line 5073 "gzip.preprocessed.c"
      __cil_tmp92__3 = (1) * (1UL);
#line 5073 "gzip.preprocessed.c"
      __cil_tmp93__3 = ((unsigned long )(magic__3)) + (__cil_tmp92__3);
#line 5073 "gzip.preprocessed.c"
      mem_279__3 = (char *)(__cil_tmp93__3);
#line 5073 "gzip.preprocessed.c"
      *mem_279__3 = (char )(tmp___10__3);
#line 5075 "gzip.preprocessed.c"
      __cil_tmp94__3 = &method;
#line 5075 "gzip.preprocessed.c"
      *__cil_tmp94__3 = -1;
#line 5076 "gzip.preprocessed.c"
      part_nb = (part_nb) + (1);
#line 5077 "gzip.preprocessed.c"
      header_bytes = 0L;
#line 5078 "gzip.preprocessed.c"
      last_member = 0;
#line 5079 "gzip.preprocessed.c"
      __cil_tmp95__3 = (0) * (1UL);
#line 5079 "gzip.preprocessed.c"
      __cil_tmp96__3 = ((unsigned long )(magic__3)) + (__cil_tmp95__3);
#line 5079 "gzip.preprocessed.c"
      __cil_tmp97__3 = (char *)(__cil_tmp96__3);
#line 5079 "gzip.preprocessed.c"
      __cil_tmp98__3 = (void const   *)(__cil_tmp97__3);
#line 5079 "gzip.preprocessed.c"
      __cil_tmp99__3 = (void const   *)("\031\139");
#line 5079 "gzip.preprocessed.c"
      __cil_tmp100__3 = (size_t )(2);
#line 5079 "gzip.preprocessed.c"
      //tmp___61__3 = memcmp(__cil_tmp98__3, __cil_tmp99__3, __cil_tmp100__3);
      {
#line 5079 "gzip.preprocessed.c"
        void const   * __arg_tmp_0__4  = __cil_tmp98__3;
#line 5079 "gzip.preprocessed.c"
        void const   * __arg_tmp_1__4  = __cil_tmp99__3;
#line 5079 "gzip.preprocessed.c"
        size_t  __arg_tmp_2__4  = __cil_tmp100__3;
#line 5079 "gzip.preprocessed.c"
        int __return__4;
#line 5079 "gzip.preprocessed.c"
        tmp___61__3 = __return__4;
      }
#line 5079 "gzip.preprocessed.c"
      __cil_tmp101__3 = (0) * (1UL);
#line 5079 "gzip.preprocessed.c"
      __cil_tmp102__3 = ((unsigned long )(magic__3)) + (__cil_tmp101__3);
#line 5079 "gzip.preprocessed.c"
      __cil_tmp103__3 = (char *)(__cil_tmp102__3);
#line 5079 "gzip.preprocessed.c"
      __cil_tmp104__3 = (void const   *)(__cil_tmp103__3);
#line 5079 "gzip.preprocessed.c"
      __cil_tmp105__3 = (void const   *)("\031\158");
#line 5079 "gzip.preprocessed.c"
      __cil_tmp106__3 = (size_t )(2);
#line 5079 "gzip.preprocessed.c"
      //tmp___62__3 = memcmp(__cil_tmp104__3, __cil_tmp105__3, __cil_tmp106__3);
      {
#line 5079 "gzip.preprocessed.c"
        void const   * __arg_tmp_0__4  = __cil_tmp104__3;
#line 5079 "gzip.preprocessed.c"
        void const   * __arg_tmp_1__4  = __cil_tmp105__3;
#line 5079 "gzip.preprocessed.c"
        size_t  __arg_tmp_2__4  = __cil_tmp106__3;
#line 5079 "gzip.preprocessed.c"
        int __return__4;
#line 5079 "gzip.preprocessed.c"
        tmp___62__3 = __return__4;
      }
#line 5081 "gzip.preprocessed.c"
      tmp___11__3 = inptr;
#line 5081 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5081 "gzip.preprocessed.c"
      __cil_tmp107__3 = (tmp___11__3) * (1UL);
#line 5081 "gzip.preprocessed.c"
      __cil_tmp108__3 = ((unsigned long )(inbuf)) + (__cil_tmp107__3);
#line 5081 "gzip.preprocessed.c"
      mem_280__3 = (uch *)(__cil_tmp108__3);
#line 5081 "gzip.preprocessed.c"
      __cil_tmp109__3 = *mem_280__3;
#line 5081 "gzip.preprocessed.c"
      tmp___13__3 = (int )(__cil_tmp109__3);
#line 5081 "gzip.preprocessed.c"
      __cil_tmp110__3 = &method;
#line 5081 "gzip.preprocessed.c"
      *__cil_tmp110__3 = tmp___13__3;
#line 5082 "gzip.preprocessed.c"
      __cil_tmp111__3 = &method;
#line 5082 "gzip.preprocessed.c"
      __cil_tmp112__3 = *__cil_tmp111__3;
#line 5089 "gzip.preprocessed.c"
      work = &unzip;
#line 5090 "gzip.preprocessed.c"
      tmp___14__3 = inptr;
#line 5090 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5090 "gzip.preprocessed.c"
      __cil_tmp120__3 = (tmp___14__3) * (1UL);
#line 5090 "gzip.preprocessed.c"
      __cil_tmp121__3 = ((unsigned long )(inbuf)) + (__cil_tmp120__3);
#line 5090 "gzip.preprocessed.c"
      mem_281__3 = (uch *)(__cil_tmp121__3);
#line 5090 "gzip.preprocessed.c"
      __cil_tmp122__3 = *mem_281__3;
#line 5090 "gzip.preprocessed.c"
      tmp___16__3 = (int )(__cil_tmp122__3);
#line 5090 "gzip.preprocessed.c"
      flags___0__3 = (uch )(tmp___16__3);
#line 5091 "gzip.preprocessed.c"
      __cil_tmp123__3 = (int )(flags___0__3);
#line 5091 "gzip.preprocessed.c"
      __cil_tmp124__3 = (__cil_tmp123__3) & (32);
#line 5098 "gzip.preprocessed.c"
      __cil_tmp130__3 = (int )(flags___0__3);
#line 5098 "gzip.preprocessed.c"
      __cil_tmp131__3 = (__cil_tmp130__3) & (2);
#line 5105 "gzip.preprocessed.c"
      __cil_tmp137__3 = (int )(flags___0__3);
#line 5105 "gzip.preprocessed.c"
      __cil_tmp138__3 = (__cil_tmp137__3) & (192);
#line 5112 "gzip.preprocessed.c"
      tmp___17__3 = inptr;
#line 5112 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5112 "gzip.preprocessed.c"
      __cil_tmp145__3 = (tmp___17__3) * (1UL);
#line 5112 "gzip.preprocessed.c"
      __cil_tmp146__3 = ((unsigned long )(inbuf)) + (__cil_tmp145__3);
#line 5112 "gzip.preprocessed.c"
      mem_282__3 = (uch *)(__cil_tmp146__3);
#line 5112 "gzip.preprocessed.c"
      __cil_tmp147__3 = *mem_282__3;
#line 5112 "gzip.preprocessed.c"
      tmp___19__3 = (int )(__cil_tmp147__3);
#line 5112 "gzip.preprocessed.c"
      stamp__3 = (ulg )(tmp___19__3);
#line 5113 "gzip.preprocessed.c"
      tmp___20__3 = inptr;
#line 5113 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5113 "gzip.preprocessed.c"
      __cil_tmp148__3 = (tmp___20__3) * (1UL);
#line 5113 "gzip.preprocessed.c"
      __cil_tmp149__3 = ((unsigned long )(inbuf)) + (__cil_tmp148__3);
#line 5113 "gzip.preprocessed.c"
      mem_283__3 = (uch *)(__cil_tmp149__3);
#line 5113 "gzip.preprocessed.c"
      __cil_tmp150__3 = *mem_283__3;
#line 5113 "gzip.preprocessed.c"
      tmp___22__3 = (int )(__cil_tmp150__3);
#line 5113 "gzip.preprocessed.c"
      __cil_tmp151__3 = (ulg )(tmp___22__3);
#line 5113 "gzip.preprocessed.c"
      __cil_tmp152__3 = (__cil_tmp151__3) << (8);
#line 5113 "gzip.preprocessed.c"
      stamp__3 = (stamp__3) | (__cil_tmp152__3);
#line 5114 "gzip.preprocessed.c"
      tmp___23__3 = inptr;
#line 5114 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5114 "gzip.preprocessed.c"
      __cil_tmp153__3 = (tmp___23__3) * (1UL);
#line 5114 "gzip.preprocessed.c"
      __cil_tmp154__3 = ((unsigned long )(inbuf)) + (__cil_tmp153__3);
#line 5114 "gzip.preprocessed.c"
      mem_284__3 = (uch *)(__cil_tmp154__3);
#line 5114 "gzip.preprocessed.c"
      __cil_tmp155__3 = *mem_284__3;
#line 5114 "gzip.preprocessed.c"
      tmp___25__3 = (int )(__cil_tmp155__3);
#line 5114 "gzip.preprocessed.c"
      __cil_tmp156__3 = (ulg )(tmp___25__3);
#line 5114 "gzip.preprocessed.c"
      __cil_tmp157__3 = (__cil_tmp156__3) << (16);
#line 5114 "gzip.preprocessed.c"
      stamp__3 = (stamp__3) | (__cil_tmp157__3);
#line 5115 "gzip.preprocessed.c"
      tmp___26__3 = inptr;
#line 5115 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5115 "gzip.preprocessed.c"
      __cil_tmp158__3 = (tmp___26__3) * (1UL);
#line 5115 "gzip.preprocessed.c"
      __cil_tmp159__3 = ((unsigned long )(inbuf)) + (__cil_tmp158__3);
#line 5115 "gzip.preprocessed.c"
      mem_285__3 = (uch *)(__cil_tmp159__3);
#line 5115 "gzip.preprocessed.c"
      __cil_tmp160__3 = *mem_285__3;
#line 5115 "gzip.preprocessed.c"
      tmp___28__3 = (int )(__cil_tmp160__3);
#line 5115 "gzip.preprocessed.c"
      __cil_tmp161__3 = (ulg )(tmp___28__3);
#line 5115 "gzip.preprocessed.c"
      __cil_tmp162__3 = (__cil_tmp161__3) << (24);
#line 5115 "gzip.preprocessed.c"
      stamp__3 = (stamp__3) | (__cil_tmp162__3);
#line 5117 "gzip.preprocessed.c"
      __cil_tmp164__3 = &time_stamp;
#line 5117 "gzip.preprocessed.c"
      *__cil_tmp164__3 = 0L;
#line 5118 "gzip.preprocessed.c"
      tmp___29__3 = inptr;
#line 5118 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5119 "gzip.preprocessed.c"
      tmp___30__3 = inptr;
#line 5119 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5120 "gzip.preprocessed.c"
      __cil_tmp165__3 = (int )(flags___0__3);
#line 5120 "gzip.preprocessed.c"
      __cil_tmp166__3 = (__cil_tmp165__3) & (2);
#line 5128 "gzip.preprocessed.c"
      __cil_tmp180__3 = (int )(flags___0__3);
#line 5128 "gzip.preprocessed.c"
      __cil_tmp181__3 = (__cil_tmp180__3) & (4);
#line 5129 "gzip.preprocessed.c"
      tmp___37__3 = inptr;
#line 5129 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5129 "gzip.preprocessed.c"
      __cil_tmp182__3 = (tmp___37__3) * (1UL);
#line 5129 "gzip.preprocessed.c"
      __cil_tmp183__3 = ((unsigned long )(inbuf)) + (__cil_tmp182__3);
#line 5129 "gzip.preprocessed.c"
      mem_288__3 = (uch *)(__cil_tmp183__3);
#line 5129 "gzip.preprocessed.c"
      __cil_tmp184__3 = *mem_288__3;
#line 5129 "gzip.preprocessed.c"
      tmp___39__3 = (int )(__cil_tmp184__3);
#line 5129 "gzip.preprocessed.c"
      len__3 = (unsigned int )(tmp___39__3);
#line 5130 "gzip.preprocessed.c"
      tmp___40__3 = inptr;
#line 5130 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5130 "gzip.preprocessed.c"
      __cil_tmp185__3 = (tmp___40__3) * (1UL);
#line 5130 "gzip.preprocessed.c"
      __cil_tmp186__3 = ((unsigned long )(inbuf)) + (__cil_tmp185__3);
#line 5130 "gzip.preprocessed.c"
      mem_289__3 = (uch *)(__cil_tmp186__3);
#line 5130 "gzip.preprocessed.c"
      __cil_tmp187__3 = *mem_289__3;
#line 5130 "gzip.preprocessed.c"
      tmp___42__3 = (int )(__cil_tmp187__3);
#line 5130 "gzip.preprocessed.c"
      __cil_tmp188__3 = (unsigned int )(tmp___42__3);
#line 5130 "gzip.preprocessed.c"
      __cil_tmp189__3 = (__cil_tmp188__3) << (8);
#line 5130 "gzip.preprocessed.c"
      len__3 = (len__3) | (__cil_tmp189__3);
#line 5135 "gzip.preprocessed.c"
      tmp___44__3 = len__3;
#line 5135 "gzip.preprocessed.c"
      len__3 = (len__3) - (1U);
#line 5135 "gzip.preprocessed.c"
      tmp___43__3 = inptr;
#line 5135 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5135 "gzip.preprocessed.c"
      tmp___44__3 = len__3;
#line 5135 "gzip.preprocessed.c"
      len__3 = (len__3) - (1U);
#line 5135 "gzip.preprocessed.c"
      tmp___43__3 = inptr;
#line 5135 "gzip.preprocessed.c"
      inptr = (inptr) + (1U);
#line 5135 "gzip.preprocessed.c"
      tmp___44__3 = len__3;
#line 5135 "gzip.preprocessed.c"
      len__3 = (len__3) - (1U);
#line 5137 "gzip.preprocessed.c"
      __cil_tmp195__3 = (int )(flags___0__3);
#line 5137 "gzip.preprocessed.c"
      __cil_tmp196__3 = (__cil_tmp195__3) & (8);
#line 5157 "gzip.preprocessed.c"
      __cil_tmp216__3 = (int )(flags___0__3);
#line 5157 "gzip.preprocessed.c"
      __cil_tmp217__3 = (__cil_tmp216__3) & (16);
#line 5161 "gzip.preprocessed.c"
      __cil_tmp221__3 = (2UL) * (8UL);
#line 5161 "gzip.preprocessed.c"
      __cil_tmp222__3 = (unsigned long )(inptr);
#line 5161 "gzip.preprocessed.c"
      __cil_tmp223__3 = (__cil_tmp222__3) + (__cil_tmp221__3);
#line 5161 "gzip.preprocessed.c"
      header_bytes = (long )(__cil_tmp223__3);
#line 5186 "gzip.preprocessed.c"
      __cil_tmp259__3 = &method;
#line 5186 "gzip.preprocessed.c"
      __cil_tmp260__3 = *__cil_tmp259__3;
#line 5186 "gzip.preprocessed.c"
      __cil_tmp261__3 = &method;
#line 5186 "gzip.preprocessed.c"
      //exiting get_method
#line 5186 "gzip.preprocessed.c"
      __return__3 = *__cil_tmp261__3;
#line 4791 "gzip.preprocessed.c"
      *__cil_tmp30__2 = __return__3;
    }
#line 4792 "gzip.preprocessed.c"
    __cil_tmp31__2 = &method;
#line 4792 "gzip.preprocessed.c"
    __cil_tmp32__2 = *__cil_tmp31__2;
#line 4801 "gzip.preprocessed.c"
    //tmp___8__2 = fileno(stdout);
    {
#line 4801 "gzip.preprocessed.c"
      struct _IO_FILE * __arg_tmp_0__3  = stdout;
#line 4801 "gzip.preprocessed.c"
      int __return__3;
#line 4801 "gzip.preprocessed.c"
      tmp___8__2 = __return__3;
    }
#line 4801 "gzip.preprocessed.c"
    //tmp___9__2 = fileno(stdin);
    {
#line 4801 "gzip.preprocessed.c"
      struct _IO_FILE * __arg_tmp_0__3  = stdin;
#line 4801 "gzip.preprocessed.c"
      int __return__3;
#line 4801 "gzip.preprocessed.c"
      tmp___9__2 = __return__3;
    }
#line 4801 "gzip.preprocessed.c"
    //tmp___10__2 = *work(tmp___9__2, tmp___8__2);
    {
#line 4801 "gzip.preprocessed.c"
      int  __arg_tmp_0__3  = tmp___9__2;
#line 4801 "gzip.preprocessed.c"
      int  __arg_tmp_1__3  = tmp___8__2;
#line 4801 "gzip.preprocessed.c"
      int __return__3;
#line 3944 "gzip.preprocessed.c"
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
#line 3947 "gzip.preprocessed.c"
      orig_crc__3 = (ulg )(0);
#line 3948 "gzip.preprocessed.c"
      orig_len___0__3 = (ulg )(0);
#line 3951 "gzip.preprocessed.c"
      ifd = in__3;
#line 3952 "gzip.preprocessed.c"
      ofd = out__3;
#line 3953 "gzip.preprocessed.c"
      __cil_tmp24__3 = (void *)(0);
#line 3953 "gzip.preprocessed.c"
      __cil_tmp25__3 = (uch *)(__cil_tmp24__3);
#line 3953 "gzip.preprocessed.c"
      //updcrc(__cil_tmp25__3, 0U);
      {
#line 3953 "gzip.preprocessed.c"
        uch * __arg_tmp_0__4  = __cil_tmp25__3;
#line 3953 "gzip.preprocessed.c"
        unsigned int  __arg_tmp_1__4  = 0U;
#line 4029 "gzip.preprocessed.c"
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
#line 4035 "gzip.preprocessed.c"
        __cil_tmp5__4 = (void *)(0);
#line 4035 "gzip.preprocessed.c"
        __cil_tmp6__4 = (unsigned long )(__cil_tmp5__4);
#line 4035 "gzip.preprocessed.c"
        __cil_tmp7__4 = (unsigned long )(s__4);
#line 4036 "gzip.preprocessed.c"
        c__4 = (ulg )(4294967295L);
#line 4043 "gzip.preprocessed.c"
        crc___0 = c__4;
#line 4044 "gzip.preprocessed.c"
        //exiting updcrc
#line 4044 "gzip.preprocessed.c"
        __return__4 = (c__4) ^ (4294967295UL);
      }
#line 3958 "gzip.preprocessed.c"
      __cil_tmp108__3 = &method;
#line 3958 "gzip.preprocessed.c"
      __cil_tmp109__3 = *__cil_tmp108__3;
#line 3959 "gzip.preprocessed.c"
      //tmp__3 = inflate();
      {
#line 3959 "gzip.preprocessed.c"
        int __return__4;
#line 2305 "gzip.preprocessed.c"
        //enter inflate
        int  e__4;
        int  r__4;
        unsigned int  h__4;
        int * __cil_tmp4__4;
        int  __cil_tmp5__4;
#line 2310 "gzip.preprocessed.c"
        outcnt = 0U;
#line 2311 "gzip.preprocessed.c"
        bk = 0U;
#line 2312 "gzip.preprocessed.c"
        bb = (ulg )(0);
#line 2313 "gzip.preprocessed.c"
        h__4 = 0U;
#line 2315 "gzip.preprocessed.c"
        hufts = 0U;
#line 2316 "gzip.preprocessed.c"
        //r__4 = inflate_block(&e__4);
        {
#line 2316 "gzip.preprocessed.c"
          int * __arg_tmp_0__5  = &e__5;
#line 2316 "gzip.preprocessed.c"
          int __return__5;
#line 2281 "gzip.preprocessed.c"
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
#line 2287 "gzip.preprocessed.c"
          b__5 = bb;
#line 2288 "gzip.preprocessed.c"
          k__5 = bk;
#line 2289 "gzip.preprocessed.c"
          tmp__5 = inptr;
#line 2289 "gzip.preprocessed.c"
          inptr = (inptr) + (1U);
#line 2289 "gzip.preprocessed.c"
          __cil_tmp14__5 = (tmp__5) * (1UL);
#line 2289 "gzip.preprocessed.c"
          __cil_tmp15__5 = ((unsigned long )(inbuf)) + (__cil_tmp14__5);
#line 2289 "gzip.preprocessed.c"
          mem_28__5 = (uch *)(__cil_tmp15__5);
#line 2289 "gzip.preprocessed.c"
          __cil_tmp16__5 = *mem_28__5;
#line 2289 "gzip.preprocessed.c"
          tmp___1__5 = (int )(__cil_tmp16__5);
#line 2289 "gzip.preprocessed.c"
          __cil_tmp17__5 = (uch )(tmp___1__5);
#line 2289 "gzip.preprocessed.c"
          __cil_tmp18__5 = (ulg )(__cil_tmp17__5);
#line 2289 "gzip.preprocessed.c"
          __cil_tmp19__5 = (__cil_tmp18__5) << (k__5);
#line 2289 "gzip.preprocessed.c"
          b__5 = (b__5) | (__cil_tmp19__5);
#line 2289 "gzip.preprocessed.c"
          k__5 = (k__5) + (8U);
#line 2290 "gzip.preprocessed.c"
          __cil_tmp20__5 = (int )(b__5);
#line 2290 "gzip.preprocessed.c"
          *e__5 = (__cil_tmp20__5) & (1);
#line 2291 "gzip.preprocessed.c"
          b__5 = (b__5) >> (1);
#line 2291 "gzip.preprocessed.c"
          k__5 = (k__5) - (1U);
#line 2293 "gzip.preprocessed.c"
          __cil_tmp27__5 = (unsigned int )(b__5);
#line 2293 "gzip.preprocessed.c"
          t__5 = (__cil_tmp27__5) & (3U);
#line 2294 "gzip.preprocessed.c"
          b__5 = (b__5) >> (2);
#line 2294 "gzip.preprocessed.c"
          k__5 = (k__5) - (2U);
#line 2295 "gzip.preprocessed.c"
          bb = b__5;
#line 2296 "gzip.preprocessed.c"
          bk = k__5;
#line 2298 "gzip.preprocessed.c"
          //tmp___5__5 = inflate_dynamic();
          {
#line 2298 "gzip.preprocessed.c"
            int __return__6;
#line 2164 "gzip.preprocessed.c"
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
#line 2181 "gzip.preprocessed.c"
            b__6 = bb;
#line 2182 "gzip.preprocessed.c"
            k__6 = bk;
#line 2184 "gzip.preprocessed.c"
            __cil_tmp54__6 = (unsigned int )(b__6);
#line 2184 "gzip.preprocessed.c"
            __cil_tmp55__6 = (__cil_tmp54__6) & (31U);
#line 2184 "gzip.preprocessed.c"
            nl__6 = (257U) + (__cil_tmp55__6);
#line 2185 "gzip.preprocessed.c"
            b__6 = (b__6) >> (5);
#line 2185 "gzip.preprocessed.c"
            k__6 = (k__6) - (5U);
#line 2186 "gzip.preprocessed.c"
            tmp___2__6 = inptr;
#line 2186 "gzip.preprocessed.c"
            inptr = (inptr) + (1U);
#line 2186 "gzip.preprocessed.c"
            __cil_tmp56__6 = (tmp___2__6) * (1UL);
#line 2186 "gzip.preprocessed.c"
            __cil_tmp57__6 = ((unsigned long )(inbuf)) + (__cil_tmp56__6);
#line 2186 "gzip.preprocessed.c"
            mem_213__6 = (uch *)(__cil_tmp57__6);
#line 2186 "gzip.preprocessed.c"
            __cil_tmp58__6 = *mem_213__6;
#line 2186 "gzip.preprocessed.c"
            tmp___4__6 = (int )(__cil_tmp58__6);
#line 2186 "gzip.preprocessed.c"
            __cil_tmp59__6 = (uch )(tmp___4__6);
#line 2186 "gzip.preprocessed.c"
            __cil_tmp60__6 = (ulg )(__cil_tmp59__6);
#line 2186 "gzip.preprocessed.c"
            __cil_tmp61__6 = (__cil_tmp60__6) << (k__6);
#line 2186 "gzip.preprocessed.c"
            b__6 = (b__6) | (__cil_tmp61__6);
#line 2186 "gzip.preprocessed.c"
            k__6 = (k__6) + (8U);
#line 2187 "gzip.preprocessed.c"
            __cil_tmp62__6 = (unsigned int )(b__6);
#line 2187 "gzip.preprocessed.c"
            __cil_tmp63__6 = (__cil_tmp62__6) & (31U);
#line 2187 "gzip.preprocessed.c"
            nd__6 = (1U) + (__cil_tmp63__6);
#line 2188 "gzip.preprocessed.c"
            b__6 = (b__6) >> (5);
#line 2188 "gzip.preprocessed.c"
            k__6 = (k__6) - (5U);
#line 2189 "gzip.preprocessed.c"
            tmp___5__6 = inptr;
#line 2189 "gzip.preprocessed.c"
            inptr = (inptr) + (1U);
#line 2189 "gzip.preprocessed.c"
            __cil_tmp64__6 = (tmp___5__6) * (1UL);
#line 2189 "gzip.preprocessed.c"
            __cil_tmp65__6 = ((unsigned long )(inbuf)) + (__cil_tmp64__6);
#line 2189 "gzip.preprocessed.c"
            mem_214__6 = (uch *)(__cil_tmp65__6);
#line 2189 "gzip.preprocessed.c"
            __cil_tmp66__6 = *mem_214__6;
#line 2189 "gzip.preprocessed.c"
            tmp___7__6 = (int )(__cil_tmp66__6);
#line 2189 "gzip.preprocessed.c"
            __cil_tmp67__6 = (uch )(tmp___7__6);
#line 2189 "gzip.preprocessed.c"
            __cil_tmp68__6 = (ulg )(__cil_tmp67__6);
#line 2189 "gzip.preprocessed.c"
            __cil_tmp69__6 = (__cil_tmp68__6) << (k__6);
#line 2189 "gzip.preprocessed.c"
            b__6 = (b__6) | (__cil_tmp69__6);
#line 2189 "gzip.preprocessed.c"
            k__6 = (k__6) + (8U);
#line 2190 "gzip.preprocessed.c"
            __cil_tmp70__6 = (unsigned int )(b__6);
#line 2190 "gzip.preprocessed.c"
            __cil_tmp71__6 = (__cil_tmp70__6) & (15U);
#line 2190 "gzip.preprocessed.c"
            nb__6 = (4U) + (__cil_tmp71__6);
#line 2191 "gzip.preprocessed.c"
            b__6 = (b__6) >> (4);
#line 2191 "gzip.preprocessed.c"
            k__6 = (k__6) - (4U);
#line 2194 "gzip.preprocessed.c"
            j__6 = 0U;
#line 2197 "gzip.preprocessed.c"
            __cil_tmp78__6 = (j__6) * (4UL);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp79__6 = ((unsigned long )(border)) + (__cil_tmp78__6);
#line 2197 "gzip.preprocessed.c"
            mem_216__6 = (unsigned int *)(__cil_tmp79__6);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp80__6 = *mem_216__6;
#line 2197 "gzip.preprocessed.c"
            __cil_tmp81__6 = (__cil_tmp80__6) * (4UL);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp82__6 = ((unsigned long )(ll__6)) + (__cil_tmp81__6);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp83__6 = (unsigned int )(b__6);
#line 2197 "gzip.preprocessed.c"
            mem_217__6 = (unsigned int *)(__cil_tmp82__6);
#line 2197 "gzip.preprocessed.c"
            *mem_217__6 = (__cil_tmp83__6) & (7U);
#line 2198 "gzip.preprocessed.c"
            b__6 = (b__6) >> (3);
#line 2198 "gzip.preprocessed.c"
            k__6 = (k__6) - (3U);
#line 2194 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp78__6 = (j__6) * (4UL);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp79__6 = ((unsigned long )(border)) + (__cil_tmp78__6);
#line 2197 "gzip.preprocessed.c"
            mem_216__6 = (unsigned int *)(__cil_tmp79__6);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp80__6 = *mem_216__6;
#line 2197 "gzip.preprocessed.c"
            __cil_tmp81__6 = (__cil_tmp80__6) * (4UL);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp82__6 = ((unsigned long )(ll__6)) + (__cil_tmp81__6);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp83__6 = (unsigned int )(b__6);
#line 2197 "gzip.preprocessed.c"
            mem_217__6 = (unsigned int *)(__cil_tmp82__6);
#line 2197 "gzip.preprocessed.c"
            *mem_217__6 = (__cil_tmp83__6) & (7U);
#line 2198 "gzip.preprocessed.c"
            b__6 = (b__6) >> (3);
#line 2198 "gzip.preprocessed.c"
            k__6 = (k__6) - (3U);
#line 2194 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2196 "gzip.preprocessed.c"
            tmp___8__6 = inptr;
#line 2196 "gzip.preprocessed.c"
            inptr = (inptr) + (1U);
#line 2196 "gzip.preprocessed.c"
            __cil_tmp72__6 = (tmp___8__6) * (1UL);
#line 2196 "gzip.preprocessed.c"
            __cil_tmp73__6 = ((unsigned long )(inbuf)) + (__cil_tmp72__6);
#line 2196 "gzip.preprocessed.c"
            mem_215__6 = (uch *)(__cil_tmp73__6);
#line 2196 "gzip.preprocessed.c"
            __cil_tmp74__6 = *mem_215__6;
#line 2196 "gzip.preprocessed.c"
            tmp___10__6 = (int )(__cil_tmp74__6);
#line 2196 "gzip.preprocessed.c"
            __cil_tmp75__6 = (uch )(tmp___10__6);
#line 2196 "gzip.preprocessed.c"
            __cil_tmp76__6 = (ulg )(__cil_tmp75__6);
#line 2196 "gzip.preprocessed.c"
            __cil_tmp77__6 = (__cil_tmp76__6) << (k__6);
#line 2196 "gzip.preprocessed.c"
            b__6 = (b__6) | (__cil_tmp77__6);
#line 2196 "gzip.preprocessed.c"
            k__6 = (k__6) + (8U);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp78__6 = (j__6) * (4UL);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp79__6 = ((unsigned long )(border)) + (__cil_tmp78__6);
#line 2197 "gzip.preprocessed.c"
            mem_216__6 = (unsigned int *)(__cil_tmp79__6);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp80__6 = *mem_216__6;
#line 2197 "gzip.preprocessed.c"
            __cil_tmp81__6 = (__cil_tmp80__6) * (4UL);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp82__6 = ((unsigned long )(ll__6)) + (__cil_tmp81__6);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp83__6 = (unsigned int )(b__6);
#line 2197 "gzip.preprocessed.c"
            mem_217__6 = (unsigned int *)(__cil_tmp82__6);
#line 2197 "gzip.preprocessed.c"
            *mem_217__6 = (__cil_tmp83__6) & (7U);
#line 2198 "gzip.preprocessed.c"
            b__6 = (b__6) >> (3);
#line 2198 "gzip.preprocessed.c"
            k__6 = (k__6) - (3U);
#line 2194 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp78__6 = (j__6) * (4UL);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp79__6 = ((unsigned long )(border)) + (__cil_tmp78__6);
#line 2197 "gzip.preprocessed.c"
            mem_216__6 = (unsigned int *)(__cil_tmp79__6);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp80__6 = *mem_216__6;
#line 2197 "gzip.preprocessed.c"
            __cil_tmp81__6 = (__cil_tmp80__6) * (4UL);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp82__6 = ((unsigned long )(ll__6)) + (__cil_tmp81__6);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp83__6 = (unsigned int )(b__6);
#line 2197 "gzip.preprocessed.c"
            mem_217__6 = (unsigned int *)(__cil_tmp82__6);
#line 2197 "gzip.preprocessed.c"
            *mem_217__6 = (__cil_tmp83__6) & (7U);
#line 2198 "gzip.preprocessed.c"
            b__6 = (b__6) >> (3);
#line 2198 "gzip.preprocessed.c"
            k__6 = (k__6) - (3U);
#line 2194 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp78__6 = (j__6) * (4UL);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp79__6 = ((unsigned long )(border)) + (__cil_tmp78__6);
#line 2197 "gzip.preprocessed.c"
            mem_216__6 = (unsigned int *)(__cil_tmp79__6);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp80__6 = *mem_216__6;
#line 2197 "gzip.preprocessed.c"
            __cil_tmp81__6 = (__cil_tmp80__6) * (4UL);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp82__6 = ((unsigned long )(ll__6)) + (__cil_tmp81__6);
#line 2197 "gzip.preprocessed.c"
            __cil_tmp83__6 = (unsigned int )(b__6);
#line 2197 "gzip.preprocessed.c"
            mem_217__6 = (unsigned int *)(__cil_tmp82__6);
#line 2197 "gzip.preprocessed.c"
            *mem_217__6 = (__cil_tmp83__6) & (7U);
#line 2198 "gzip.preprocessed.c"
            b__6 = (b__6) >> (3);
#line 2198 "gzip.preprocessed.c"
            k__6 = (k__6) - (3U);
#line 2194 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp84__6 = (j__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp85__6 = ((unsigned long )(border)) + (__cil_tmp84__6);
#line 2201 "gzip.preprocessed.c"
            mem_218__6 = (unsigned int *)(__cil_tmp85__6);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp86__6 = *mem_218__6;
#line 2201 "gzip.preprocessed.c"
            __cil_tmp87__6 = (__cil_tmp86__6) * (4UL);
#line 2201 "gzip.preprocessed.c"
            __cil_tmp88__6 = ((unsigned long )(ll__6)) + (__cil_tmp87__6);
#line 2201 "gzip.preprocessed.c"
            mem_219__6 = (unsigned int *)(__cil_tmp88__6);
#line 2201 "gzip.preprocessed.c"
            *mem_219__6 = 0U;
#line 2200 "gzip.preprocessed.c"
            j__6 = (j__6) + (1U);
#line 2202 "gzip.preprocessed.c"
            __cil_tmp89__6 = &bl__6;
#line 2202 "gzip.preprocessed.c"
            *__cil_tmp89__6 = 7;
#line 2203 "gzip.preprocessed.c"
            __cil_tmp90__6 = (0) * (4UL);
#line 2203 "gzip.preprocessed.c"
            __cil_tmp91__6 = ((unsigned long )(ll__6)) + (__cil_tmp90__6);
#line 2203 "gzip.preprocessed.c"
            __cil_tmp92__6 = (unsigned int *)(__cil_tmp91__6);
#line 2203 "gzip.preprocessed.c"
            __cil_tmp93__6 = (void *)(0);
#line 2203 "gzip.preprocessed.c"
            __cil_tmp94__6 = (ush *)(__cil_tmp93__6);
#line 2203 "gzip.preprocessed.c"
            __cil_tmp95__6 = (void *)(0);
#line 2203 "gzip.preprocessed.c"
            __cil_tmp96__6 = (ush *)(__cil_tmp95__6);
#line 2203 "gzip.preprocessed.c"
            //i__6 = huft_build(__cil_tmp92__6, 19U, 19U, __cil_tmp94__6, __cil_tmp96__6, &tl__6, &bl__6);
            {
#line 2203 "gzip.preprocessed.c"
              unsigned int * __arg_tmp_0__7  = __cil_tmp92__6;
#line 2203 "gzip.preprocessed.c"
              unsigned int  __arg_tmp_1__7  = 19U;
#line 2203 "gzip.preprocessed.c"
              unsigned int  __arg_tmp_2__7  = 19U;
#line 2203 "gzip.preprocessed.c"
              ush * __arg_tmp_3__7  = __cil_tmp94__6;
#line 2203 "gzip.preprocessed.c"
              ush * __arg_tmp_4__7  = __cil_tmp96__6;
#line 2203 "gzip.preprocessed.c"
              struct huft ** __arg_tmp_5__7  = &tl__7;
#line 2203 "gzip.preprocessed.c"
              int * __arg_tmp_6__7  = &bl__7;
#line 2203 "gzip.preprocessed.c"
              int __return__7;
#line 1849 "gzip.preprocessed.c"
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
              union __anonunion_v_47  r_v168__7;
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
#line 1877 "gzip.preprocessed.c"
              __cil_tmp36__7 = (0) * (4UL);
#line 1877 "gzip.preprocessed.c"
              __cil_tmp37__7 = ((unsigned long )(c__7)) + (__cil_tmp36__7);
#line 1877 "gzip.preprocessed.c"
              __cil_tmp38__7 = (unsigned int *)(__cil_tmp37__7);
#line 1877 "gzip.preprocessed.c"
              __cil_tmp39__7 = (voidp )(__cil_tmp38__7);
#line 1877 "gzip.preprocessed.c"
              //memset(__cil_tmp39__7, 0, 68UL);
              {
#line 1877 "gzip.preprocessed.c"
                voidp  __arg_tmp_0__8  = __cil_tmp39__7;
#line 1877 "gzip.preprocessed.c"
                int  __arg_tmp_1__8  = 0;
#line 1877 "gzip.preprocessed.c"
                unsigned long  __arg_tmp_2__8  = 68UL;
              }
#line 1878 "gzip.preprocessed.c"
              p__7 = b__7;
#line 1878 "gzip.preprocessed.c"
              i__7 = n__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp40__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp41__7 = (__cil_tmp40__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp42__7 = ((unsigned long )(c__7)) + (__cil_tmp41__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp43__7 = *p__7;
#line 1881 "gzip.preprocessed.c"
              __cil_tmp44__7 = (__cil_tmp43__7) * (4UL);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp45__7 = ((unsigned long )(c__7)) + (__cil_tmp44__7);
#line 1881 "gzip.preprocessed.c"
              mem_171__7 = (unsigned int *)(__cil_tmp45__7);
#line 1881 "gzip.preprocessed.c"
              __cil_tmp46__7 = *mem_171__7;
#line 1881 "gzip.preprocessed.c"
              mem_172__7 = (unsigned int *)(__cil_tmp42__7);
#line 1881 "gzip.preprocessed.c"
              *mem_172__7 = (__cil_tmp46__7) + (1U);
#line 1882 "gzip.preprocessed.c"
              p__7 = (p__7) + (1);
#line 1879 "gzip.preprocessed.c"
              i__7 = (i__7) - (1U);
#line 1884 "gzip.preprocessed.c"
              __cil_tmp47__7 = (0) * (4UL);
#line 1884 "gzip.preprocessed.c"
              __cil_tmp48__7 = ((unsigned long )(c__7)) + (__cil_tmp47__7);
#line 1884 "gzip.preprocessed.c"
              mem_173__7 = (unsigned int *)(__cil_tmp48__7);
#line 1884 "gzip.preprocessed.c"
              __cil_tmp49__7 = *mem_173__7;
#line 1886 "gzip.preprocessed.c"
              __cil_tmp50__7 = (void *)(0);
#line 1886 "gzip.preprocessed.c"
              *t__7 = (struct huft *)(__cil_tmp50__7);
#line 1887 "gzip.preprocessed.c"
              *m__7 = 0;
#line 1888 "gzip.preprocessed.c"
              //exiting huft_build
#line 1888 "gzip.preprocessed.c"
              __return__7 = 0;
#line 2203 "gzip.preprocessed.c"
              i__6 = __return__7;
            }
#line 2209 "gzip.preprocessed.c"
            n__6 = (nl__6) + (nd__6);
#line 2210 "gzip.preprocessed.c"
            __cil_tmp99__6 = &bl__6;
#line 2210 "gzip.preprocessed.c"
            __cil_tmp100__6 = *__cil_tmp99__6;
#line 2210 "gzip.preprocessed.c"
            __cil_tmp101__6 = (__cil_tmp100__6) * (2UL);
#line 2210 "gzip.preprocessed.c"
            __cil_tmp102__6 = ((unsigned long )(mask_bits)) + (__cil_tmp101__6);
#line 2210 "gzip.preprocessed.c"
            mem_220__6 = (ush *)(__cil_tmp102__6);
#line 2210 "gzip.preprocessed.c"
            __cil_tmp103__6 = *mem_220__6;
#line 2210 "gzip.preprocessed.c"
            m__6 = (unsigned int )(__cil_tmp103__6);
#line 2211 "gzip.preprocessed.c"
            l__6 = 0U;
#line 2211 "gzip.preprocessed.c"
            i__6 = (int )(l__6);
#line 2212 "gzip.preprocessed.c"
            __cil_tmp104__6 = (unsigned int )(i__6);
#line 2214 "gzip.preprocessed.c"
            __cil_tmp105__6 = &bl__6;
#line 2214 "gzip.preprocessed.c"
            __cil_tmp106__6 = *__cil_tmp105__6;
#line 2214 "gzip.preprocessed.c"
            __cil_tmp107__6 = (unsigned int )(__cil_tmp106__6);
#line 2215 "gzip.preprocessed.c"
            __cil_tmp114__6 = &td__6;
#line 2215 "gzip.preprocessed.c"
            __cil_tmp115__6 = (unsigned int )(b__6);
#line 2215 "gzip.preprocessed.c"
            __cil_tmp116__6 = (__cil_tmp115__6) & (m__6);
#line 2215 "gzip.preprocessed.c"
            __cil_tmp117__6 = &tl__6;
#line 2215 "gzip.preprocessed.c"
            __cil_tmp118__6 = *__cil_tmp117__6;
#line 2215 "gzip.preprocessed.c"
            *__cil_tmp114__6 = (__cil_tmp118__6) + (__cil_tmp116__6);
#line 2215 "gzip.preprocessed.c"
            __cil_tmp119__6 = &td__6;
#line 2215 "gzip.preprocessed.c"
            __cil_tmp120__6 = *__cil_tmp119__6;
#line 2215 "gzip.preprocessed.c"
            __cil_tmp121__6 = (unsigned long )(__cil_tmp120__6);
#line 2215 "gzip.preprocessed.c"
            __cil_tmp122__6 = (__cil_tmp121__6) + (1);
#line 2215 "gzip.preprocessed.c"
            mem_222__6 = (uch *)(__cil_tmp122__6);
#line 2215 "gzip.preprocessed.c"
            __cil_tmp123__6 = *mem_222__6;
