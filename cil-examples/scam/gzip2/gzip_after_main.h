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
