#include <signal.h>
#include <setjmp.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <string.h>

#define GBSIZE 256
#define FNSIZE 128
#define LBSIZE 4096
#define BLKSIZE 4096
#define NBRA 5
#define ESIZE 256

const int NBLK = 2047;
const int CBRA = 1;
const int CCHR = 2;  
const int CDOT = 4;  
const int CCL = 6;  
const int NCCL = 8;  
const int CDOL = 10;
const int CEOF = 11;  
const int CKET = 12;  
const int CBACK = 14;  
const int CCIRC = 15;  
const int STAR = 01;
const int READ = 0;  
const int WRITE = 1;
int  peekc, lastc, given, ninbuf, io, pflag;
int  vflag  = 1, oflag, listf, listn, col, tfile  = -1, tline, iblock  = -1, oblock  = -1, ichanged, nleft;
int  names[26], nbra, fchange;
unsigned nlall = 128;  
unsigned int  *addr1, *addr2, *dot, *dol, *zero;
long  count;
char  savedfile[FNSIZE], file[FNSIZE], linebuf[LBSIZE], rhsbuf[LBSIZE/2], expbuf[ESIZE+4];
char  genbuf[LBSIZE], *nextip, *linebp, *globp, *mktemp(char *), tmpXXXXX[50] = "/tmp/eXXXXX";
char  *tfname, *loc1, *loc2, ibuff[BLKSIZE], obuff[BLKSIZE], WRERR[]  = "WRITE ERROR", *braslist[NBRA], *braelist[NBRA];
char  line[70];  
char  *linp  = line;
int advance(char *lp, char *ep);
int append(int (*f)(void), unsigned int *a);
void blkio(int b, char *buf, long (*iofcn)(int, void*, unsigned long));
void compile(int eof); 
int execute(unsigned int *addr);  
void exfile(void);
void filename(int comm); 
char *getblock(unsigned int atl, int iof); 
int getchr(void);
int getcopy(void);  
int getfile(void);  
char *getline_blk(unsigned int tl);   
void global(int k);  
void init(void);
void newline(void);  
void nonzero(void);  
void onhup(int n);
void print(void);  
void putchr_(int ac);
void putd(void);  
void putfile(void);  
int putline(void);  
void puts_(char *sp);
void quit(int n); 
jmp_buf  savej;
void readfile(const char * c);
int getch_(void);
void ungetch_(int c);
void search(const char* re);
void printcommand(void);
void drawline();
typedef void  (*SIG_TYP)(int);
SIG_TYP  oldhup, oldquit;

int main(int argc, char *argv[]) {
  if (argc != 3) { 
    fprintf(stderr, "Usage: ./grep searchre file(s)\n"); 
    exit(ARGC_ERROR); 
  }
  zero = (unsigned *)malloc(nlall * sizeof(unsigned));  
  tfname = mktemp(tmpXXXXX);  
  init();

  readfile(argv[2]);
  search(argv[1]);
  printf("\nquitting...\n");  
  exit(1);
}

int advance(char *lp, char *ep) {
   char *curlp; 
   int i;
   return 0;
}

int append(int (*f)(void), unsigned int *a) {
  unsigned int *a1, *a2, *rdot;
  int nline, tl;
  nline = 0;
  dot = a;
  while ((*f)() == 0) {
    if ((dol-zero)+1 >= nlall) {
      unsigned *ozero = zero;
      nlall += 1024;
      if ((zero = (unsigned *)realloc((char *)zero, nlall*sizeof(unsigned)))==NULL) {
        onhup(0); 
      }
      dot += zero - ozero;
      dol += zero - ozero;
    }
    tl = putline();
    nline++;
    a1 = ++dol;
    a2 = a1+1; 
    rdot = ++dot;
    while (a1 > rdot) { *--a2 = *--a1; }
    *rdot = tl;
  }
  return(nline);
}
void blkio(int b, char *buf, long (*iofcn)(int, void*, unsigned long)) {
  lseek(tfile, (long)b*BLKSIZE, 0);
}

void compile(int eof) {
  int c, cclcnt;
  char *ep = expbuf, *lastep, bracket[NBRA], *bracketp = bracket;
  if ((c = getchr()) == '\n') { peekc = c;  c = eof; }
  if (c == eof) { return; }
  nbra = 0;
  if (c=='^') {
    c = getchr();
    *ep++ = CCIRC;
  }
  peekc = c;
  lastep = 0;
  for (;;) {
    c = getchr();
    if (c == '\n') {
      peekc = c;
      c = eof;
    }
    if (c==eof) {
      *ep++ = CEOF;
      return;
    }
    if (c!='*') { lastep = ep; }
    switch (c) {
      case '\\':
        if ((c = getchr())=='(') {
            *bracketp++ = nbra;
            *ep++ = CBRA;
            *ep++ = nbra++;
            continue;
        }
        if (c == ')') {
          *ep++ = CKET;
          *ep++ = *--bracketp;
          continue;
        }
        if (c>='1' && c<'1'+NBRA) {
          *ep++ = CBACK;
          *ep++ = c-'1';
          continue;
        }
        *ep++ = CCHR;
        *ep++ = c;
        continue;
      case '.':
        *ep++ = CDOT;
        continue;
      case '*':
        if (lastep==0 || *lastep==CBRA || *lastep==CKET) { goto defchar; }
        *lastep |= STAR; 
        continue;
      case '$':
        if ((peekc=getchr()) != eof && peekc!='\n') { goto defchar; }
        *ep++ = CDOL;
        continue;
      case '[':
        *ep++ = CCL;
        *ep++ = 0;  cclcnt = 1;
        if ((c=getchr()) == '^') {
          c = getchr();
          ep[-2] = NCCL; 
        }
        do {
          if (c=='-' && ep[-1]!=0) {
            if ((c=getchr())==']') {
              *ep++ = '-';
              cclcnt++;
              break;
            }
            while (ep[-1] < c) {
              *ep = ep[-1] + 1;
              ep++;  cclcnt++;
            }
          }
          *ep++ = c;
          cclcnt++;
        } while ((c = getchr()) != ']');
        lastep[1] = cclcnt;  continue;
      defchar:  default:  *ep++ = CCHR;  *ep++ = c;
    }
  }
}

int execute(unsigned int *addr) {  char *p1, *p2 = expbuf;  int c;
  for (c = 0; c < NBRA; c++) {  braslist[c] = 0;  braelist[c] = 0;  }
  if (addr == (unsigned *)0) {
    if (*p2 == CCIRC) { return(0); }  p1 = loc2; } else if (addr == zero) { return(0); }
  else { p1 = getline_blk(*addr); }
  if (*p2 == CCIRC) {  loc1 = p1;  return(advance(p1, p2+1)); }
  if (*p2 == CCHR) { c = p2[1];
    do {  if (*p1 != c) { continue; }  if (advance(p1, p2)) {  loc1 = p1;  return(1); }
    } while (*p1++);
    return(0);
  }
  do {if (advance(p1, p2)) {  loc1 = p1;  return(1);  }  } while (*p1++);  return(0);
}
void exfile(void) {  close(io);  io = -1;  if (vflag) {  putd();  putchr_('\n'); }  }

void filename(int comm) {  char *p1, *p2;  int c;  count = 0;  c = getchr();
  if (c == '\n' || c == EOF) {
    p1 = savedfile;  p2 = file;  while ((*p2++ = *p1++) == 1) { }  return;
  }
  while ((c = getchr()) == ' ') { } p1 = file;
  do {
    *p1++ = c;
  } while ((c = getchr()) != '\n');
  *p1++ = 0;
  if (savedfile[0] == 0||comm == 'e'||comm == 'f') { p1 = savedfile;  p2 = file;  while ((*p1++ = *p2++) == 1) { } }
}

char * getblock(unsigned int atl, int iof) {  int off, bno = (atl/(BLKSIZE/2));  off = (atl<<1) & (BLKSIZE-1) & ~03;
  if (bno >= NBLK) {  lastc = '\n';}  nleft = BLKSIZE - off;
  if (bno==iblock) {  ichanged |= iof;  return(ibuff+off);  }  if (bno==oblock)  { return(obuff+off);  }
  if (iof==READ) {
    if (ichanged) { blkio(iblock, ibuff, (long (*)(int, void*, unsigned long))write); }
    ichanged = 0;  iblock = bno;  blkio(bno, ibuff, read);  return(ibuff+off);
  }
  if (oblock>=0) { blkio(oblock, obuff, (long (*)(int, void*, unsigned long))write); }
  oblock = bno;  return(obuff+off);
}
char inputbuf[GBSIZE];

int getchr(void) {  char c;
  if ((lastc=peekc)) {  peekc = 0;  return(lastc); }
  if (globp) {  if ((lastc = *globp++) != 0) { return(lastc); }  globp = 0;  return(EOF);  }
  if (read(0, &c, 1) <= 0) { return(lastc = EOF); }
  lastc = c&0177;  return(lastc);
}

int getfile(void) {  int c;  char *lp = linebuf, *fp = nextip;
  do {
    if (--ninbuf < 0) {
      if ((ninbuf = (int)read(io, genbuf, LBSIZE)-1) < 0) {
        if (lp>linebuf) { puts_("'\\n' appended");  *genbuf = '\n';  } else { return(EOF); }
      }
      fp = genbuf;  while(fp < &genbuf[ninbuf]) {  if (*fp++ & 0200) { break; }  }  fp = genbuf;
    }
    c = *fp++;  if (c=='\0') { continue; }
    if (c&0200 || lp >= &linebuf[LBSIZE]) {  lastc = '\n';  }  *lp++ = c;  count++;
  } while (c != '\n');
  *--lp = 0;  nextip = fp;  return(0);
}

char* getline_blk(unsigned int tl) {  char *bp, *lp;  int nl;  lp = linebuf;  bp = getblock(tl, READ);
  nl = nleft;  tl &= ~((BLKSIZE/2)-1);
  while ((*lp++ = *bp++)) { if (--nl == 0) {  bp = getblock(tl+=(BLKSIZE/2), READ);  nl = nleft;  } }
  return(linebuf);
}

void global(int k) {  char *gp;  int c;  unsigned int *a1;  char globuf[GBSIZE];
  compile(c);  gp = globuf;
  while ((c = getchr()) != '\n') {
    
    if (c == '\\') {  c = getchr();  if (c != '\n') { *gp++ = '\\'; }  }
    *gp++ = c;
  }
  if (gp == globuf) { *gp++ = 'p'; }  *gp++ = '\n';  *gp++ = 0;
  for (a1 = zero; a1 <= dol; a1++) {  *a1 &= ~01;  if (a1>=addr1 && a1<=addr2 && execute(a1)==k) { *a1 |= 01; } }
  for (a1 = zero; a1 <= dol; a1++) {
    if (*a1 & 01) {  *a1 &= ~01;  dot = a1;  globp = globuf; a1 = zero; }
  }
}

void init(void) {  int *markp;  close(tfile);  tline = 2;
  for (markp = names; markp < &names[26]; )  {  *markp++ = 0;  }
  iblock = -1;  oblock = -1;  ichanged = 0;
  close(creat(tfname, 0600));  tfile = open(tfname, 2);  dot = dol = zero;  memset(inputbuf, 0, sizeof(inputbuf));
}

void newline(void) {  int c;  if ((c = getchr()) == '\n' || c == EOF) { return; }
  if (c == 'p' || c == 'l' || c == 'n') {  pflag++;
    if (c == 'l') { listf++;  } else if (c == 'n') { listn++; }
    if ((c = getchr()) == '\n') { return; }
  };

}

void onhup(int n) {
  signal(SIGINT, SIG_IGN);  signal(SIGHUP, SIG_IGN);
  if (dol > zero) {  addr1 = zero+1;  addr2 = dol;  io = creat("ed.hup", 0600);  if (io > 0) { putfile(); } }
  fchange = 0;  quit(0);
}

void print(void) {  unsigned int *a1 = addr1;  nonzero();
  do {  if (listn) {  count = a1 - zero;  putd();  putchr_('\t');  }  puts_(getline_blk(*a1++));  } while (a1 <= addr2);
  dot = addr2;  listf = 0;  listn = 0;  pflag = 0;
}

void putchr_(int ac) {  char *lp = linp;  int c = ac;
  if (listf) {
    if (c == '\n') {
      if (linp != line && linp[-1]==' ') {  *lp++ = '\\';  *lp++ = 'n';  }
    } else {
      if (col > (72 - 4 - 2)) {  col = 8;  *lp++ = '\\';  *lp++ = '\n';  *lp++ = '\t';  }  col++;
      if (c=='\b' || c=='\t' || c=='\\') {
        *lp++ = '\\';
        if (c=='\b') { c = 'b'; }  else if (c=='\t') { c = 't'; }  col++;
      } else if (c<' ' || c=='\177') {
        *lp++ = '\\';  *lp++ =  (c>>6) +'0';  *lp++ = ((c >> 3) & 07) + '0';  c = (c & 07) + '0';  col += 3;
      }
    }
  }
  *lp++ = c;
  if (c == '\n' || lp >= &line[64]) {  linp = line;  write(oflag ? 2 : 1, line, lp - line);  return;  }  linp = lp;
}

void putd(void) {  int r = count % 10;  count /= 10;  if (count) { putd(); }  putchr_(r + '0');  }

void putfile(void) {  unsigned int *a1;  char *fp, *lp;  int n, nib = BLKSIZE;  fp = genbuf;  a1 = addr1;
  do {
    lp = getline_blk(*a1++);
    for (;;) {
      if (--nib < 0) {
        n = (int)(fp-genbuf);
        if (write(io, genbuf, n) != n) {  puts_(WRERR); }  nib = BLKSIZE-1;  fp = genbuf;
      }
      count++;  if ((*fp++ = *lp++) == 0) {  fp[-1] = '\n';  break; }
    }
  } while (a1 <= addr2);
  n = (int)(fp-genbuf);  if (write(io, genbuf, n) != n) {  puts_(WRERR); }
}

int putline(void) {  char *bp, *lp;  int nl;  unsigned int tl;  fchange = 1;  lp = linebuf;
  tl = tline;  bp = getblock(tl, WRITE);  nl = nleft;  tl &= ~((BLKSIZE/2)-1);
  while ((*bp = *lp++)) {
    if (*bp++ == '\n') {  *--bp = 0;  linebp = lp;  break;  }
    if (--nl == 0) {  bp = getblock(tl += (BLKSIZE/2), WRITE);  nl = nleft;  }
  }
  nl = tline;  tline += (((lp - linebuf) + 03) >> 1) & 077776;  return(nl);
}

void puts_(char *sp) {  col = 0;  while (*sp) { putchr_(*sp++); }  putchr_('\n');  }

void quit(int n) { if (vflag && fchange && dol!=zero) {  fchange = 0;}  unlink(tfname); exit(0); }

void readfile(const char * c) {
  filename(c);  
  init();
  addr2 = zero;
  if ((io = open((const char*)file, 0)) < 0) { lastc = '\n';}  
  ninbuf = 0;
  c = zero != dol;
  append(getfile, addr2);
  exfile();
  fchange = c;
}

#define BUFSIZE 100
char buf[BUFSIZE];  
int bufp = 0;

int getch_(void) {  
  char c = (bufp > 0) ? buf[--bufp] : getchar();  
  lastc = c & 0177;
  return lastc;
}
void ungetch_(int c) { 
  if (bufp >= BUFSIZE) {  
    printf("ungetch: overflow\n"); 
  }  else {  
    buf[bufp++] = c; 
  } 
}

void drawline() {
   printf("----------------------------------------------------");
}

void search(const char* re) {  
  char buf[GBSIZE];  
  snprintf(buf, sizeof(buf), "/%s\n", re);
  drawline();  
  printf("g%s", buf);  const char* p = buf + strlen(buf) - 1;
  while (p >= buf) { ungetch_(*p--); }  global(1);
}

void printcommand(void) {  int c;  char lastsep;
  for (;;) {  unsigned int* a1;
    if (pflag) { pflag = 0;  addr1 = addr2 = dot;  print(); }  c = '\n';
    for (addr1 = 0;;) {  lastsep = c; c = getchr();
      if (c != ',' && c != ';') { break; }
      if (a1==0) {  a1 = zero+1;  if (a1 > dol) { a1--; }  }  addr1 = a1;  if (c == ';') { dot = a1; }
    }
    if (lastsep != '\n' && a1 == 0) { a1 = dol; }
    if ((addr2 = a1)==0) { given = 0;  addr2 = dot;  } else { given = 1; }  if (addr1==0) { addr1 = addr2; }
    switch(c) {
      case 'p':  case 'P':  newline();  print();  continue;
      case EOF:  default:  return;
    }
  }
}
