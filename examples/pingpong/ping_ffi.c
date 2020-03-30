/*
  Implements the foreign function interface (FFI) used in the CakeML basis
  library, as a thin wrapper around the relevant system calls.
*/
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <assert.h>

/* This flag is on by default. It catches CakeML's out-of-memory exit codes
 * and prints a helpful message to stderr.
 * Note that this is not specified by the basis library.
 * */
#define STDERR_MEM_EXHAUST

/* clFFI (command line) */

/* argc and argv are exported in cake.S */
extern unsigned int argc;
extern char **argv;

void ffiwrite (unsigned char *c, long clen, unsigned char *a, long alen) {
  printf("Write is stubbed out. Whatever's happening now shouldn't be.\n");
  // stubbed out
}


void ffisend (unsigned char *c, long clen, unsigned char *a, long alen) {
  printf("lawl\n");
  printf("(Pretending to) send message to %s (length %lu): %s\n",c,alen,a);
}

void ffireceive (unsigned char *c, long clen, unsigned char *a, long alen) {
  printf("(Pretending to) receive message from %s\n",c);
  a[0] = 6;
}

/* GC FFI */
int inGC = 0;
struct timeval t1,t2,lastT;
long microsecs = 0;
int numGC = 0;
int hasT = 0;

void cml_exit(int arg) {

  #ifdef STDERR_MEM_EXHAUST
  if(arg == 1) {
    fprintf(stderr,"CakeML heap space exhausted.\n");
  }
  else if(arg == 2) {
    fprintf(stderr,"CakeML stack space exhausted.\n");
  }
  #endif

  #ifdef DEBUG_FFI
  {
    fprintf(stderr,"GCNum: %d, GCTime(us): %ld\n",numGC,microsecs);
  }
  #endif

  exit(arg);
}

void ffiexit (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(alen == 1);
  exit((int)a[0]);
}


/* empty FFI (assumed to do nothing, but can be used for tracing/logging) */
void ffi (unsigned char *c, long clen, unsigned char *a, long alen) {
  #ifdef DEBUG_FFI
  {
    if (clen == 0)
    {
      if(inGC==1)
      {
        gettimeofday(&t2, NULL);
        microsecs += (t2.tv_usec - t1.tv_usec) + (t2.tv_sec - t1.tv_sec)*1e6;
        numGC++;
        inGC = 0;
      }
      else
      {
        inGC = 1;
        gettimeofday(&t1, NULL);
      }
    } else {
      int indent = 30;
      for (int i=0; i<clen; i++) {
        putc(c[i],stderr);
        indent--;
      }
      for (int i=0; i<indent; i++) {
        putc(' ',stderr);
      }
      struct timeval nowT;
      gettimeofday(&nowT, NULL);
      if (hasT) {
        long usecs = (nowT.tv_usec - lastT.tv_usec) +
                     (nowT.tv_sec - lastT.tv_sec)*1e6;
        fprintf(stderr," --- %ld milliseconds\n",usecs / (long)1000);
      } else {
        fprintf(stderr,"\n");
      }
      gettimeofday(&lastT, NULL);
      hasT = 1;
    }
  }
  #endif
}

typedef union {
  double d;
  char bytes[8];
} double_bytes;

// FFI calls for floating-point parsing
void ffidouble_fromString (unsigned char *c, long clen, unsigned char *a, long alen) {
  double_bytes d;
  sscanf(c, "%lf",&d.d);
  assert (8 == alen);
  for (int i = 0; i < 8; i++){
    a[i] = d.bytes[i];
  }
}

void ffidouble_toString (unsigned char *c, long clen, unsigned char *a, long alen) {
  double_bytes d;
  assert (256 == alen);
  for (int i = 0; i < 8; i++){
    d.bytes[i] = a[i];
  }
  //snprintf always terminates with a 0 byte if space was sufficient
  int bytes_written = snprintf(&a[0], 255, "%.20g", d.d);
  // snprintf returns number of bytes it would have written if the buffer was
  // large enough -> check that it did not write more than the buffer size - 1
  // for the 0 byte
  assert (bytes_written <= 255);
}
