#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>


struct buff_desc {
  int io_or_offsets;
  int len;
};

struct strct {
  struct buff_desc *buffers;
  uint64_t len;
};

/*@
predicate structs(struct strct *s, int *xs, int *ys, uint64_t len) = 
  malloc_block_strct(s) &*& s->xs |-> xs &*& s->ys |-> ys &*& s->len |-> len &*& 
    xs[0..len] |-> ?vxs &*& ys[0..len] |-> ?vys &*& 
    malloc_block_ints(xs, len) &*& malloc_block_ints(ys, len);
@*/

struct strct * create_structs(uint64_t len)
//@requires 0 <= (len * sizeof(int)) &*& (len * sizeof(int)) <= UINTPTR_MAX;
//@ensures structs(result, _, _, len);
{
  struct strct *s = malloc(sizeof(struct strct));
  int *xs = malloc(len *sizeof(int));
  if(xs == NULL) {
    abort();
  }
  
  int *ys = malloc(len*sizeof(int));
  if(ys == NULL) {
    abort();
  }
  if(s == NULL) {
    abort();
  }
  s->xs = xs;
  s->ys = ys;
  s->len = len;
  //@close structs(s, xs, ys, len);

  return s;
}



