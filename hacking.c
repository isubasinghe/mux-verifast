#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>


struct node {
  int x;
  int y;
};
struct strct {
  struct node *nodes;
  int *x;
  uint64_t len;
};

/*@
predicate structs(struct strct *s, struct node *nodes, uint64_t len) = 
  malloc_block_strct(s) &*& s->nodes |-> nodes &*& s->len |-> len;
@*/

struct strct * create_structs(uint64_t len)
//@requires 0 <= (len * sizeof(struct node)) &*& (len * sizeof(struct node)) <= UINTPTR_MAX;
//@ensures structs(result, _, len);
{
  struct strct *s = malloc(sizeof(struct strct));
  int *x = malloc(len *sizeof(int));
  if(x == NULL) {
    abort();
  }
  struct node *nodes = malloc(len * sizeof(struct node));
  if(nodes == NULL) {
    abort();
  }
  
  if(s == NULL) {
    abort();
  }
  s->nodes = nodes;
  s->len = len;
  //@leak chars((char *)nodes, len*sizeof(struct node), _);
  //@leak malloc_block_chars((char *)nodes, len*sizeof(struct node));
  //@close structs(s, nodes, len);

  return s;
}


void set_struct(struct strct *s, uint64_t index, int x, int y)
//@requires structs(s, _, ?len) &*& index < len;
//@ensures structs(s, _, len); 
{
  //@open structs(s, _, _);
  s->nodes[index].x = x;
  s->nodes[index].y = y;
  //@close structs(s, _, _);
}
