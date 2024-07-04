#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#define CONFIG_L1_CACHE_LINE_SIZE_BITS 64
#define DRIVER 0
#define CLIENT_CH 1
#define NUM_CLIENTS 3
#define NET_BUFFER_SIZE 2048

#define RING_SIZE 512

#define ROUND_DOWN(n, b) (((n) >> (b)) << (b))
#define LINE_START(a) ROUND_DOWN(a, CONFIG_L1_CACHE_LINE_SIZE_BITS)
#define LINE_INDEX(a) (LINE_START(a)>>CONFIG_L1_CACHE_LINE_SIZE_BITS)

typedef unsigned int microkit_channel;

void microkit_notify(uint64_t ch);

void microkit_notify_delayed(uint64_t ch);

static inline void
dsb(void)
{
    // asm volatile("dsb sy" ::: "memory");
}

void 
dmb(void)
{
    // asm volatile("dmb sy" ::: "memory");
}


void
clean_by_va(unsigned long vaddr)
{
    // asm volatile("dc cvac, %0" : : "r"(vaddr));
    dmb();
}
void
cache_clean(unsigned long start, unsigned long end)
{
    unsigned long line;
    unsigned long index;

    for (index = LINE_INDEX(start); index < LINE_INDEX(end) + 1; index++) {
        line = index << CONFIG_L1_CACHE_LINE_SIZE_BITS;
        clean_by_va(line);
    }
}

struct net_queue {
    /* index to insert at */
    uint32_t tail;
    /* index to remove from */
    uint32_t head;
    /* flag to indicate whether consumer requires signalling */
    uint32_t consumer_signalled;
 
    
    uint64_t *io_or_offsets;
    uint16_t *lens;
    
    //@ int ghost_io_or_offset;
    //@ int len;
};


/*@
predicate ghost_io_perm(int io_or_offset);

lemma int create_ghost_io_perm(int io_or_offset);
  requires true;
  ensures ghost_io_perm(io_or_offset);
@*/

// Goes away with Viper
// Proving a predicate like this is a good way to establish all permissions to access a given struct (here net_queue) and its fields
// This exposes them so preconditions or postconditions can access them later
/*@
predicate mk_net_queue(struct net_queue *q, uint32_t tail, uint32_t head, uint32_t consumer_signalled, uint64_t *io_or_offsets, uint16_t *lens) = 
  // malloc_block_net_queue(q) is a VeriFast builtin that says that q points to a valid struct net_queue-sized region of memory
  // &*& is separating conjunction. A |-> B says the (one) location being dereferenced in expression A will point to value B.
  malloc_block_net_queue(q) &*& q->tail |-> tail &*& q->head |-> head &*& q->consumer_signalled |-> consumer_signalled &*& 
  q->io_or_offsets |-> io_or_offsets &*& q->lens |-> lens &*&
  // malloc_block_ullongs(A, B) is a VeriFast builtin that says that there is a region of memory starting at A of size B unsigned long longs (uint64_t)
  // similarly for malloc_block_ushorts for unsigned shorts (uint16_t)
  malloc_block_ullongs(io_or_offsets, RING_SIZE) &*& malloc_block_ushorts(lens, RING_SIZE) &*&
  // using a variable ?B on the right-hand side of a |-> declares B as a ghost variable, it should then be referred to as B (without the question mark)
  // after declaring A[0..x] |-> ?B, each entry within A can be referred to using B[0], B[1], ... B[RING_SIZE-1]
  io_or_offsets[0..RING_SIZE] |-> ?viofs &*& lens[0..RING_SIZE] |-> ?vlens;
@*/


struct net_queue_handle {
     /* available buffers */
    struct net_queue *free;
     /* filled buffers */
    struct net_queue *active;
    /* size of the queues */
    uint32_t size;
};

// Goes away with Viper
/*@
predicate mk_net_queue_handle(struct net_queue_handle *q, struct net_queue *free, uint32_t ftail, uint32_t fhead, struct net_queue *active, uint32_t atail, uint32_t ahead, uint32_t size) = 
  malloc_block_net_queue_handle(q) &*& q->free |-> free &*& q->active |-> active &*& q->size |-> size &*& 
  // the underscore _ is a don't-care value
  mk_net_queue(free, ftail, fhead, _, _, _) &*& mk_net_queue(active, atail, ahead, _, _, _);
@*/


uintptr_t tx_free_drv;
uintptr_t tx_active_drv;
uintptr_t tx_free_arp;
uintptr_t tx_active_arp;
uintptr_t tx_free_cli0;
uintptr_t tx_active_cli0;
uintptr_t tx_free_cli1;
uintptr_t tx_active_cli1;

uintptr_t buffer_data_region_arp_vaddr;
uintptr_t buffer_data_region_cli0_vaddr;
uintptr_t buffer_data_region_cli1_vaddr;

uintptr_t buffer_data_region_arp_paddr;
uintptr_t buffer_data_region_cli0_paddr;
uintptr_t buffer_data_region_cli1_paddr;

struct state {
    struct net_queue_handle tx_queue_drv;
    struct net_queue_handle tx_queue_clients[NUM_CLIENTS];
    uintptr_t buffer_region_vaddrs[NUM_CLIENTS];
    uintptr_t buffer_region_paddrs[NUM_CLIENTS];
};


bool net_queue_empty_free(struct net_queue_handle *queue)
//@ requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize);
// The first sep-conjunct of this ensures accounts for the memory that was talked about in the requirement.
// Without either having this or explicitly deallocating that memory, VeriFast will complain of a memory leak.
//@ ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize) &*& result == !truncate_unsigned(ftail - fhead, 32);
// VeriFast will define a variable "result" for the return value of the function.
// truncate_unsigned(A, B) is a VeriFast builtin that says to truncate the unsigned value of A to B bits
{
    
    //@ open mk_net_queue_handle(queue, gfree, ftail, fhead, ?active, atail, ahead, _);
    uint32_t size = queue->size;
    // Nested opens goes away with Viper, because we expect Viper will implicitly open heap fragments reachable from the initial open as needed.
    //@ open mk_net_queue(gfree, _, _, _, _, _);
    // This "truncating" attribute tells VeriFast not to overflow/underflow-check the following expression.
    bool retval = !(/*@truncating@*/(queue->free->tail - queue->free->head));
    
    //@close mk_net_queue(gfree, _, _, _, _, _);
    
    //@close mk_net_queue_handle(queue, gfree, _, _, active, _, _, _);
    return retval;
    
}

/**
 * Check if the active queue is empty.
 *
 * @param queue queue handle for the active queue to check.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
bool net_queue_empty_active(struct net_queue_handle *queue)
//@requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize);
//@ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize) &*& result == !truncate_unsigned(atail - ahead, 32); 
{
    //@ open mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
    // Nested opens goes away with Viper
    //@ open mk_net_queue(gactive, _, _, _, _, _);
    uint32_t tail_head = /*@truncating@*/(queue->active->tail - queue->active->head);
    bool retval = !(tail_head);
    //@ close mk_net_queue(gactive, _, _, _, _, _);
    
    //@ close mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
    return retval;
}

bool net_queue_full_free(struct net_queue_handle *queue)
//@requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize);
//@ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize) &*& result == (truncate_unsigned(truncate_unsigned(ftail + 1, 32) - fhead, 32) == gsize); 
{
    //@ open mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
    // Nested opens goes away with Viper
    //@ open mk_net_queue(gfree, _, _, _, _, _);
    uint32_t tail1 = /*@truncating@*/(queue->free->tail + 1);
    uint32_t tail_head = /*@truncating@*/(tail1 - queue->free->head);
    bool retval = tail_head == queue->size;
    //@ close mk_net_queue(gfree, _, _, _, _, _);
    //@ close mk_net_queue_handle(queue, _, _, _, _, _, _, _);
    return retval;
}


bool net_queue_full_active(struct net_queue_handle *queue)
//@requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize);
//@ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize) &*& result == (truncate_unsigned(truncate_unsigned(atail + 1, 32) - ahead, 32) == gsize); 
{
    //@ open mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
    // Nested opens goes away with Viper
    //@ open mk_net_queue(gactive, _, _, _, _, _);
    
    uint32_t tail1 = /*@truncating@*/(queue->active->tail + 1);
    uint32_t tail_head = /*@truncating@*/(tail1 - queue->active->head);
    bool retval = tail_head == queue->size;
    return retval;
    //@ close mk_net_queue(gactive, _, _, _, _, _);
    //@ close mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
}

uint64_t val_mod_size(uint64_t val, uint64_t size) 
//@ requires size == RING_SIZE;
//@ ensures result < RING_SIZE;
{
    //@assume(val%size < size);
    uint64_t retval = val%size;
    return retval;
}
/*@
fixpoint bool net_queue_full(int tail, int head, int size){
  return truncate_unsigned(truncate_unsigned(tail + 1, 32) - head, 32) == size;
}

fixpoint bool impl(bool cond1, bool cond2) {
  return !cond1 || cond2;
}
@*/

int net_enqueue_free(struct net_queue_handle *queue, uint64_t io_or_offset, uint16_t len)
//@requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE;
//@ensures mk_net_queue_handle(queue, gfree, ?nftail, fhead, gactive, atail, ahead, gsize) &*& impl(net_queue_full(ftail, fhead, gsize), result == -1) == true &*& impl(!net_queue_full(ftail, fhead, gsize), nftail == truncate_unsigned(ftail +1 ,32)) == true;
{
    if (net_queue_full_free(queue)) {
      return -1;
    }
    //@ open mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
    uint32_t size = queue->size;
    struct net_queue *free = queue->free;
    
    //@open mk_net_queue(gfree, ftail, _, _, _, _);
  
    uint64_t *io_or_offsets = free->io_or_offsets;
    uint16_t *lens = free->lens;
    uint64_t index = val_mod_size(free->tail, queue->size);
    
    io_or_offsets[index] = io_or_offset;
    lens[index] = len;
    
    uint32_t new_tail = /*@truncating@*/(free->tail + 1);
    free->tail = new_tail;
    
    //@close mk_net_queue(gfree, new_tail, _, _, _, _);
    
    //@close mk_net_queue_handle(queue, gfree, new_tail, fhead, gactive, atail, ahead, gsize);
    
    return 0;
}

int net_enqueue_active(struct net_queue_handle *queue, uint64_t io_or_offset, uint16_t len)
//@ requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE;
//@ ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, ?natail, ahead, gsize);
{
    if (net_queue_full_active(queue)) {
        return -1;
    }
    //@ open mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
    uint32_t size = queue->size;
    struct net_queue *active = queue->active;
    
    //@ open mk_net_queue(gactive, atail, _, _, _, _);
    uint64_t *io_or_offsets = active->io_or_offsets;
    uint16_t *lens = active->lens;
    uint64_t index = val_mod_size(active->tail, size);
    
    io_or_offsets[index] = 0;
    lens[index] = 0;
    uint32_t new_tail = /*@truncating@*/(active->tail + 1);
    active->tail = new_tail;
    
    //@ close mk_net_queue(gactive, new_tail, _, _, _, _);
    
    //@ close mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, new_tail, ahead, gsize);

    return 0;
}

int net_dequeue_free(struct net_queue_handle *queue, uint64_t *io_or_offset, uint16_t *len)
//@ requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE &*& *io_or_offset |-> _ &*& *len |-> _;
//@ ensures mk_net_queue_handle(queue, gfree, ftail, ?nfhead, gactive, atail, ahead, gsize) &*& *io_or_offset |-> _ &*& *len |-> _;
{
  if(net_queue_empty_free(queue)) {
    return -1;
  }
  //@ open mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
  uint32_t size = queue->size;
  struct net_queue *free = queue->free;
  
  //@ open mk_net_queue(gfree, _, _, _, _, _);
  uint64_t *io_or_offsets = free->io_or_offsets;
  uint16_t *lens = free->lens;
  uint64_t index = val_mod_size(free->head, size);
  
  *io_or_offset = io_or_offsets[index];
  *len = lens[index];

  uint32_t new_head = /*@truncating@*/(free->head + 1);
  free->head = new_head;
  
  //@close mk_net_queue(gfree, _, _, _, _, _);
  
  //@close mk_net_queue_handle(queue, _, _, _, _, _, _, _);
  return 0;
  
}

int net_dequeue_active(struct net_queue_handle *queue, uint64_t *io_or_offset, uint16_t *len)
//@ requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE &*&  *io_or_offset |-> _ &*& *len |-> _;
//@ ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ?nahead, gsize) &*& *io_or_offset |-> _ &*& *len |-> _;
{
    if (net_queue_empty_active(queue)) {
      return -1;
    }
    //@ open mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
    uint32_t size = queue->size;
    //@open mk_net_queue(gactive, _, _, _, _, _);
    uint64_t *io_or_offsets = queue->active->io_or_offsets;
    uint16_t *lens = queue->active->lens;
    uint64_t index = val_mod_size(queue->active->head, size);
    *io_or_offset = io_or_offsets[index];
    *len = lens[index];
    uint32_t new_head = /*@truncating@*/(queue->active->head + 1);
    queue->active->head = new_head;
    
    //@close mk_net_queue(gactive, _, _, _, _, _);
    
    //@close mk_net_queue_handle(queue, _, _, _, _, _, _, _);
    
    return 0;
}

void net_queue_init(struct net_queue_handle *queue, struct net_queue *free, struct net_queue *active, uint32_t size)
{
    queue->free = free;
    queue->active = active;
    queue->size = size;
}

void net_buffers_init(struct net_queue_handle *queue, uintptr_t base_addr)
{
    for (uint32_t i = 0; i < queue->size - 1; i++) {
        struct net_buff_desc buffer = {(NET_BUFFER_SIZE * i) + base_addr, 0};
        int err = net_enqueue_free(queue, buffer);
    }
}

void net_request_signal_free(struct net_queue_handle *queue)
//@ requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE;
//@ ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
{
    //@ open mk_net_queue_handle(queue, _, _, _, _, _, _, _);
    //@ open mk_net_queue(gfree, _, _, _, _, _ );
    queue->free->consumer_signalled = 0;
    //@ close mk_net_queue(gfree, _, _, _, _, _);
    //@ close mk_net_queue_handle(queue, _, _, _, _, _, _, _);
}

void net_request_signal_active(struct net_queue_handle *queue)
//@ requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE;
//@ ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
{
    //@ open mk_net_queue_handle(queue, _, _, _, _, _, _, _);
    //@ open mk_net_queue(gactive, _, _, _, _, _ );
    queue->active->consumer_signalled = 0;
    //@ close mk_net_queue(gactive, _, _, _, _, _);
    //@ close mk_net_queue_handle(queue, _, _, _, _, _, _, _);
}

void net_cancel_signal_free(struct net_queue_handle*queue)
//@ requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE;
//@ ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
{
    //@ open mk_net_queue_handle(queue, _, _, _, _, _, _, _);
    //@ open mk_net_queue(gfree, _, _, _, _, _ );
    queue->free->consumer_signalled = 1;
    //@ close mk_net_queue(gfree, _, _, _, _, _);
    //@ close mk_net_queue_handle(queue, _, _, _, _, _, _, _);
}


void net_cancel_signal_active(struct net_queue_handle *queue)
//@ requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE;
//@ ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
{
    //@ open mk_net_queue_handle(queue, _, _, _, _, _, _, _);
    //@ open mk_net_queue(gactive, _, _, _, _, _ );
    queue->active->consumer_signalled = 1;
    //@ close mk_net_queue(gactive, _, _, _, _, _);
    //@ close mk_net_queue_handle(queue, _, _, _, _, _, _, _);
}

/**
 * Consumer of the free queue requires signalling.
 *
 * @param queue queue handle of the free queue to check.
 */
bool net_require_signal_free(struct net_queue_handle *queue)
//@ requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE;
//@ ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
{
    //@ open mk_net_queue_handle(queue, _, _, _, _, _, _, _);
    //@ open mk_net_queue(gfree, _, _, _, _, _ );
    return !queue->free->consumer_signalled;
    //@ close mk_net_queue(gfree, _, _, _, _, _);
    //@ close mk_net_queue_handle(queue, _, _, _, _, _, _, _);
}

/**
 * Consumer of the active queue requires signalling.
 *
 * @param queue queue handle of the active queue to check.
 */
bool net_require_signal_active(struct net_queue_handle *queue)
//@ requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE;
//@ ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
{
    //@ open mk_net_queue_handle(queue, _, _, _, _, _, _, _);
    //@ open mk_net_queue(gactive, _, _, _, _, _ );
    return !queue->active->consumer_signalled;
    //@ close mk_net_queue(gactive, _, _, _, _, _);
    //@ close mk_net_queue_handle(queue, _, _, _, _, _, _, _);
}



int extract_offset(uintptr_t *phys, struct state *gstate)
{

    uintptr_t myphys = *phys;
    uintptr_t *paddrs = gstate->buffer_region_paddrs;
    uintptr_t *vaddrs = gstate->buffer_region_vaddrs;
    struct net_queue_handle *tx_queue_clients = gstate->tx_queue_clients;
    /* for (int client = 0; client < NUM_CLIENTS; client++)
    {
        if (myphys >= paddrs[client] &&
            myphys <  paddrs[client] + (uint64_t)tx_queue_clients[client].size * NET_BUFFER_SIZE) {
            return client;
        }
    } */

    return -1;
}

void tx_provide_dequeue_enqueue(struct net_queue_handle *queue_client, struct net_queue_handle *queue_drv, uint64_t client_vaddrs, uint64_t client_paddrs)
//@ requires mk_net_queue_handle(queue_client, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE &*& mk_net_queue_handle(queue_drv, ?dgfree, ?dftail, ?dfhead, ?dgactive, ?datail, ?dahead, ?dgsize) &*& dgsize == RING_SIZE;
//@ ensures mk_net_queue_handle(queue_client, _, _, _, _, _, _, _) &*& mk_net_queue_handle(queue_drv, _, _, _, _, _, _, _);
{
  uint64_t io_or_offset;
  uint16_t len;
  int err = net_dequeue_active(queue_client, &io_or_offset, &len);
  if(err) {
    abort();  	
  }
  //@open mk_net_queue_handle(queue_client, _, _, _, _, _, _, _);
  uint64_t size = queue_client->size;
  //@close mk_net_queue_handle(queue_client, _, _, _, _, _, _, _);
  
  if(io_or_offset % NET_BUFFER_SIZE || io_or_offset >= NET_BUFFER_SIZE * size) {
    err = net_enqueue_free(queue_client, io_or_offset, len);
    if(err) {
      abort();
    }
  }
  // cache clean
  
  err = net_enqueue_active(queue_drv, io_or_offset, len);
  if(err) {
    abort();
  }
}

void tx_provide(struct state *state)
{
    bool enqueued = false;
    for (int client = 0; client < NUM_CLIENTS; client++) {
        bool reprocess = true;
        while (reprocess) {
            while (!net_queue_empty_active(&state->tx_queue_clients[client])) {
                struct net_buff_desc buffer;
                int err = net_dequeue_active(&state->tx_queue_clients[client], &buffer);
                // assert(!err);
                if (buffer.io_or_offset % NET_BUFFER_SIZE ||
                    buffer.io_or_offset >= NET_BUFFER_SIZE * state->tx_queue_clients[client].size) {
                    /* sddf_dprintf("VIRT_TX|LOG: Client provided offset %lx which is not buffer aligned or outside of buffer region\n",
                                 buffer.io_or_offset); */
                    err = net_enqueue_free(&state->tx_queue_clients[client], buffer);
                    // assert(!err);
                    continue;
                }

                cache_clean(buffer.io_or_offset + state->buffer_region_vaddrs[client],
                            buffer.io_or_offset + state->buffer_region_vaddrs[client] + buffer.len);

                buffer.io_or_offset = buffer.io_or_offset + state->buffer_region_paddrs[client];
                err = net_enqueue_active(&state->tx_queue_drv, buffer);
                assert(!err);
                enqueued = true;
            }

            net_request_signal_active(&state->tx_queue_clients[client]);
            reprocess = false;

            if (!net_queue_empty_active(&state->tx_queue_clients[client])) {
                net_cancel_signal_active(&state->tx_queue_clients[client]);
                reprocess = true;
            }
        }
    }

    if (enqueued && net_require_signal_active(&state->tx_queue_drv)) {
        net_cancel_signal_active(&state->tx_queue_drv);
        microkit_notify_delayed(DRIVER);
    }
}

void tx_return_dequeue_enqueue(struct net_queue_handle *queue_client, struct net_queue_handle *queue_drv) 
//@ requires mk_net_queue_handle(queue_client, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE &*& mk_net_queue_handle(queue_drv, ?dgfree, ?dftail, ?dfhead, ?dgactive, ?datail, ?dahead, ?dgsize) &*& dgsize == RING_SIZE;
//@ ensures mk_net_queue_handle(queue_client, _, _, _, _, _, _, _) &*& mk_net_queue_handle(queue_drv, _, _, _, _, _, _, _);
{
  uint64_t io_or_offset = 0;
  uint16_t len = 0;
  int err = net_dequeue_free(queue_drv, &io_or_offset, &len);
  if(err) {
    abort();
  }
  
  // client is implied because we assume only one client
  
  err = net_enqueue_free(queue_client, io_or_offset, len);
  if(err) {
    abort();
  }
}

void tx_return(struct state *state)
{
    bool reprocess = true;
    bool notify_clients[NUM_CLIENTS] = {false};
    while (reprocess) {
        while (!net_queue_empty_free(&state->tx_queue_drv)) {
            struct net_buff_desc buffer;
            int err = net_dequeue_free(&state->tx_queue_drv, &buffer.io_or_offset, &buffer.len);
            assert(!err);

            int client = extract_offset(&buffer.io_or_offset, state);
            assert(client >= 0);

            err = net_enqueue_free(&state->tx_queue_clients[client], buffer);
            assert(!err);
            notify_clients[client] = true;
        }

        net_request_signal_free(&state->tx_queue_drv);
        reprocess = false;

        if (!net_queue_empty_free(&state->tx_queue_drv)) {
            net_cancel_signal_free(&state->tx_queue_drv);
            reprocess = true;
        }
    }

    for (int client = 0; client < NUM_CLIENTS; client++) {
        if (notify_clients[client] && net_require_signal_free(&state->tx_queue_clients[client])) {
            net_cancel_signal_free(&state->tx_queue_clients[client]);
            microkit_notify(client + CLIENT_CH);
        }
    }
}

/* void notified(microkit_channel ch)
{
    tx_return();
    tx_provide();
} */

/* void init(void)
{
    net_queue_init(&state.tx_queue_drv, (net_queue_t *)tx_free_drv, (net_queue_t *)tx_active_drv, TX_QUEUE_SIZE_DRIV);
    virt_queue_init_sys(microkit_name, state.tx_queue_clients, tx_free_arp, tx_active_arp);

    mem_region_init_sys(microkit_name, state.buffer_region_vaddrs, buffer_data_region_arp_vaddr);

    state.buffer_region_paddrs[0] = buffer_data_region_arp_paddr;
    state.buffer_region_paddrs[1] = buffer_data_region_cli0_paddr;
    state.buffer_region_paddrs[2] = buffer_data_region_cli1_paddr;

    tx_provide();
}
*/

int main(int argc, char *argv[]) 
//@ requires true;
//@ ensures true;
{
  return 0;
}
