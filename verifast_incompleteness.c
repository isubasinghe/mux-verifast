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
};

/*@
  
predicate mk_net_queue(struct net_queue *q, uint32_t tail, uint32_t head, uint32_t consumer_signalled, uint64_t *io_or_offsets, uint16_t *lens) = 
  malloc_block_net_queue(q) &*& q->tail |-> tail &*& q->head |-> head &*& q->consumer_signalled |-> consumer_signalled &*& 
  q->io_or_offsets |-> io_or_offsets &*& q->lens |-> lens &*&
  malloc_block_ullongs(io_or_offsets, RING_SIZE) &*& malloc_block_ushorts(lens, RING_SIZE) &*&
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

/*@
predicate mk_net_queue_handle(struct net_queue_handle *q, struct net_queue *free, uint32_t ftail, uint32_t fhead, struct net_queue *active, uint32_t atail, uint32_t ahead, uint32_t size) = 
  malloc_block_net_queue_handle(q) &*& q->free |-> free &*& q->active |-> active &*& q->size |-> size &*& 
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
//@ ensures mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize) &*& result == !truncate_unsigned(ftail - fhead, 32);
{
    //@ open mk_net_queue_handle(queue, gfree, ftail, fhead, ?active, atail, ahead, _);
    uint32_t size = queue->size;

    //@ open mk_net_queue(gfree, _, _, _, _, _);
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
    //@ open mk_net_queue(gactive, _, _, _, _, _);
    
    uint32_t tail1 = /*@truncating@*/(queue->active->tail + 1);
    uint32_t tail_head = /*@truncating@*/(tail1 - queue->active->head);
    bool retval = tail_head == queue->size;
    return retval;
    //@ close mk_net_queue(gactive, _, _, _, _, _);
    //@ close mk_net_queue_handle(queue, gfree, ftail, fhead, gactive, atail, ahead, gsize);
}

uint64_t tail_mod_size(uint64_t tail, uint64_t size) 
//@ requires size == RING_SIZE;
//@ ensures result < RING_SIZE;
{
    //@assume(tail%size < size);
    uint64_t retval = tail%size;
    return retval;
}

int net_enqueue_free(struct net_queue_handle *queue, uint64_t io_or_offset, uint16_t len)
//@requires mk_net_queue_handle(queue, ?gfree, ?ftail, ?fhead, ?gactive, ?atail, ?ahead, ?gsize) &*& gsize == RING_SIZE;
//@ensures mk_net_queue_handle(queue, gfree, ?nftail, fhead, gactive, atail, ahead, gsize) &*& nftail == truncate_unsigned(ftail + 1, 32);
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
    uint64_t index = tail_mod_size(free->tail, queue->size);
    
    io_or_offsets[index] = io_or_offset;
    lens[index] = len;
    
    uint32_t new_tail = /*@truncating@*/(free->tail + 1);
    free->tail = new_tail;
    
    //@close mk_net_queue(gfree, new_tail, _, _, _, _);
    
    //@close mk_net_queue_handle(queue, gfree, new_tail, fhead, gactive, atail, ahead, gsize);
    
    return 0;
}