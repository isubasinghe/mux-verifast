#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#define CONFIG_L1_CACHE_LINE_SIZE_BITS 64
#define DRIVER 0
#define CLIENT_CH 1
#define NUM_CLIENTS 3
#define NET_BUFFER_SIZE 2048

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
  malloc_block_ullongs(io_or_offsets, NET_BUFFER_SIZE) &*& malloc_block_ushorts(lens, NET_BUFFER_SIZE) &*&
  io_or_offsets[0..NET_BUFFER_SIZE] |-> ?viofs &*& lens[0..NET_BUFFER_SIZE] |-> ?vlens;
@*/


struct net_queue *create_queue() 
//@requires true;
//@ensures mk_net_queue(result, _, _, _, _, _);
{
  struct net_queue *q = malloc(sizeof(struct net_queue));
  if(q == NULL) {
    abort();
  }
  
  uint64_t *io_or_offsets = malloc(NET_BUFFER_SIZE * sizeof(uint64_t));
  if(io_or_offsets == NULL) {
    abort();
  }
  uint16_t *lens = malloc(NET_BUFFER_SIZE * sizeof(uint16_t));
  if(lens == NULL) {
    abort();
  }
  
  q->io_or_offsets = io_or_offsets;
  
  q->lens = lens;
  
  //@close mk_net_queue(q, _, _, _, io_or_offsets, lens);
  return q;
}

void set_iof(struct net_queue *q, uint64_t io_or_offset, uint64_t index)
//@ requires mk_net_queue(q, _, _, _, _, _) &*& index < NET_BUFFER_SIZE;
//@ ensures mk_net_queue(q, _, _, _, _, _);
{
  //@ open mk_net_queue(q, _, _, _, _, _);
  q->io_or_offsets[index] = 0;
  //@ close mk_net_queue(q, _, _, _, _, _);
}

struct net_queue_handle {
     /* available buffers */
    struct net_queue *free;
     /* filled buffers */
    struct net_queue *active;
    /* size of the queues */
    uint32_t size;
};

/*@
predicate mk_net_queue_handle(struct net_queue_handle *q, struct net_queue *free, struct net_queue *active, uint32_t size) = 
  malloc_block_net_queue_handle(q) &*& q->free |-> free &*& q->active |-> active &*& q->size |-> size &*& 
  mk_net_queue(free, _, _, _, _, _) &*& mk_net_queue(active, _, _, _, _, _);
@*/

struct net_queue_handle *create_net_queue_hnd() 
//@requires true;
//@ensures mk_net_queue_handle(result, _, _, _);
{
  struct net_queue_handle *q = malloc(sizeof(struct net_queue_handle));
  if(q == NULL) {
    abort();
  }
  struct net_queue *free = create_queue();
  if(free == NULL) {
    abort();
  }
  struct net_queue *active = create_queue();
  if(active == NULL) {
    abort();
  }
  q->free = free;
  q->active = active;
  q->size = 0;
  //@ close mk_net_queue_handle(q, free, active, 0);
  return q;
}


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

/*@
lemma bool check_this(struct net_queue_handle *queue)
requires mk_net_queue_handle(queue, _, _, _);
ensures mk_net_queue_handle(queue, _, _, _);
{
  return true;
}
@*/

bool net_queue_empty_free(struct net_queue_handle *queue)
//@ requires mk_net_queue_handle(queue, ?gfree, ?gactive, ?gsize);
//@ ensures mk_net_queue_handle(queue, gfree, gactive, gsize);
{
    //@ open mk_net_queue_handle(queue, gfree, ?active, _);
    uint32_t size = queue->size;

    //@ open mk_net_queue(gfree, _, _, _, _, _);
    bool retval = false;
    
    //@close mk_net_queue(gfree, _, _, _, _, _);
    
    //@close mk_net_queue_handle(queue, gfree, active, _);
    return retval;
    
}


void call(struct net_queue_handle *queue)
//@ requires mk_net_queue_handle(queue, ?gfree, ?active, ?size);
//@ ensures mk_net_queue_handle(queue, gfree, active, size);
{
  //@ open mk_net_queue_handle(queue, gfree, _, _);
  //@ open mk_net_queue(gfree, _, _, _, _, _);
  queue->free->tail = 1;
  queue->free->head = 1;
  //@close mk_net_queue(gfree, _, _, _, _, _);
  
  //@close mk_net_queue_handle(queue, gfree, _, _);
    net_queue_empty_free(queue);

  
  
}


/**
 * Check if the active queue is empty.
 *
 * @param queue queue handle for the active queue to check.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
bool net_queue_empty_active(struct net_queue_handle *queue)
{
    uint32_t size = queue->size;
    struct net_queue *active = queue->active;
    
    bool retval = !((active->tail - active->head) % size);
    return retval;
}

bool net_queue_full_free(struct net_queue_handle *queue)
{
    uint32_t size = queue->size;
    struct net_queue *free = queue->free;

    bool retval = !((free->tail + 1 - free->head) % size);
    
    return retval;
}


bool net_queue_full_active(struct net_queue_handle *queue)
{
    uint32_t size = queue->size;
    struct net_queue *active = queue->active;
  
    bool retval = !((active->tail + 1 - active->head) % size);
    return retval;
}



int net_enqueue_free(struct net_queue_handle *queue, uint64_t io_or_offset, uint16_t len)
{
    if (net_queue_full_free(queue)) {
      return -1;
    }

    uint32_t size = queue->size;
    struct net_queue *free = queue->free;

    struct net_buff_desc *buffers = free->buffers;

    buffers[free->tail % size].io_or_offset = io_or_offset;
    buffers[free->tail % size].len = len;
    free->tail++;

    return 0;
}

int net_enqueue_active(struct net_queue_handle *queue, uint64_t io_or_offset, uint16_t len)
{
    if (net_queue_full_active(queue)) return -1;

    queue->active->buffers[queue->active->tail % queue->size].io_or_offset = io_or_offset;
    queue->active->buffers[queue->active->tail % queue->size].len = len;
    queue->active->tail++;

    return 0;
}

int net_dequeue_free(struct net_queue_handle *queue, uint64_t *io_or_offset, uint16_t *len) 
{
  if(net_queue_empty_free(queue)) {
    return -1;
  }
  
  uint64_t val;
  uint32_t size = queue->size;
  struct net_queue *free = queue->free;
  
  struct net_buff_desc *buffers = free->buffers;

  struct net_buff_desc *d = &buffers[free->head];
  val = d->io_or_offset;

  uint32_t new_head = /*@truncating@*/(free->head + 1);
  if(new_head >= size) {
    new_head = size - 1;
  }
  free->head = new_head;
  return 0;
  
}

int net_dequeue_active(struct net_queue_handle *queue, uint64_t *io_or_offset, uint16_t *len)
{
    if (net_queue_empty_active(queue)) {
      return -1;
    }

    *io_or_offset = queue->active->buffers[queue->active->head % queue->size].io_or_offset;
    *len = queue->active->buffers[queue->active->head % queue->size].len;
    queue->active->head++;
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
{
    queue->free->consumer_signalled = 0;
}

void net_request_signal_active(struct net_queue_handle *queue)
{
    queue->active->consumer_signalled = 0;
}

void net_cancel_signal_free(struct net_queue_handle*queue)
{
    queue->free->consumer_signalled = 1;
}


void net_cancel_signal_active(struct net_queue_handle *queue)
{
    queue->active->consumer_signalled = 1;
}

/**
 * Consumer of the free queue requires signalling.
 *
 * @param queue queue handle of the free queue to check.
 */
bool net_require_signal_free(struct net_queue_handle *queue)
{
    return !queue->free->consumer_signalled;
}

/**
 * Consumer of the active queue requires signalling.
 *
 * @param queue queue handle of the active queue to check.
 */
bool net_require_signal_active(struct net_queue_handle *queue)
{
    return !queue->active->consumer_signalled;
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
