#include <stdint.h>
#include <stdbool.h>
#define DRIVER 0
#define CLIENT_CH 1
#define NUM_CLIENTS 3
#define NET_BUFFER_SIZE 2048

struct net_buff_desc {
    /* offset of buffer within buffer memory region or io address of buffer */
    uint64_t io_or_offset;
    /* length of data inside buffer */
    uint16_t len;
};

struct net_queue {
    /* index to insert at */
    uint32_t tail;
    /* index to remove from */
    uint32_t head;
    /* flag to indicate whether consumer requires signalling */
    uint32_t consumer_signalled;
    /* buffer descripter array */
    struct net_buff_desc *buffers;

    //@ list<struct net_buff_desc> ghost_buffers;
};

struct net_queue_handle {
     /* available buffers */
    struct net_queue *free;
     /* filled buffers */
    struct net_queue *active;
    /* size of the queues */
    uint32_t size;
};


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
predicate net_buff_desc(struct net_buff_desc *desc, uint64_t io_or_offset, uint64_t len) = 
  desc->io_or_offset |-> io_or_offset &*& desc->len |-> len;
@*/


/*@
predicate valid_buffers(struct net_buff_desc *buffers, int num_buffers, list<struct net_buff_desc> nbdl) =
  num_buffers == 0 ?
    nbdl == nil
  :
   net_buff_desc(buffers, ?io_or_offset, ?len) &*& valid_buffers(buffers -1, num_buffers -1, ?nnbdl) &*& 
     nnbdl == cons(?gel, nnbdl) &*& gel.io_or_offset == io_or_offset &*& gel.len == len;
@*/

/*@
 predicate unfold_net_queue(struct net_queue *q, uint32_t tail, uint32_t head, uint32_t consumer_signalled, struct net_buff_desc *buffers, list<struct net_buff_desc> gbufs) = 
   q->tail |-> tail &*& q->head |-> head &*& q->consumer_signalled |-> consumer_signalled &*& q->buffers |-> buffers &*& q->ghost_buffers |-> gbufs &*&
   valid_buffers(buffers, 2048, gbufs);

 predicate unfold_queue(struct net_queue_handle *queue, uint32_t free_tail, uint32_t free_head, uint32_t active_tail, uint32_t active_head, uint32_t qsize) =
   queue->free |-> ?gfree &*& queue->active |-> ?gactive &*&
   unfold_net_queue(gfree, free_tail, free_head, _, _, _) &*& unfold_net_queue(gactive, active_tail, active_head, _, _, _) &*& queue->size |-> qsize;
@*/

bool net_queue_empty_free(struct net_queue_handle *queue)
//@ requires unfold_queue(queue, ?ftail, ?fhead, ?atail, ?ahead, ?qsize) &*& (ftail -fhead) >= 0 &*& qsize > 0;
//@ ensures unfold_queue(queue, _, _, _, _, _);
{
    //@ open unfold_queue(queue, _, _, _, _, _);
    uint32_t size = queue->size;
    struct net_queue *free = queue->free;
    
    //@open unfold_net_queue(free, _, _, _, _, _);
    bool retval = !((free->tail - free->head));
    //@close unfold_net_queue(free, _, _, _, _, _);

    //@close unfold_queue(queue, _, _, _, _, _);
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
//@ requires unfold_queue(queue, ?ftail, ?fhead, ?atail, ?ahead, ?qsize) &*& (atail - ahead) >= 0 &*& qsize > 0;
//@ ensures unfold_queue(queue, _, _, _, _, _);
{
    //@open unfold_queue(queue, _, _, _, _, _);
    uint32_t size = queue->size;
    struct net_queue *active = queue->active;
    
    //@open unfold_net_queue(active, _, _, _, _, _);
    bool retval = !((active->tail - active->head) % size);
    //@close unfold_net_queue(active, _, _, _, _, _);
    //@close unfold_queue(queue, _, _, _, _, _);
    return retval;
}

bool net_queue_full_free(struct net_queue_handle *queue)
//@ requires unfold_queue(queue, ?ftail, ?fhead, ?atail, ?ahead, ?qsize) &*& (ftail + 1) <= 0xffffffff &*& ((ftail + 1) -fhead) >= 0 &*& qsize > 0;
//@ ensures unfold_queue(queue, _, _, _, _, ?nsize) &*& nsize == qsize;
{
    //@open unfold_queue(queue, _, _, _, _, _);
    uint32_t size = queue->size;
    struct net_queue *free = queue->free;

    //@open unfold_net_queue(free, _, _, _, _, _);
    bool retval = !((free->tail + 1 - free->head) % size);
    //@close unfold_net_queue(free, _, _, _, _, _);
    
    //@close unfold_queue(queue, _, _, _, _, _);
    
    return retval;
}


bool net_queue_full_active(struct net_queue_handle *queue)
//@ requires unfold_queue(queue, ?ftail, ?fhead, ?atail, ?ahead, ?qsize) &*& (atail + 1) <= 4294967295 &*& ((atail + 1) - ahead) >= 0 &*& qsize > 0;
//@ ensures unfold_queue(queue, _, _, _, _, qsize);
{
    //@open unfold_queue(queue, _, _, _, _, _);
    uint32_t size = queue->size;
    struct net_queue *active = queue->active;
  
    //@open unfold_net_queue(active, _, _, _, _, _);
    bool retval = !((active->tail + 1 - active->head) % size);
    //@close unfold_net_queue(active, _, _, _, _, _);
    
    //@close unfold_queue(queue, _, _, _, _, _);
    return retval;
}



int net_enqueue_free(struct net_queue_handle *queue, struct net_buff_desc buffer)
{
    if (net_queue_full_free(queue)) {
      return -1;
    }

    //@open unfold_queue(queue, _, _, _, _, ?gsize);
    uint32_t size = queue->size;
    //@assert size > 0;
    struct net_queue *free = queue->free;

    //@open unfold_net_queue(free, _, _, _, _, _);
    struct net_buff_desc *buffers = free->buffers;

    //@open valid_buffers(buffers, 2048, free->ghost_buffers);
    //
    buffers[free->tail % size] = buffer;
    free->tail++;
    //@close valid_buffers(buffers, 2048, free->ghost_buffers);
    //@close unfold_net_queue(free, _, _, _, _, _); 
    //@close unfold_queue(queue, _, _, _, _, _);

    return 0;
}

int net_enqueue_active(struct net_queue_handle *queue, struct net_buff_desc buffer)
{
    if (net_queue_full_active(queue)) return -1;

    queue->active->buffers[queue->active->tail % queue->size] = buffer;
    queue->active->tail++;

    return 0;
}

int net_dequeue_free(struct net_queue_handle *queue, struct net_buff_desc *buffer) {
  if(net_queue_empty_free(queue)) {
    return -1;
  }
  *buffer = queue->free->buffers[queue->free->head % queue->size];
  queue->free->head++;
  return 0;
}

int net_dequeue_active(struct net_queue_handle *queue, struct net_buff_desc *buffer)
{
    if (net_queue_empty_active(queue)) {
      return -1;
    }

    *buffer = queue->active->buffers[queue->active->head % queue->size];
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


/*@
predicate unfold_state(struct state *state) = 1 == 1;
@*/

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
            int err = net_dequeue_free(&state->tx_queue_drv, &buffer);
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
