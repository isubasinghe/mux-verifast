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
 predicate unfold_queue(struct net_queue_handle *queue, uint32_t free_tail, uint32_t free_head, uint32_t active_tail, uint32_t active_head, uint32_t qsize) =
   queue->free |-> ?gfree &*& queue->active |-> ?gactive &*& gfree->tail |-> free_tail &*& gfree->head |-> free_head &*&
     gactive->tail |-> active_tail &*& gactive->head |-> active_head &*&
     queue->size |-> qsize;
@*/

bool net_queue_empty_free(struct net_queue_handle *queue)
//@ requires unfold_queue(queue, ?ftail, ?fhead, ?atail, ?ahead, ?qsize) &*& (ftail -fhead) >= 0 &*& qsize > 0;
//@ ensures unfold_queue(queue, _, _, _, _, _);
{
    //@open unfold_queue(queue,_, _, _, _, _);
    return !((queue->free->tail - queue->free->head) % queue->size);
    //@close unfold_queue(queue, _, _, _, _, _);
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
    return !((queue->active->tail - queue->active->head) % queue->size);
    //@close unfold_queue(queue, _, _, _, _, _);
}

bool net_queue_full_free(struct net_queue_handle *queue)
//@ requires unfold_queue(queue, ?ftail, ?fhead, ?atail, ?ahead, ?qsize) &*& (ftail + 1) <= 0xffffffff &*& ((ftail + 1) -fhead) >= 0 &*& qsize > 0;
//@ ensures unfold_queue(queue, _, _, _, _, _);
{
    //@open unfold_queue(queue, _, _, _, _, _);
    return !((queue->free->tail + 1 - queue->free->head) % queue->size);
    //@close unfold_queue(queue, _, _, _, _, _);
}


bool net_queue_full_active(struct net_queue_handle *queue)
//@ requires unfold_queue(queue, ?ftail, ?fhead, ?atail, ?ahead, ?qsize) &*& (atail + 1) <= 4294967295 &*& ((atail + 1) - ahead) >= 0 &*& qsize > 0;
//@ ensures unfold_queue(queue, _, _, _, _, _);
{
    //@open unfold_queue(queue, _, _, _, _, _);
    return !((queue->active->tail + 1 - queue->active->head) % queue->size);
    //@close unfold_queue(queue, _, _, _, _, _);
}


/*@
predicate net_buff_desc(struct net_buff_desc *desc, uint64_t io_or_offset, uint64_t len) = 
  desc->io_or_offset |-> io_or_offset &*& desc->len |-> len;
@*/

/*@

@*/

/*@
predicate valid_buffers(struct net_buff_desc *buffers, int num_buffers, list<struct net_buff_desc> nbdl) =
  num_buffers == 0 ?
    nbdl == nil
  :
   net_buff_desc(buffers, ?io_or_offset, ?len);

@*/
int net_enqueue_free(struct net_queue_handle *queue, struct net_buff_desc buffer)
{
    if (net_queue_full_free(queue)) return -1;

    queue->free->buffers[queue->free->tail % queue->size] = buffer;
    queue->free->tail++;

    return 0;
}

/* int extract_offset(uintptr_t *phys, struct state *gstate)
{

    int myphys = *phys;
    uintptr_t *paddrs = gstate->buffer_region_paddrs;
    uintptr_t *vaddrs = gstate->buffer_region_vaddrs;
    struct net_queue_handle *tx_queue_clients = gstate->tx_queue_clients;
    for (int client = 0; client < NUM_CLIENTS; client++)
    {
        if (myphys >= paddrs[client] &&
            myphys <  paddrs[client] + tx_queue_clients[client].size * NET_BUFFER_SIZE) {
            return client;
        }
    }

    return -1;
} */


void init() {
}

int main(int argc, char *argv[]) 
//@ requires true;
//@ ensures true;
{
  return 0;
}
