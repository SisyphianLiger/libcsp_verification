#include "csp_if_can_pbuf.h"

#include <string.h>

#include <csp/csp_buffer.h>
#include <csp/csp_error.h>
#include <csp/arch/csp_time.h>
#include <csp/interfaces/csp_if_can.h>

/* Buffer element timeout in ms */
#define PBUF_TIMEOUT_MS 1000



void csp_can_pbuf_free(csp_can_interface_data_t * ifdata, csp_packet_t * buffer, int buf_free, int * task_woken) {

	csp_packet_t * packet = ifdata->pbufs;
	csp_packet_t * prev = NULL;

	while (packet) {

		/* Perform cleanup in used pbufs */
		if (packet == buffer) {

			/* Erase from list prev->next = next */
			if (prev) {
				prev->next = packet->next;
			} else {
				ifdata->pbufs = packet->next;
			}

			if (buf_free) {
				if (task_woken == NULL) {
					csp_buffer_free(packet);
				} else {
					csp_buffer_free_isr(packet);
				}
			}

		}

		prev = packet;
		packet = packet->next;
	}

}






csp_packet_t * csp_can_pbuf_new(csp_can_interface_data_t * ifdata, uint32_t id, int * task_woken) {

	csp_can_pbuf_cleanup(ifdata);

	uint32_t now = (task_woken) ? csp_get_ms_isr() : csp_get_ms();

	csp_packet_t * packet = (task_woken) ? csp_buffer_get_isr(0) : csp_buffer_get(0);
	if (packet == NULL) {
		return NULL;
	}

	packet->last_used = now;
	packet->cfpid = id;
	packet->remain = 0;

	/* Insert at beginning, because easy */
	packet->next = ifdata->pbufs;
	ifdata->pbufs = packet;

	return packet;
}


/*@

    requires \valid(ifdata);
    ensures \valid(ifdata) || ifdata == \null;

*/

void csp_can_pbuf_cleanup(csp_can_interface_data_t * ifdata) {

	uint32_t now = csp_get_ms();
    //@ assert now >= 0 || now <= INT_MAX;
    csp_packet_t * packet; 
    //@ assert now >= 0 || now <= INT_MAX && ifdata -> pbufs == \null || \valid(&(ifdata -> pbufs)); 
    if(ifdata -> pbufs == NULL){
    //@ assert now >= 0 || now <= INT_MAX && ifdata -> pbufs == \null;
        packet = NULL;
        //@ assert now >= 0 || now <= INT_MAX && ifdata -> pbufs == \null && packet == \null;
    }
    else {
        packet = ifdata->pbufs;
        //@ assert now >= 0 || now <= INT_MAX && \valid(&(ifdata -> pbufs)) && packet == ifdata->pbufs;
    } 
    //@ assert now >= 0 || now <= INT_MAX && \valid_read(packet) && \valid(&(ifdata -> pbufs));
	csp_packet_t * prev = NULL;
    /*@ assert now >= 0 || now <= INT_MAX && 
               \valid_read(packet) && \valid(&(ifdata -> pbufs)) &&
               \valid_read(prev) && prev == \null; 
     */


    /*@ 
        loop invariant \forall csp_packet_t *packet; \valid(packet);
        loop invariant \forall csp_packet_t *prev; prev == \null || (\valid(prev) && (\valid(prev->next) || prev->next == \null));
    */
	while (packet) {
		/* Perform cleanup in used pbufs */
        
        //@ assert (now - packet -> last_used) > PBUF_TIMEOUT_MS || (now - packet -> last_used) < PBUF_TIMEOUT_MS;
        if (now - packet->last_used > PBUF_TIMEOUT_MS) {
        //@ assert (now - packet -> last_used) > PBUF_TIMEOUT_MS;
	
            /* Erase from list prev->next = next */
            //@ assert (now - packet -> last_used) > PBUF_TIMEOUT_MS && prev == \null || \valid(prev);
			if (prev) {
                //@ assert (now - packet -> last_used) > PBUF_TIMEOUT_MS && \valid(prev);
				prev->next = packet->next;
                //@ assert (now - packet -> last_used) > PBUF_TIMEOUT_MS && \valid(prev) && ifdata -> pbufs == packet -> next; 
			} else {
                //@ assert (now - packet -> last_used) > PBUF_TIMEOUT_MS && prev == \null;
				ifdata->pbufs = packet->next;
                //@ assert (now - packet -> last_used) > PBUF_TIMEOUT_MS && prev == \null && ifdata -> pbufs == packet -> next;
			}

			csp_buffer_free(packet);
		}
        //@ assert now - packet -> last_used < PBUF_TIMEOUT_MS;
		prev = packet;
        //@ assert prev == packet && now - packet -> last_used < PBUF_TIMEOUT_MS;
		packet = packet->next;
        //@ assert packet ==  packet -> next && prev == packet && now - packet -> last_used < PBUF_TIMEOUT_MS;
	}
    //@ assert now >= 0 || now <= INT_MAX && packet == \null && packet == \null ==> ifdata -> pbufs == \null;
}

/*@
		predicate valid_if_data(csp_packet_t * packet, uint32_t id, uint32_t mask, int * task_woken) =	
                                                                        \valid(packet) && 
                                                                        id >= INT_MAX && id <= INT_MAX && 
                                                                        mask >= INT_MIN && mask <= INT_MAX &&
                                                                        \valid(task_woken);

        predicate no_packet_found(csp_packet_t * packet, uint32_t id, uint32_t mask, int * task_woken) = 
                                                                        packet == \null &&
                                                                        id >= INT_MAX && id <= INT_MAX && 
                                                                        mask >= INT_MIN && mask <= INT_MAX &&
                                                                        \valid(task_woken);
        predicate valid_packet(csp_packet_t * packet, csp_can_interface_data_t * ifdata) = \valid(packet) &&
                                                        packet == ifdata -> pbufs;

        predicate valid_ifdata(csp_can_interface_data_t * ifdata) = \valid(ifdata) && \valid(&(ifdata -> pbufs));
        
*/ 

/*@
    lemma valid_packet:
        \forall csp_packet_t * packet; \valid(packet) || packet == \null;
*/

/*@
        requires valid_ifdata(ifdata) ;
        assigns \nothing;
        
	    behavior found_packet:
	    ensures (\exists csp_packet_t * packet; \valid(packet) && packet == \result);

	    behavior packet_not_found:
        ensures \result == \null; 
        
        disjoint behaviors;
        complete behaviors;
*/

csp_packet_t * csp_can_pbuf_find(csp_can_interface_data_t * ifdata, uint32_t id, uint32_t mask, int * task_woken) {
    //@ assert valid_ifdata(ifdata);
    csp_packet_t * packet = ifdata->pbufs;
    //@ assert \valid(packet) && packet == ifdata -> pbufs || packet == \null;
    /*@
        loop assigns packet;
        loop invariant \forall  csp_packet_t * packet; \valid(packet);
        loop invariant \forall  csp_packet_t * packet; (packet->cfpid & mask) != (id & mask) ==>  packet == packet -> next;
    */
	while (packet) {
        //@ assert (packet->cfpid & mask) == (id & mask) || (packet->cfpid & mask) != (id & mask);
        if (packet->cfpid & mask == id & mask) {	 
            //@ assert (packet->cfpid & mask) == (id & mask);
            packet->last_used = (task_woken) ? csp_get_ms_isr() : csp_get_ms();	 
            //@ assert \true && (packet->cfpid & mask) == (id & mask);
            return packet;
		}
        packet = packet->next; 
        //@ assert packet == packet -> next && (packet->cfpid & mask) != (id & mask);
	}
	//@ assert packet == \null; 
    return NULL;
}
