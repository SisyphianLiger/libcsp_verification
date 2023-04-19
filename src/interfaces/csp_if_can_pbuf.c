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

void csp_can_pbuf_cleanup(csp_can_interface_data_t * ifdata) {

	uint32_t now = csp_get_ms();

	csp_packet_t * packet = ifdata->pbufs;
	csp_packet_t * prev = NULL;

	while (packet) {

		/* Perform cleanup in used pbufs */
		if (now - packet->last_used > PBUF_TIMEOUT_MS) {

			/* Erase from list prev->next = next */
			if (prev) {
				prev->next = packet->next;
			} else {
				ifdata->pbufs = packet->next;
			}

			csp_buffer_free(packet);
		}

		prev = packet;
		packet = packet->next;
	}

}

/*@
		predicate valid_if_data(csp_can_interface_data_t * ifdata) =	\valid(ifdata)
																		&& \valid(&(ifdata -> pbufs));
		predicate success_csp_packet_t(csp_packet_t * t) = \valid(t);
		predicate failure_csp_packet_t(csp_packet_t * t) = t == \null;
*/
/*@
		requires valid_if_data(ifdata)
				&& \valid(task_woken)
				&& (id > INT_MIN && id < INT_MAX)
				&& (mask > INT_MIN && mask < INT_MAX);

		behavior success:
			assumes valid_if_data(ifdata);
	        ensures \valid(\result) && (\result->cfpid & mask) == (id & mask);

		behavior no_match_found:
			assumes valid_if_data(ifdata);
			ensures \result == \null;

		complete behaviors;
		disjoint behaviors success, no_match_found;
*/
csp_packet_t * csp_can_pbuf_find(csp_can_interface_data_t * ifdata, uint32_t id, uint32_t mask, int * task_woken) {
	//@ assert valid_if_data(ifdata) || ifdata == \null;
	csp_packet_t * packet = ifdata->pbufs;
	// SEE CUBESAT
	//@ assert \valid(packet) || packet == \null;

/*@
      loop invariant \forall csp_packet_t * packet; (packet -> next) != \null ==> \valid(packet);
      loop assigns packet;
*/
	while (packet) {
		//@ assert success_csp_packet_t(packet);
		if ((packet->cfpid & mask) == (id & mask)) {
			//@ assert (packet->cfpid & mask) == (id & mask);
			packet->last_used = (task_woken) ? csp_get_ms_isr() : csp_get_ms();
			//@ assert true;
			return packet;
		}
		packet = packet->next;
		// assert packet == \valid(&(packet -> next));
	}
	//@ assert failure_csp_packet_t(packet);
	return NULL;
}
