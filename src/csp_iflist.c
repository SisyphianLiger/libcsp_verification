

#include <csp/csp_iflist.h>
#include <csp/csp_id.h>

#include <string.h>

#include <csp_autoconfig.h>
#include <csp/csp_debug.h>

/* Interfaces are stored in a linked list */
static csp_iface_t * interfaces = NULL;

static csp_iface_t * dfl_if = NULL;

void csp_iflist_set_default(csp_iface_t * interface) {
	dfl_if = interface;
}

csp_iface_t * csp_iflist_get_default(void) {
	return dfl_if;
}

int csp_iflist_is_within_subnet(uint16_t addr, csp_iface_t * ifc) {

	if (ifc == NULL) {
		return 0;
	}

	uint16_t netmask = ((1 << ifc->netmask) - 1) << (csp_id_get_host_bits() - ifc->netmask);
	uint16_t network_a = ifc->addr & netmask;
	uint16_t network_b = addr & netmask;

	if (network_a == network_b) {
		return 1;
	} else {
		return 0;
	}

}

csp_iface_t * csp_iflist_get_by_subnet(uint16_t addr, csp_iface_t * ifc) {

	/* Head of list */
	if (ifc == NULL) {
		ifc = interfaces;

	/* Otherwise, continue from user defined ifc */
	} else {
		ifc = ifc->next;
	}

	while (ifc) {

		/* Reject searches involving subnets, if the netmask is invalud */
		if (ifc->netmask == 0) {
			ifc = ifc->next;
			continue;
		}

		if (csp_iflist_is_within_subnet(addr, ifc)) {
			return ifc;
		}

		ifc = ifc->next;
	}

	return NULL;

}

csp_iface_t * csp_iflist_get_by_addr(uint16_t addr) {

	csp_iface_t * ifc = interfaces;
	while (ifc) {
		if (ifc->addr == addr) {
			return ifc;
		}
		ifc = ifc->next;
	}

	return NULL;

}

csp_iface_t * csp_iflist_get_by_name(const char * name) {
	csp_iface_t * ifc = interfaces;
	while (ifc) {
		if (strncmp(ifc->name, name, CSP_IFLIST_NAME_MAX) == 0) {
			return ifc;
		}
		ifc = ifc->next;
	}
	return NULL;
}

csp_iface_t * csp_iflist_get_by_index(int idx) {
	csp_iface_t * ifc = interfaces;
	while(ifc && idx--) {
		ifc = ifc->next;
	}
	return ifc;
}

/*
 * Quick note, interfaces == csp_iface_t
 *
 */
/*@
		predicate valid_ifc(csp_iface_t * ifc) = \valid(ifc);
		predicate invalid_ifc(csp_iface_t * ifc) = ifc == \null;
*/

/*@
  lemma ifc_is_valid:
  \forall csp_iface_t * ifc; \valid(ifc);*/
/*@
        requires interfaces == \null || interfaces == ifc;
        requires \valid(ifc); 

		behavior valid_ifc:
            assumes \valid(ifc) && \valid(&(ifc -> next));
			ensures \result == CSP_ERR_NONE;

		behavior invalid_ifc:
            assumes interfaces == ifc;
			ensures \result == CSP_ERR_ALREADY;
*/
int csp_iflist_add(csp_iface_t * ifc) {

	ifc->next = NULL;
	//@ assert \valid(ifc) && (ifc -> next) == \null;

	/* Add interface to pool */
	if (interfaces == NULL) {
		/* This is the first interface to be added */
		//@ assert \valid(ifc) && (ifc -> next) == \null && interfaces == \null;
		interfaces = ifc;
		//@ assert \valid(ifc) && (ifc -> next) == \null && interfaces == ifc;
	} else {
		/* Insert interface last if not already in pool */
		csp_iface_t * last = NULL;
		//@ assert \valid(ifc) && interfaces != \null && (ifc -> next) == \null && last == \null;

		/*@
		  loop invariant i == interfaces && i != \null;
		  loop invariant \forall csp_iface_t* i; (i -> next) != \null ==> \valid(i);
		  loop assigns i, last;
		*/
		for (csp_iface_t * i = interfaces; i != NULL; i = i->next) {
			if ((i == ifc) || (strncmp(ifc->name, i->name, CSP_IFLIST_NAME_MAX) == 0))
				//@ assert i == ifc || (ifc -> name) == (i -> name) && i != \null;
				return CSP_ERR_ALREADY;

			last = i;
			//@ assert i != ifc && (ifc -> name) != (i -> name);
		}
		last->next = ifc;
		//@ assert \valid(ifc) && (ifc -> next) == \null;
	}
	return CSP_ERR_NONE;
	//@ assert \valid(ifc) && interfaces == ifc && (ifc -> next) == \null;
}
csp_iface_t * csp_iflist_get(void) {
	return interfaces;
}

unsigned long csp_bytesize(unsigned long bytes, char *postfix) {
	unsigned long size;

	if (bytes >= (1024 * 1024)) {
		size = bytes / (1024 * 1024);
		*postfix = 'M';
	} else if (bytes >= 1024) {
		size = bytes / 1024;
		*postfix = 'K';
	} else {
		size = bytes;
		*postfix = 'B';
	}

	return size;
}

#if (CSP_ENABLE_CSP_PRINT)

void csp_iflist_print(void) {
	csp_iface_t * i = interfaces;
	unsigned long tx, rx;
	char tx_postfix, rx_postfix;

	while (i) {
		tx = csp_bytesize(i->txbytes, &tx_postfix);
		rx = csp_bytesize(i->rxbytes, &rx_postfix);
		csp_print("%-10s addr: %"PRIu16" netmask: %"PRIu16" mtu: %"PRIu16"\r\n"
				  "           tx: %05" PRIu32 " rx: %05" PRIu32 " txe: %05" PRIu32 " rxe: %05" PRIu32 "\r\n"
				  "           drop: %05" PRIu32 " autherr: %05" PRIu32 " frame: %05" PRIu32 "\r\n"
				  "           txb: %" PRIu32 " (%" PRIu32 "%c) rxb: %" PRIu32 " (%" PRIu32 "%c) \r\n\r\n",
				  i->name, i->addr, i->netmask, i->mtu, i->tx, i->rx, i->tx_error, i->rx_error, i->drop,
				  i->autherr, i->frame, i->txbytes, tx, tx_postfix, i->rxbytes, rx, rx_postfix);
		i = i->next;
	}
}

#endif
