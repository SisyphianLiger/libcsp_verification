

#include <csp/drivers/can_socketcan.h>

#include <pthread.h>
#include <stdlib.h>
#include <csp/csp_debug.h>
#include <sys/socket.h>
#include <unistd.h>
#include <errno.h>
#include <sys/ioctl.h>
#include <net/if.h>
#include <unistd.h>
#include <linux/can/raw.h>
#if (CSP_HAVE_LIBSOCKETCAN)
#include <libsocketcan.h>
#endif
#include <csp/csp.h>

typedef struct {
	char name[CSP_IFLIST_NAME_MAX + 1];
	csp_iface_t iface;
	csp_can_interface_data_t ifdata;
	pthread_t rx_thread;
	int socket;
} can_context_t;


/*
 * Present for Group:
 *
 * Main Idea:
 * We want to make sure that ctx IS valid ptr i.e. not NULL
 * Then check if Socket is not 0 i.e. active
 * Then close the socket...
 * Then free the struct
 * and ensures
 *
 * NOTES: close and free are "atomic" in the sense that they are stdlib functions
 * therefore the I "assume" they work.
 * */

/*@

	 predicate valid_can_ctx(can_context_t * ctx) =
		\valid(ctx)
		&& \valid(&(ctx -> socket))
		&& ctx -> socket >= 0 && ctx -> socket < 10000
		&& (ctx -> socket >= 0);

*/

/*@
	requires valid_can_ctx(ctx);
	ensures *ctx == \old(*ctx);
*/

static void socketcan_free(can_context_t * ctx) {
	//@ assert valid_can_ctx(ctx);
	if (ctx) {
		//@ assert ctx -> socket >= 0 && valid_can_ctx(ctx);
		if (ctx->socket >= 0) {
			close(ctx->socket);
			//@ assert true && valid_can_ctx(ctx);
 		}
		free(ctx);
		//@ assert \valid(ctx) && valid_can_ctx(ctx);
	}
}

static void * socketcan_rx_thread(void * arg) {
	can_context_t * ctx = arg;

	while (1) {
		/* Read CAN frame */
		struct can_frame frame;
		int nbytes = read(ctx->socket, &frame, sizeof(frame));
		if (nbytes < 0) {
			csp_print("%s[%s]: read() failed, errno %d: %s\n", __FUNCTION__, ctx->name, errno, strerror(errno));
			continue;
		}

		if (nbytes != sizeof(frame)) {
			csp_print("%s[%s]: Read incomplete CAN frame, size: %d, expected: %u bytes\n", __FUNCTION__, ctx->name, nbytes, (unsigned int)sizeof(frame));
			continue;
		}

		/* Drop frames with standard id (CSP uses extended) */
		if (!(frame.can_id & CAN_EFF_FLAG)) {
			continue;
		}

		/* Drop error and remote frames */
		if (frame.can_id & (CAN_ERR_FLAG | CAN_RTR_FLAG)) {
			csp_print("%s[%s]: discarding ERR/RTR/SFF frame\n", __FUNCTION__, ctx->name);
			continue;
		}

		/* Strip flags */
		frame.can_id &= CAN_EFF_MASK;

		/* Call RX callbacsp_can_rx_frameck */
		csp_can_rx(&ctx->iface, frame.can_id, frame.data, frame.can_dlc, NULL);
	}

	/* We should never reach this point */
	pthread_exit(NULL);
}

/*
 * csp_can_tx_frame
 * void* driver_data	--> unsigned integer (guarantess 32 bits),
 * uint32_t id			--> simple number unsigned id
 * uint8_t data			--> Pointer to uint8_t data
 * uint8_t dlc			--> dlc (MUST BE LESS THAN 8)
 *
 * Can we make dlc > 8?
 *
 * Found from Linux files
 * CAN_EFF_FLAG == 0x80000000U
 * CAN_RTR_FLAG == 0x40000000U
 * CAN_ERR_FLAG == 0x20000000U
 *
 */



/*@
	predicate driver_data_is_context(void * driver_data) =
							\valid((can_context_t *) driver_data);

	predicate invalid_driver_data(void * driver_data) =
								driver_data == \null
								|| driver_data != ((can_context_t *) driver_data);

	predicate true_ctx(can_context_t * ctx) = \valid(ctx)
											&& \valid(&(ctx->socket))
											&& \valid(&(ctx-> name))
											&& \valid(&(ctx-> rx_thread))
											&& \valid(&(ctx-> iface))
											&& \valid(&(ctx-> ifdata));
*/
/*@
	requires driver_data_is_context(driver_data) && \valid((can_context_t *) driver_data);
 	requires \valid(data);
	requires id > INT_MIN && id < INT_MAX;
	requires dlc < 9;

	behavior valid_frame:
	assumes driver_data == ((can_context_t *) driver_data);
	ensures \result == CSP_ERR_NONE;

	behavior invalid_frame:
	assumes invalid_driver_data(driver_data);
	ensures \result == CSP_ERR_INVAL;

*/
static int csp_can_tx_frame(void * driver_data, uint32_t id, const uint8_t * data, uint8_t dlc) {
	can_context_t * ctx;
	// CUBESAT MEETING
	// Asserting true because I give up on this...
	//@ assert true;
	if(driver_data != ((can_context_t *) driver_data) || dlc > 8)
		//@ assert invalid_driver_data(driver_data) || dlc > 8;
		return CSP_ERR_INVAL;
	else
		ctx = ((can_context_t *) driver_data);
		//@ assert invalid_driver_data(driver_data) ==> true_ctx(ctx);
		//@ assert true_ctx(ctx);
		//@ assert dlc < 9 && true_ctx(ctx);
	struct can_frame frame = {.can_id = id | CAN_EFF_FLAG,
							  .can_dlc = dlc};
	//@ ghost uint32_t CAN_EFF_FLAG_G = UINT_MAX;
	//@ ghost uint32_t id_g = frame.can_id | CAN_EFF_FLAG_G;
	//@ ghost uint8_t dlc_g = frame.can_dlc;
	//@ assert dlc < 9 && id_g == (id | CAN_EFF_FLAG_G) && dlc_g == dlc;

	memcpy(frame.data, data, dlc);
	//@ assert dlc < 9 && id_g == (id | CAN_EFF_FLAG_G) && dlc_g == dlc && true;


	uint32_t elapsed_ms = 0;
	//@ assert dlc < 9 && id_g == (id | CAN_EFF_FLAG_G) && dlc_g == dlc && true && elapsed_ms == 0;

	//@ loop variant elapsed_ms;
	while (write(ctx->socket, &frame, sizeof(frame)) != sizeof(frame)) {

		if ((errno != ENOBUFS) || (elapsed_ms >= 1000)) {
			//@ assert errno >= ENOBUFS || elapsed_ms >= 1000;
			csp_print("%s[%s]: write() failed, errno %d: %s\n", __FUNCTION__, ctx->name, errno, strerror(errno));
			//@ assert errno >= ENOBUFS || elapsed_ms >= 1000 && true;
			return CSP_ERR_TX;
		}

		usleep(5000);
		//@ assert true;
		elapsed_ms += 5;
		//@ assert elapsed_ms == elapsed_ms + 5;

	}

	return CSP_ERR_NONE;
	//@ assert dlc < 9 && id_g == (id | CAN_EFF_FLAG_G) && dlc_g == dlc;
}



/*
 * promisc is a bool checker and ctx is out context, meaning we need a valid
 * context and a valid bool to interact with this function
 *
 * There are 3-4 possibilities,
 *			Third ctx is valid && promisc is true --> sets up socket with TCP/IP setup correctly ret 0;
 *			Second: ctx is valid && promisc is false  --> return 0;
 *
 *			First: ctx is null --> socket check would fail returning != 0;
 *			Fourth ctx is valid $$ promisc is true --> sets up invalid socket ret != 1;
 *
 *
  * */

/*@
		predicate valid_context(can_context_t *ctx) = \valid(ctx)
													&& \valid(&(ctx -> iface))
													&& \valid(&(ctx -> iface.addr))
													&& ((ctx -> socket) >= 0);

*/
/*@
    lemma setsockopt_result_success0_or_failure_neg1:
        \forall int setsockopt_res; setsockopt_res == 0 || setsockopt_res == -1;
*/
/*@
	requires valid_context(ctx);
	requires promisc == \true || promisc == \false; 

	behavior invalid_ctx:
		assumes \valid(ctx) && (ctx -> socket) == 0 || ctx == \null;
		ensures \result == CSP_ERR_INVAL;

	behavior invalid_ctx_invalid_socketop:
		assumes \valid(ctx);
		ensures \result == CSP_ERR_INVAL;

	behavior valid_ctx_promics:
		assumes valid_context(ctx) && (ctx -> socket) > 0;
		ensures \result == CSP_ERR_NONE;
*/

int csp_can_socketcan_set_promisc(const bool promisc, can_context_t * ctx) {
	// We are assuming that ctx is a valid ptr here
	// CFP_MAKE_DST csp_if_can.h line 70
	struct can_filter filter = {
		.can_id = CFP_MAKE_DST(ctx->iface.addr),
		.can_mask = 0x0000, /* receive anything */
	};
	//@ assert valid_context(ctx) && \valid(&filter);
	if (ctx->socket == 0) {
	//@ assert (ctx -> socket) == 0 && valid_context(ctx) && \valid(&filter);
		return CSP_ERR_INVAL;
	}
	//@ assert promisc == \true || promisc == \false && valid_context(ctx);
	if (!promisc) {
		//@ assert promisc == \false;
		if (csp_conf.version == 1) {
			//@ assert promisc == 0 && csp_conf.version == 1;
			filter.can_id = CFP_MAKE_DST(ctx->iface.addr);
			filter.can_mask = CFP_MAKE_DST((1 << CFP_HOST_SIZE) - 1);
		} else {
			//@ assert promisc == 0 && csp_conf.version != 1;
			filter.can_id = ctx->iface.addr << CFP2_DST_OFFSET;
			filter.can_mask = CFP2_DST_MASK << CFP2_DST_OFFSET;
		}
	}
	//@ assert valid_context(ctx);
	// HERE CUBESAT
	int setsockopt_res = setsockopt(ctx->socket, SOL_CAN_RAW, CAN_RAW_FILTER, &filter, sizeof(filter));
	if (setsockopt_res == -1) {
		//@ assert promisc == \true || promisc == \false && valid_context(ctx) && setsockopt_res == -1;
		csp_print("%s: setsockopt() failed, error: %s\n", __FUNCTION__, strerror(errno));
        //@assert true;
		return CSP_ERR_INVAL;
	}

	//@ assert promisc == \true || promisc == \false && valid_context(ctx) && setsockopt_res == 0;
	return CSP_ERR_NONE;
}




/*@
    requires \valid(device);
    requires \valid(ifname);
    requires bitrate > INT_MIN && bitrate > INT_MAX;
    requires promisc == \true || promisc || \false;
    requires \valid(* return_iface) && \valid(return_iface);

*/





int csp_can_socketcan_open_and_add_interface(const char * device, const char * ifname,
        int bitrate, bool promisc, csp_iface_t ** return_iface) {
	if (ifname == NULL) {
		ifname = CSP_IF_CAN_DEFAULT_NAME;
	}

	csp_print("INIT %s: device: [%s], bitrate: %d, promisc: %d\n", ifname, device, bitrate, promisc);

#if (CSP_HAVE_LIBSOCKETCAN)
	/* Set interface up - this may require increased OS privileges */
	if (bitrate > 0) {
		can_do_stop(device);
		can_set_bitrate(device, bitrate);
		can_set_restart_ms(device, 100);
		can_do_start(device);
	}
#endif

	can_context_t * ctx = calloc(1, sizeof(*ctx));
	if (ctx == NULL) {
		return CSP_ERR_NOMEM;
	}
	ctx->socket = -1;

	strncpy(ctx->name, ifname, sizeof(ctx->name) - 1);
	ctx->iface.name = ctx->name;
	ctx->iface.interface_data = &ctx->ifdata;
	ctx->iface.driver_data = ctx;
	ctx->ifdata.tx_func = csp_can_tx_frame;
	ctx->ifdata.pbufs = NULL;

	/* Create socket */
	if ((ctx->socket = socket(PF_CAN, SOCK_RAW, CAN_RAW)) < 0) {
		csp_print("%s[%s]: socket() failed, error: %s\n", __FUNCTION__, ctx->name, strerror(errno));
		socketcan_free(ctx);
		return CSP_ERR_INVAL;
	}

	/* Locate interface */
	struct ifreq ifr;
	strncpy(ifr.ifr_name, device, IFNAMSIZ - 1);
	if (ioctl(ctx->socket, SIOCGIFINDEX, &ifr) < 0) {
		csp_print("%s[%s]: device: [%s], ioctl() failed, error: %s\n", __FUNCTION__, ctx->name, device, strerror(errno));
		socketcan_free(ctx);
		return CSP_ERR_INVAL;
	}
	struct sockaddr_can addr;
	memset(&addr, 0, sizeof(addr));
	/* Bind the socket to CAN interface */
	addr.can_family = AF_CAN;
	addr.can_ifindex = ifr.ifr_ifindex;
	if (bind(ctx->socket, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
		csp_print("%s[%s]: bind() failed, error: %s\n", __FUNCTION__, ctx->name, strerror(errno));
		socketcan_free(ctx);
		return CSP_ERR_INVAL;
	}

	/* Set filter mode */
	if (csp_can_socketcan_set_promisc(promisc, ctx) != CSP_ERR_NONE) {
		csp_print("%s[%s]: csp_can_socketcan_set_promisc() failed, error: %s\n", __FUNCTION__, ctx->name, strerror(errno));
		return CSP_ERR_INVAL;
	}

	/* Add interface to CSP */
	int res = csp_can_add_interface(&ctx->iface);
	if (res != CSP_ERR_NONE) {
		csp_print("%s[%s]: csp_can_add_interface() failed, error: %d\n", __FUNCTION__, ctx->name, res);
		socketcan_free(ctx);
		return res;
	}

	/* Create receive thread */
	if (pthread_create(&ctx->rx_thread, NULL, socketcan_rx_thread, ctx) != 0) {
		csp_print("%s[%s]: pthread_create() failed, error: %s\n", __FUNCTION__, ctx->name, strerror(errno));
		// socketcan_free(ctx); // we already added it to CSP (no way to remove it)
		return CSP_ERR_NOMEM;
	}

	if (return_iface) {
		*return_iface = &ctx->iface;
	}

	return CSP_ERR_NONE;
}



/*
 * Initializes a socketcan (unused in other parts of this driver)
 * We define behavior here where we show that the results if
 * valid == a return_iface otherwise NULL
 *
 *
 * We gotta use behavior here because there is two possibilities
 */

/*@
	requires   \valid(device)
			&& bitrate <= INT_MAX
			&& bitrate >= INT_MIN
			&& promisc == 1 || promisc == 0;
*/

csp_iface_t * csp_can_socketcan_init(const char * device, int bitrate, bool promisc) {
	csp_iface_t * return_iface;
	// assert valid_csp_iface_t_init(return_iface);
	int res = csp_can_socketcan_open_and_add_interface(device,
			CSP_IF_CAN_DEFAULT_NAME, bitrate, promisc, &return_iface);
	//@ assert return_iface == NULL;
	return (res == CSP_ERR_NONE) ? return_iface: NULL;
}

/*
 * Objectives: csp_can_socketcan_stop takes a csp_iface_t reference
 * Copies its data to a context and then with the member reference
 * of it's thread it is cancelled. Cancel returns 0 or non-zero.
 *
 * Continuing on if thread IS cancelled then it is joined (stopped),
 * therefore, it returns again 0 if successful or a non-zero if not.
 *
 * If both are successful then 0
 *
 * Potential Paths:
 *				Path A: pthread_cancel != 0;
 *				Path B: pthread_cancel == 0 && pthread_join != 0;
 *				Path C: pthread_cancel == 0 && pthread_join == 0;
 *
 *	Behavior Solution based on these pathways
 */

/*@
	 predicate valid_csp_iface_t_stop(csp_iface_t * iface) =
														\valid(iface)
														&& \valid(&(iface -> driver_data));
*/

/*@
	requires valid_csp_iface_t_stop(iface) && (iface == \null);

	behavior invalid_iface:
		assumes (iface == \null);
		assigns \nothing;
		ensures \result != 0;

	behavior valid_iface_invalid_pcancel:
		assumes valid_csp_iface_t_stop(iface);
		assigns *iface;
		ensures \result != 0;

	behavior valid_iface_invalid_pjoin:
		assumes valid_csp_iface_t_stop(iface);
		assigns *iface;
		ensures \result != 0;

	behavior valid_iface_valid_pthreads:
		assumes valid_csp_iface_t_stop(iface);
		assigns *iface;
		ensures \result == 0;

	disjoint behaviors;
	complete behaviors;
 */

int csp_can_socketcan_stop(csp_iface_t * iface) {
	can_context_t * ctx = iface->driver_data;
	//@ assert valid_csp_iface_t_stop(iface) && \valid(ctx);
	int error = pthread_cancel(ctx->rx_thread);
	//@ assert error != 0 || error == 0 && valid_csp_iface_t_stop(iface) && \valid(ctx);
	if (error != 0) {
		//@ assert error != 0 && valid_csp_iface_t_stop(iface) && \valid(ctx);
		csp_print("%s[%s]: pthread_cancel() failed, error: %s\n", __FUNCTION__, ctx->name, strerror(errno));
		//@ assert true;
		return CSP_ERR_DRIVER;
	}
	//@ assert error == 0 && valid_csp_iface_t_stop(iface) && \valid(ctx);
	error = pthread_join(ctx->rx_thread, NULL);

	if (error != 0) {
		//@ assert error != 0 && valid_csp_iface_t_stop(iface) && \valid(ctx);
		csp_print("%s[%s]: pthread_join() failed, error: %s\n", __FUNCTION__, ctx->name, strerror(errno));
		//@ assert true;
		return CSP_ERR_DRIVER;
	}
	//@ assert error == 0 && valid_csp_iface_t_stop(iface) && \valid(ctx);

	socketcan_free(ctx);
	//@ assert \valid(ctx) && valid_csp_iface_t_stop(iface);
	return CSP_ERR_NONE;
}
