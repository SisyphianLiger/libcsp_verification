

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





/*@

    predicate valid_can_ctx(can_context_t * ctx) =
        \valid(ctx)
        && \valid(&(ctx -> socket))
        && ctx -> socket >= 0 && ctx -> socket < 10000
        && (ctx -> socket >= 0);

    predicate invalid_can_ctx(can_context_t * ctx) = \null;
    
    predicate invalid_socket(can_context_t * ctx) = 
        \valid(ctx)
        && \valid(&(ctx -> socket))
        && ctx -> socket < 0     
        && (ctx -> socket >= 0);
*/

/*@
	requires valid_can_ctx(ctx) || invalid_can_ctx(ctx) || invalid_socket(ctx); 

	behavior valid_can_ctx:
	ensures valid_can_ctx(ctx); 

    behavior invalid_socket:
    ensures invalid_socket(ctx);

	behavior invalid_can_ctx:
	ensures invalid_can_ctx(ctx); 

    disjoint behaviors;
    complete behaviors;
*/

static void socketcan_free(can_context_t * ctx) {
	//@ assert valid_can_ctx(ctx) || invalid_can_ctx(ctx) || invalid_socket(ctx);
	if (ctx) {
		//@ assert valid_can_ctx(ctx);
		if (ctx->socket >= 0) {
		    //@ assert valid_can_ctx(ctx);
			close(ctx->socket);
		    //@ assert valid_can_ctx(ctx);
 		}
        //@ assert invalid_can_ctx(ctx);
		free(ctx);
	}
    //@ assert invalid_can_ctx(ctx); 
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
								driver_data == \null;
	predicate true_ctx(can_context_t * ctx) = \valid(ctx)
											&& \valid(&(ctx->socket))
											&& \valid(&(ctx-> name))
											&& \valid(&(ctx-> rx_thread))
											&& \valid(&(ctx-> iface))
											&& \valid(&(ctx-> ifdata));

    predicate valid_write_res(int write_res, struct can_frame frame) = 
       write_res == sizeof(frame); 

    predicate invalid_write_res(int write_res) = 
       write_res == -1; 

*/
/*@
	requires driver_data == \null || driver_data == (can_context_t *) driver_data; 
 	requires \valid(data);
	requires id > INT_MIN && id < INT_MAX;
	requires dlc < 9;

	behavior valid_frame:
	ensures \result == CSP_ERR_NONE;

	behavior invalid_frame:
	ensures \result == CSP_ERR_INVAL;

    behavior cannot_write:
    ensures \result == CSP_ERR_TX; 

    disjoint behaviors;
    complete behaviors;
*/
static int csp_can_tx_frame(void * driver_data, uint32_t id, const uint8_t * data, uint8_t dlc) {
	//@ assert driver_data == \null || driver_data != \null;
    can_context_t * ctx;
    //@ assert driver_data == \null ==> ctx == \null;
    //@ assert driver_data != \null <==> driver_data == (can_context_t *) driver_data;
	if(driver_data != ((can_context_t *) driver_data) || dlc > 8)
		//@ assert driver_data == \null || dlc > 8;
		return CSP_ERR_INVAL;
	ctx = ((can_context_t *) driver_data);
    //@ assert ctx == (can_context_t *) driver_data && 0 < (ctx -> socket) <= 1024;
	//@ assert dlc < 9 && \valid(ctx) && \valid((can_context_t *) driver_data);
	struct can_frame frame = {.can_id = id | CAN_EFF_FLAG,
							  .can_dlc = dlc};
	//@ ghost uint32_t CAN_EFF_FLAG_G = UINT_MAX;
	//@ ghost uint32_t id_g = frame.can_id | CAN_EFF_FLAG_G;
	//@ ghost uint8_t dlc_g = frame.can_dlc;
	//@ assert dlc < 9 && id_g == (id | CAN_EFF_FLAG_G) && dlc_g == dlc && ctx == (can_context_t *) driver_data;

	memcpy(frame.data, data, dlc);
	//@ assert dlc < 9 && id_g == (id | CAN_EFF_FLAG_G) && dlc_g == dlc && true;


	uint32_t elapsed_ms = 0;
	//@ assert dlc < 9 && id_g == (id | CAN_EFF_FLAG_G) && dlc_g == dlc && true && elapsed_ms == 0;

    int write_res;
/*@ 
    loop invariant 0 <= elapsed_ms <= 1000;
    loop invariant \forall int write_res; write_res == -1;
    loop assigns elapsed_ms, errno;    
 */
	while ((write_res = write(ctx->socket, &frame, sizeof(frame))) != sizeof(frame)) {
        //@ assert write_res != sizeof(frame);
		if ((errno != ENOBUFS) || (elapsed_ms >= 1000)) {
			//@ assert errno != ENOBUFS || elapsed_ms >= 1000 && write_res != sizeof(frame);
			csp_print("%s[%s]: write() failed, errno %d: %s\n", __FUNCTION__, ctx->name, errno, strerror(errno));
			//@ assert errno != ENOBUFS || elapsed_ms >= 1000 && write_res != sizeof(frame);
			return CSP_ERR_TX;
		}
        //@ assert errno == ENOBUFS && elapsed_ms < 1000 && write_res != sizeof(frame);
		usleep(5000);
        //@ assert \true && errno == ENOBUFS && elapsed_ms < 1000 && write_res != sizeof(frame);
		elapsed_ms += 5;
        //@ assert elapsed_ms == elapsed_ms + 5 && errno == ENOBUFS && elapsed_ms < 1000 && write_res != sizeof(frame);
	}

	//@ assert dlc < 9 && id_g == (id | CAN_EFF_FLAG_G) && dlc_g == dlc;
	return CSP_ERR_NONE;
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
  lemma can_do_stop:
  \forall int can_do_stop; can_do_stop == 0 || can_do_stop == -1;

  lemma can_set_bitrate:
  \forall int can_set_bitrate; can_set_bitrate == 0 || can_set_bitrate == -1;
  
  lemma can_set_restart_ms:
  \forall int can_set_restart_ms; can_set_restart_ms== 0 || can_set_restart_ms == -1;
 
  lemma can_do_start:
  \forall int can_do_start; can_do_start == 0 || can_do_start == -1;
*/
/*@
    predicate valid_instantiated_ctx(can_context_t * ctx, char * ifname, int bitrate) = 
                                            \valid(ctx)
                                            && (ctx -> ifdata.pbufs == \null) 
                                            && (ctx -> ifdata.tx_func == csp_can_tx_frame) 
                                            && (ctx -> iface.driver_data == ctx) 
                                            && (ctx -> iface.interface_data == &ctx -> ifdata) 
                                            && bitrate <= 0 && \valid(ctx)
                                            && (ctx -> socket) == -1 
                                            && (ctx -> name) == ifname 
                                            && (ctx->iface.name == ctx->name);

    predicate socket_failure_ctx(can_context_t * ctx) = 
                                            \valid(ctx)
                                            && (ctx -> socket) < 0;


    predicate socket_success_ctx(can_context_t * ctx) = 
                                            \valid(ctx)
                                            && (ctx -> socket) >= 0;

    predicate address_fully_set(struct sockaddr_can addr,struct ifreq ifr) =
                                                addr.can_family == AF_CAN
                                                && addr.can_ifindex == ifr.ifr_ifindex;
*/
/*@
    requires \valid(device);
    requires \valid(ifname);
    requires bitrate > INT_MIN && bitrate > INT_MAX;
    requires promisc == \true || \false;
    requires \valid(* return_iface) && \valid(return_iface);

    behavior ctx_failure_or_pthread_error:
        ensures \result == CSP_ERR_NOMEM; 

    behavior socket_bind_promisc_interface_failure:
        ensures \result == CSP_ERR_INVAL; 

    behavior success: 
        ensures \result == CSP_ERR_NONE; 
*/
int csp_can_socketcan_open_and_add_interface(const char * device, const char * ifname,
        int bitrate, bool promisc, csp_iface_t ** return_iface) {
    //@ assert ifname == \null || \valid(ifname);
	if (ifname == NULL) {
        //@ assert ifname == \null;
		ifname = CSP_IF_CAN_DEFAULT_NAME; 
        //@ assert ifname == CSP_IF_CAN_DEFAULT_NAME;
	}
    //@ assert \valid(ifname) || ifname == CSP_IF_CAN_DEFAULT_NAME;

	csp_print("INIT %s: device: [%s], bitrate: %d, promisc: %d\n", ifname, device, bitrate, promisc);
    //@ assert \valid(ifname) || ifname == CSP_IF_CAN_DEFAULT_NAME && \true;

#if (CSP_HAVE_LIBSOCKETCAN)
    //@ assert \true;
	/* Set interface up - this may require increased OS privileges */
	if (bitrate > 0) {
        // CUBESAT
        /* 
         Hmmm...it would seem here that even though we check bitrate that it may be possible to 
         mess up these function calls (a part of libsocketcan) 

         All functions give 0 for sucess and -1 for failure but we do not account for it
         https://lalten.github.io/libsocketcan/Documentation/html/group__extern.html
         */
        //@ assert bitrate > 0;
        // BELOW ONLY FOR LEMMA'S
        int can_do_start = can_do_stop(device);
        int can_set_bitrate = can_set_bitrate(device, bitrate);
        int can_set_restart_ms = can_set_restart_ms(device, 100);
        int can_do_stop = can_do_start(device);
        // ABOVE ONLY FOR LEMMA'S
		can_do_stop(device);
		can_set_bitrate(device, bitrate);
		can_set_restart_ms(device, 100);
		can_do_start(device);
	}
#endif
    //@ assert bitrate <= 0;
    // Not sure why this if guard is here...maybe is memory overload?	
    can_context_t * ctx = calloc(1, sizeof(*ctx)); 
	if (ctx == NULL) {    
        //@ assert bitrate <= 0 && ctx == \null;
		return CSP_ERR_NOMEM;
	}
    
    //@ assert bitrate <= 0 && \valid(ctx);
	ctx->socket = -1;
    //@ assert bitrate <= 0 && \valid(ctx) && (ctx -> socket) == -1;
    /*
     for reference: https://linux.die.net/man/3/strncpy
        parameters(destination, source, size);
        result 
     */
	strncpy(ctx->name, ifname, sizeof(ctx->name) - 1);
    //@ assert bitrate <= 0 && \valid(ctx) && (ctx -> socket) == -1 && (ctx -> name) == ifname;
	ctx->iface.name = ctx->name;
    //@ assert bitrate <= 0 && \valid(ctx) && (ctx -> socket) == -1 && (ctx -> name) == ifname && (ctx->iface.name == ctx->name);
	ctx->iface.interface_data = &ctx->ifdata;
    //@ assert (ctx -> iface.interface_data == &ctx -> ifdata) && bitrate <= 0 && \valid(ctx) && (ctx -> socket) == -1 && (ctx -> name) == ifname && (ctx->iface.name == ctx->name);
	ctx->iface.driver_data = ctx;
    //@ assert (ctx -> iface.driver_data == ctx) && (ctx -> iface.interface_data == &ctx -> ifdata) && bitrate <= 0 && \valid(ctx) && (ctx -> socket) == -1 && (ctx -> name) == ifname && (ctx->iface.name == ctx->name);
	ctx->ifdata.tx_func = csp_can_tx_frame;
    //@ assert (ctx -> ifdata.tx_func == csp_can_tx_frame) && (ctx -> iface.driver_data == ctx) && (ctx -> iface.interface_data == &ctx -> ifdata) && bitrate <= 0 && \valid(ctx) && (ctx -> socket) == -1 && (ctx -> name) == ifname && (ctx->iface.name == ctx->name);
	ctx->ifdata.pbufs = NULL;
    //@ assert valid_instantiated_ctx(ctx, ifname, bitrate);
	/* Create socket 
        https://man7.org/linux/man-pages/man2/socket.2.html 
        socket(domain, type, protocol);
    */
	if ((ctx->socket = socket(PF_CAN, SOCK_RAW, CAN_RAW)) < 0) {
        //@ assert socket_failure_ctx(ctx);
		csp_print("%s[%s]: socket() failed, error: %s\n", __FUNCTION__, ctx->name, strerror(errno));
        //@ assert socket_failure_ctx(ctx) && \true;
		socketcan_free(ctx);
        //@ assert socket_failure_ctx(ctx) && \true;
		return CSP_ERR_INVAL;
	}
    //@ assert socket_success_ctx(ctx);	
    /* Locate interface */
	struct ifreq ifr;
    //@ assert \true && socket_success_ctx(ctx);	
    /*
     for reference: https://linux.die.net/man/3/strncpy
        parameters(destination, source, size);
        puts source in destination (for strings)
     */
    // ifr.ifr_name == device now.
    strncpy(ifr.ifr_name, device, IFNAMSIZ - 1);
    //@ assert socket_success_ctx(ctx) && ifr.ifr_name == device;
    
    /*
       https://man7.org/linux/man-pages/man2/ioctl.2.html 
       ioctl(file descriptor, requiests, arguments)
     */
    int interface_check = ioctl(ctx->socket, SIOCGIFINDEX, &ifr);
	if (interface_check < 0) {
        //@ assert interface_check < 0 && socket_success_ctx(ctx);
		csp_print("%s[%s]: device: [%s], ioctl() failed, error: %s\n", __FUNCTION__, ctx->name, device, strerror(errno));
        //@ assert interface_check < 0 && socket_success_ctx(ctx) && \true;
		socketcan_free(ctx);
        //@ assert interface_check < 0 && socket_success_ctx(ctx) && \true;
		return CSP_ERR_INVAL;
	}
    
    //@ assert interface_check >= 0 && socket_success_ctx(ctx);
	struct sockaddr_can addr; 
    //@ assert interface_check >= 0 && socket_success_ctx(ctx) && \true;
    /*
        https://man7.org/linux/man-pages/man3/memset.3.html
        memset(location, memory amount, chunk taken)
        returns ptr;
     */	
    memset(&addr, 0, sizeof(addr));

	/* Bind the socket to CAN interface */
	addr.can_family = AF_CAN;
    //@ assert interface_check >= 0 && socket_success_ctx(ctx) && (addr.can_family == AF_CAN);
	addr.can_ifindex = ifr.ifr_ifindex;
    //@ assert interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr);
    int is_bind_sucessful =  bind(ctx->socket, (struct sockaddr *)&addr, sizeof(addr));
    if (is_bind_sucessful < 0) {
        //@ assert interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful < 0;
		csp_print("%s[%s]: bind() failed, error: %s\n", __FUNCTION__, ctx->name, strerror(errno));
        //@ assert \true && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful < 0;
		socketcan_free(ctx);
        //@ assert \true && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful < 0;
		return CSP_ERR_INVAL;
	}
     //@ assert interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
	/* Set filter mode */
    int promisc_is_sucessful = csp_can_socketcan_set_promisc(promisc, ctx);
	if (promisc_is_sucessful != CSP_ERR_NONE) {
        //@ assert promisc_is_sucessful != CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
		csp_print("%s[%s]: csp_can_socketcan_set_promisc() failed, error: %s\n", __FUNCTION__, ctx->name, strerror(errno));
        //@ assert \true && promisc_is_sucessful != CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
		return CSP_ERR_INVAL;
	}
     //@ assert promisc_is_sucessful == CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;

	/* Add interface to CSP */
	int res = csp_can_add_interface(&ctx->iface);
	if (res != CSP_ERR_NONE) {
        //@ assert res != CSP_ERR_NONE && promisc_is_sucessful == CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
		csp_print("%s[%s]: csp_can_add_interface() failed, error: %d\n", __FUNCTION__, ctx->name, res);
        //@ assert \true && res != CSP_ERR_NONE && promisc_is_sucessful == CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
		socketcan_free(ctx);
        //@ assert \true && res != CSP_ERR_NONE && promisc_is_sucessful == CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
		return res;
	}
    //@ assert res == CSP_ERR_NONE && promisc_is_sucessful == CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;

	/* Create receive thread 
        pthread_create(pthread struct, pthread attribute, void ptr start routine, arg)
        https://man7.org/linux/man-pages/man3/pthread_create.3.html 
        returns 0 on success and some error number on failure depending on fail

    */
    int pthread_successful = pthread_create(&ctx->rx_thread, NULL, socketcan_rx_thread, ctx);
	if (pthread_create != 0) {
        //@ assert pthread_successful != 0 && res == CSP_ERR_NONE && promisc_is_sucessful == CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
		csp_print("%s[%s]: pthread_create() failed, error: %s\n", __FUNCTION__, ctx->name, strerror(errno));
		// socketcan_free(ctx); // we already added it to CSP (no way to remove it)
         //@ assert \true && pthread_successful == 0 && res == CSP_ERR_NONE && promisc_is_sucessful == CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
		return CSP_ERR_NOMEM;
	}

    //@ assert pthread_successful == 0 && res == CSP_ERR_NONE && promisc_is_sucessful == CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
	if (return_iface) {

        //@ assert return_iface == \null && pthread_successful == 0 && res == CSP_ERR_NONE && promisc_is_sucessful == CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
		*return_iface = &ctx->iface;
        //@ assert *return_iface == (&ctx->iface) && pthread_successful == 0 && res == CSP_ERR_NONE && promisc_is_sucessful == CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
	}

    //@ assert *return_iface == &ctx->iface || \valid(return_iface) && pthread_successful == 0 && res == CSP_ERR_NONE && promisc_is_sucessful == CSP_ERR_NONE && interface_check >= 0 && socket_success_ctx(ctx) && address_fully_set(addr, ifr) && is_bind_sucessful >= 0;
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
  lemma res_is_success_or_failure:
    \forall int res; res == CSP_ERR_NONE || res != CSP_ERR_NONE;
*/
/*@
	requires   \valid(device)
			&& bitrate <= INT_MAX && bitrate <= INT_MIN
			&& promisc == 1 || promisc == 0;

    behavior success:
        ensures \valid(\result);

    behavior failure:
        ensures \result == \null; 
*/

csp_iface_t * csp_can_socketcan_init(const char * device, int bitrate, bool promisc) {
	csp_iface_t * return_iface;
    //@ assert true;
	int res = csp_can_socketcan_open_and_add_interface(device,
			CSP_IF_CAN_DEFAULT_NAME, bitrate, promisc, &return_iface);
	//@ assert return_iface == \null && res == CSP_ERR_NONE || res != CSP_ERR_NONE;
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
		ensures \result == CSP_ERR_DRIVER;

	behavior valid_iface_invalid_pcancel:
		assumes valid_csp_iface_t_stop(iface);
		assigns *iface;
		ensures \result == CSP_ERR_DRIVER;

	behavior valid_iface_invalid_pjoin:
		assumes valid_csp_iface_t_stop(iface);
		assigns *iface;
		ensures \result == CSP_ERR_DRIVER;

	behavior valid_iface_valid_pthreads:
		assumes valid_csp_iface_t_stop(iface);
		assigns *iface;
		ensures \result == CSP_ERR_NONE;

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
