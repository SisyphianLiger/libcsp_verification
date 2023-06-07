

#include <csp/arch/csp_time.h>

#include <time.h>
#include <sys/time.h>
#include <limits.h>

/*@
        requires \true;
        ensures \result > 0 || \result == 0;  
 */
uint32_t csp_get_ms(void) {
    struct timespec ts;
    //@ assert \valid(&(ts));
    int clock_res = clock_gettime(CLOCK_MONOTONIC, &ts) == 0;
    //@ assert clock_res == 0 || clock_res == 1 && \valid(&(ts));
	if (0 == clock_res) {
        int result = (uint32_t)((ts.tv_sec * 1000) + (ts.tv_nsec / 1000000));
        //@ assert clock_res == 0 && \valid(&(ts)) && result > 0 && result <= INT_MAX;
		return result; 
	}
    //@ assert clock_res == 1 && \valid(&(ts));
	return 0;
}

/*@
        assigns \nothing;
        ensures \result > 0 || \result == 0;  
 */
uint32_t csp_get_ms_isr(void) {
    int clock_res = csp_get_ms();
    //@ assert clock_res == 0 || clock_res > 0;
    return clock_res;
}

uint32_t csp_get_s(void) {

	struct timespec ts;
	if (clock_gettime(CLOCK_MONOTONIC, &ts) == 0) {
		return (uint32_t)ts.tv_sec;
	}
	return 0;
}

uint32_t csp_get_s_isr(void) {

	return csp_get_s();
}
