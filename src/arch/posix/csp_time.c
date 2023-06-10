

#include <csp/arch/csp_time.h>
#include <errno.h>
#include <time.h>
#include <sys/time.h>
#include <limits.h>

#define RESET_CLOCK 0

/*@ 
        lemma clock_gettime_res:
            \forall int clock_res; clock_res == 0 || clock_res == -1;
*/
/*@
        requires \true;

        behavior clock_returns_valid_time:
        ensures \result <= INT_MAX && \result >= 0;

        behavior clock_gettime_fails_or_overflows:
        ensures \result == RESET_CLOCK;

        disjoint behaviors;
        complete behaviors;

 */
uint32_t csp_get_ms(void) {
    struct timespec ts;
    //@ assert \valid(&(ts));
    int clock_res = clock_gettime(CLOCK_MONOTONIC, &ts) == 0;
    //@ assert clock_res == 0 || clock_res == -1 && \valid(&(ts));
	if (0 == clock_res) {
        //@ assert clock_res == 0 && \valid(&(ts));
        long result = ((ts.tv_sec * 1000) + (ts.tv_nsec / 1000000));   
        /*@ assert result <= INT_MAX && result >= 0 || 
                   result < INT_MAX && result > 0 && 
                   clock_res == 0  && 
                   \valid(&(ts)); */
        if ( result < 0 || result > INT_MAX)
            //@ assert result > INT_MAX || result < 0 && clock_res == 0 && \valid(&(ts));
            return RESET_CLOCK;
        //@ assert result < INT_MAX && result > 0 && clock_res == 0 && \valid(&(ts)); 
		return (uint32_t) result;         	
    }
    //@ assert clock_res == -1 && \valid(&(ts)); 
	return RESET_CLOCK;
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
