#ifndef ML_DSA_REDUCE_H
#define ML_DSA_REDUCE_H

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include "../common/cbmc.h"
#include "params.h"

/*************************************************
 * Name:        ml_dsa_reduce32
 *
 * Description: For finite field element a with a <= 2**31 - 2**22 - 1,
 *              (where "**" means exponentiation),
 *              computes r which is congruent to a (mod Q) AND
 *              such that -6283009 <= r < 6283009.
 *
 *              The returned result r is an approximation to the C
 *              expression (a % ML_DSA_Q) but might be "too big" or
 *              "too small" by exactly ML_DSA_Q
 *
 * Arguments:   - int32_t: finite field element a
 *
 * Returns r.
 **************************************************/
#define REDUCE_DOMAIN_MAX (INT32_MAX - (1 << 22))
#define REDUCE_RANGE_MAX 6283009
int32_t ml_dsa_reduce32(int32_t a)
__contract__(
  requires(a <= REDUCE_DOMAIN_MAX)
  // Type safety as per comments above
  ensures(return_value >= -REDUCE_RANGE_MAX)
  ensures(return_value <   REDUCE_RANGE_MAX)
  // Extra credit: Returned value is congruent to to a % ML_DSA_Q, either
  // "just right" or too big or too small by 1*ML_DSA_Q
  ensures((return_value == (a % ML_DSA_Q)) ||
          (return_value == (a % ML_DSA_Q + ML_DSA_Q)) ||
          (return_value == (a % ML_DSA_Q - ML_DSA_Q)))
);

/*************************************************
 * Name:        ml_dsa_caddq
 *
 * Description: Add ML_DSA_Q if input coefficient is negative.
 *
 * Arguments:   - int32_t: finite field element a such
 *              that a > -ML_DSA_Q && a < ML_DSA_Q
 *
 * Returns r such that r >= 0 && r < ML_DSA_Q
 **************************************************/
int32_t ml_dsa_caddq(int32_t a)
__contract__(
  requires(a > -ML_DSA_Q)
  requires(a < ML_DSA_Q)
  ensures(return_value >= 0)
  ensures(return_value < ML_DSA_Q)
  // Extra credit for partial correctness:
  ensures(return_value == (a >= 0) ? a : (a + ML_DSA_Q))
);

/*************************************************
 * Name:        ml_dsa_freeze
 *
 * Description: For finite field element a with a <= REDUCE_DOMAIN_MAX,
 *              compute standard representation r = a mod ML_DSA_Q such that
 *              r >= 0 && r < ML_DSA_Q
 *
 * Arguments:   - int32_t: finite field element a
 *
 * Returns r.
 **************************************************/
int32_t ml_dsa_freeze(int32_t a)
__contract__(
  requires(a <= REDUCE_DOMAIN_MAX)
  ensures(return_value >= 0)
  ensures(return_value < ML_DSA_Q)
);

/*************************************************
 * Name:        ml_dsa_fqmul
 *
 * Description: Multiplication followed by Montgomery reduction
 *              For finite field element a and b such that
 *              ML_DSA_Q*(-2**31) <= (a * b) <= ML_DSA_Q*(2**31),
 *              compute r congruent to (a*b)*2**(-32) (mod ML_DSA_Q)
 *              such that -ML_DSA_Q < r < ML_DSA_Q.
 *
 * Arguments:   - int32_t a: first factor
 *              - int32_t b: second factor
 *
 * Returns r.
 **************************************************/
int64_t ml_dsa_fqmul(int32_t a, int32_t b)
__contract__(
  requires(((int64_t) a * (int64_t)b) <= (2147483648LL * (int64_t) ML_DSA_Q))
  requires(((int64_t) a * (int64_t)b) >= (2147483648LL * (int64_t) -ML_DSA_Q))
  ensures(return_value > -ML_DSA_Q)
  ensures(return_value < ML_DSA_Q)
);

/*************************************************
 * Name:        poly_freeze
 *
 * Description: Freezes all elements of array p
 *              such that for all i
 *               0 <= p[i] < ML_DSA_Q
 *
 * This example illustrates the use of array_bound
 * macro for CBMC, and loop invariant contracts
 * in the body
 **************************************************/
#define N 256
void poly_freeze(int32_t p[N])
__contract__(
  requires(memory_no_alias(p, sizeof(int32_t) * N))

  /* To meet the precondition of ml_dsa_freeze() we need to know that */
  requires(array_bound(p, 0, N, 0, (REDUCE_DOMAIN_MAX + 1)))

  assigns(object_whole(p))

  /* use the array_bound() macro to express that all elements p are
   * frozen to 0 <= p[i] < ML_DSA_Q */
  ensures(array_bound(p, 0, N, 0, ML_DSA_Q))
);

#endif
