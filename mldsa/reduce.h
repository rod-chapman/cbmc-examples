#ifndef ML_DSA_REDUCE_H
#define ML_DSA_REDUCE_H

#include <stdbool.h>
#include <stdint.h>
#include "../common/cbmc.h"
#include "params.h"

/*************************************************
 * Name:        ml_dsa_reduce32
 *
 * Description: For finite field element a with a <= 2^{31} - 2^{22} - 1,
 *              compute r \equiv a (mod Q) such that -6283009 <= r <= 6283008.
 *
 * Arguments:   - int32_t: finite field element a
 *
 * Returns r.
 **************************************************/
#define REDUCE_DOMAIN_MAX 2143289343
#define REDUCE_RANGE_MAX 6283009
int32_t ml_dsa_reduce32(int32_t a)
__contract__(
  requires(a <= REDUCE_DOMAIN_MAX)
  ensures(return_value >= -REDUCE_RANGE_MAX)
  ensures(return_value < REDUCE_RANGE_MAX)
  // Extra credit for proof of:
  // ensures(return_value == a % ML_DSA_Q)
);

/*************************************************
 * Name:        ml_dsa_caddq
 *
 * Description: Add Q if input coefficient is negative.
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
 * Description: For finite field element a, compute standard
 *              representative r = a mod^+ Q such that
 *              r >= 0 && r < Q
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
 *              For finite field element a with -2^{31}Q <= a <= Q*2^31,
 *              compute r \equiv a*2^{-32} (mod Q) such that -Q < r < Q.
 *
 * Arguments:   - int32_t a: first factor
 *              - int32_t b: second factor
 *
 * Returns r.
 **************************************************/
int64_t ml_dsa_fqmul(int32_t a, int32_t b)
__contract__(
  requires(((int64_t) a * (int64_t)b) <= (2147483648UL * (int64_t) ML_DSA_Q))
  requires(((int64_t) a * (int64_t)b) >= (2147483648UL * (int64_t) -ML_DSA_Q))
  ensures(return_value > -ML_DSA_Q)
  ensures(return_value < ML_DSA_Q)
);

#define N 256
void poly_freeze(int32_t p[N])
__contract__(
  requires(memory_no_alias(p, sizeof(int32_t) * N))

  /* To meet the precondition of ml_dsa_freeze() we need to know that */
  requires(array_bound(p, 0, N, 0, (REDUCE_DOMAIN_MAX + 1)))

  assigns(object_whole(p))

  /* use the array_bound() macro to express that all elements p are frozen to 0 <= [[i] < Q */
  ensures(array_bound(p, 0, N, 0, ML_DSA_Q))
);

#endif
