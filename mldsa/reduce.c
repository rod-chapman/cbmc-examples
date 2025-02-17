#include "reduce.h"
#include <stdint.h>
#include "params.h"

int32_t ml_dsa_reduce32(int32_t a)
{
  int32_t t;

  /* To compute (a % ML_DSA_Q), a compiler would normally
   * generate a % ML_DSA_Q == (a - (a / ML_DSA_Q) * ML_DSA_Q),
   * but this is both slow and involve a division that might not
   * be executed in constant time.
   *
   * To improve performace and constant-time, this code computes
   * an approximation of (a / ML_DSA_Q), dividing by 2**23 (with rounding to
   * nearest) where 2**23 = ML_DSA_Q + 2**13 - 1. This is "close enough" to
   * yield (a / ML_DSA_Q) +/- 1
   */

  /* Round-to-nearest division by 2**23 by adding 0.5*(2**23) first */
  t = (a + (1 << 22)) >> 23;

  /* Sanity check: prove that t is either exactly a / ML_DSA_Q or
   * is too big or too small by exactly 1 */
  cassert((t == (a / ML_DSA_Q)) || (t == (a / ML_DSA_Q) + 1) ||
          (t == (a / ML_DSA_Q) - 1));

  return (a - t * ML_DSA_Q);
}

int32_t ml_dsa_caddq(int32_t a)
{
  /* Generate a "mask" against which a bitwise-and of ML_DSA_Q may
   * be evaluated.
   *  Any negative     a -> mask == b1111111111 etc.
   *  Zero or positive a -> mask == b0000000000 etc.
   *
   * PORTABILITY WARNING: Right-shift of a negative signed integer is
   * implementation-defined in C (C99 6.5.7(5)), but this code depends
   * on the behaviour being a "sign preserving arithmetic" shift for
   * negative values. */
  const int32_t mask = a >> 31;

  /* If a is negative, then add ML_DSA_Q, otherwise add 0 */
  a += (mask & ML_DSA_Q);
  return a;
}


int32_t ml_dsa_freeze(int32_t a)
{
  a = ml_dsa_reduce32(a);

  /* Note that the post-condition of ml_dsa_reduce32() is suffifient
   * to ensure the pre-condition of ml_dsa_caddq() */
  a = ml_dsa_caddq(a);
  return a;
}

#define ML_DSA_QINV 58728449  // q^(-1) mod 2^32

int64_t ml_dsa_fqmul(int32_t a, int32_t b)
{
  int64_t s;
  int32_t t;

  /* This code exploits conversion from int64_t to int32_t,
   * and right-shift of a signed integer (that might be negative),
   * both of which are implementation-defined in C.
   * This code should be re-written to remove these non-portable
   * idioms, and then proven with CBMC */
  s = (int64_t)a * b;
  t = (int64_t)(int32_t)s * ML_DSA_QINV;
  t = (s - (int64_t)t * ML_DSA_Q) >> 32;
  return t;
}

void poly_freeze(int32_t p[N])
{
  unsigned i;
  for (i = 0; i < N; i++)
  __loop__(
    invariant(i <= N)
    /* Elements from 0 to < i are reduced */
    invariant(array_bound(p, 0, i, 0, ML_DSA_Q))
    /* Elements from i to < N have not been reduced (yet) */
    invariant(array_bound(p, i, N, 0, (REDUCE_DOMAIN_MAX + 1)))
  )
  {
    p[i] = ml_dsa_freeze(p[i]);
  }

  /* Substitute the loop exit condition (i == N) into the
   * invariant above to get our post-condition */
}
