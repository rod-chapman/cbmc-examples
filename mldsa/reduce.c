#include "reduce.h"
#include <stdint.h>
#include "params.h"

int32_t ml_dsa_reduce32(int32_t a)
{
  int32_t t;

  t = (a + (1 << 22)) >> 23;
  t = a - t * ML_DSA_Q;
  return t;
}

int32_t ml_dsa_caddq(int32_t a)
{
  a += (a >> 31) & ML_DSA_Q;
  return a;
}


int32_t ml_dsa_freeze(int32_t a)
{
  a = ml_dsa_reduce32(a);
  a = ml_dsa_caddq(a);
  return a;
}

#define ML_DSA_QINV 58728449  // q^(-1) mod 2^32

int64_t ml_dsa_fqmul(int32_t a, int32_t b)
{
  int64_t s;
  int32_t t;

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
  )
  {
    p[i] = ml_dsa_freeze(p[i]);
  }
}
