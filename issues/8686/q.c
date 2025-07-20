#include "q.h"

void mld_polyveck_caddq(mld_polyveck *v)
{
  unsigned int i;

  for (i = 0; i < K; ++i)
  __loop__(
    assigns(i, memory_slice(v, sizeof(mld_polyveck)))
    invariant(i <= K)
    invariant(forall(k0, i, K, forall(k1, 0, N, v->vec[k0].coeffs[k1] == loop_entry(*v).vec[k0].coeffs[k1])))
    invariant(forall(k1, 0, i, array_bound(v->vec[k1].coeffs, 0, N, 0, Q))))
  {
    caddq(&v->vec[i]);
  }
}

void mld_polyveck_caddq_harness()
{
  mld_polyveck *v;
  mld_polyveck_caddq(v);
}
