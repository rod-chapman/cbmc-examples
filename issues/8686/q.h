#include <stdint.h>
#include "cbmc.h"
#include "p.h"

#define K 7

typedef struct
{
  mld_poly vec[K];
} mld_polyveck;

void mld_polyveck_caddq(mld_polyveck *v)
__contract__(
  requires(memory_no_alias(v, sizeof(mld_polyveck)))
  requires(forall(k0, 0, K,
    array_abs_bound(v->vec[k0].coeffs, 0, N, Q)))
  assigns(memory_slice(v, sizeof(mld_polyveck)))
  ensures(forall(k1, 0, K,
    array_bound(v->vec[k1].coeffs, 0, N, 0, Q)))
);
