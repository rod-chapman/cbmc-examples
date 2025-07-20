#include <stdint.h>
#include "cbmc.h"

#define N 256
#define Q 8380417

typedef struct
{
  int32_t coeffs[N];
} mld_poly;

void caddq(mld_poly *a)
__contract__(
  requires(memory_no_alias(a, sizeof(mld_poly)))
  requires(array_abs_bound(a->coeffs, 0, N, Q))
  assigns(memory_slice(a, sizeof(mld_poly)))
  ensures(array_bound(a->coeffs, 0, N, 0, Q))
);
