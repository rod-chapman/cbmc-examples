/*
 * Copyright (c) 2025 The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "polyvec.h"
#include <stdint.h>
#include "poly.h"

void polyveck_decompose(polyveck *v1, polyveck *v0, const polyveck *v)
{
  unsigned int i;

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(v0, sizeof(polyveck)), memory_slice(v1, sizeof(polyveck)))
    invariant(i <= MLDSA_K)
    invariant(forall(k1, 0, i,
                     array_bound(v1->vec[k1].coeffs, 0, MLDSA_N, 0, (MLDSA_Q-1)/(2*MLDSA_GAMMA2)) &&
                     array_abs_bound(v0->vec[k1].coeffs, 0, MLDSA_N, MLDSA_GAMMA2+1)))
  )
  {
    poly_decompose(&v1->vec[i], &v0->vec[i], &v->vec[i]);
  }
}
