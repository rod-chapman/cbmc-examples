/*
 * Copyright (c) 2025 The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef POLYVEC_H
#define POLYVEC_H

#include <stdint.h>
#include "cbmc.h"
#include "poly.h"

/* Vectors of polynomials of length MLDSA_K */
typedef struct
{
  poly vec[MLDSA_K];
} polyveck;

void polyveck_decompose(polyveck *v1, polyveck *v0, const polyveck *v)
__contract__(
  requires(memory_no_alias(v1,  sizeof(polyveck)))
  requires(memory_no_alias(v0, sizeof(polyveck)))
  requires(memory_no_alias(v, sizeof(polyveck)))
  requires(forall(k0, 0, MLDSA_K,
    array_bound(v->vec[k0].coeffs, 0, MLDSA_N, 0, MLDSA_Q)))
  assigns(object_whole(v1))
  assigns(object_whole(v0))
  ensures(forall(k1, 0, MLDSA_K,
                 array_bound(v1->vec[k1].coeffs, 0, MLDSA_N, 0, (MLDSA_Q-1)/(2*MLDSA_GAMMA2)) &&
                 array_abs_bound(v0->vec[k1].coeffs, 0, MLDSA_N, MLDSA_GAMMA2+1)))
);

#endif
