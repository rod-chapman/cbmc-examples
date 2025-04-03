/*
 * Copyright (c) 2025 The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef POLY_H
#define POLY_H

#include <stdint.h>
#include "cbmc.h"

#define MLDSA_N 256
#define MLDSA_Q 8380417
#define MLDSA_K 4
#define MLDSA_L 4
#define MLDSA_GAMMA2 ((MLDSA_Q - 1) / 88)

typedef struct
{
  int32_t coeffs[MLDSA_N];
} poly;

void poly_decompose(poly *a1, poly *a0, const poly *a)
__contract__(
  requires(memory_no_alias(a1,  sizeof(poly)))
  requires(memory_no_alias(a0, sizeof(poly)))
  requires(memory_no_alias(a, sizeof(poly)))
  requires(array_bound(a->coeffs, 0, MLDSA_N, 0, MLDSA_Q))
  assigns(memory_slice(a1, sizeof(poly)))
  assigns(memory_slice(a0, sizeof(poly)))
  ensures(array_bound(a1->coeffs, 0, MLDSA_N, 0, (MLDSA_Q-1)/(2*MLDSA_GAMMA2)))
  ensures(array_abs_bound(a0->coeffs, 0, MLDSA_N, MLDSA_GAMMA2+1))
);

#endif
